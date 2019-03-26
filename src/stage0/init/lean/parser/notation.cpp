// Lean compiler output
// Module: init.lean.parser.notation
// Imports: init.lean.parser.token
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
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27;
obj* l_Lean_Parser_command_notation_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_transition_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2(obj*);
obj* l___private_init_lean_parser_parsec_4__mkStringResult___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__2(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_kind_Parser___closed__1;
obj* l_Lean_Parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit;
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_binder;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_command_notation_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadRec;
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4;
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_command_NotationSpec_transition;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_notationLike_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6;
obj* l_Lean_Parser_command_reserveNotation_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView;
obj* l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasView;
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens;
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_command_reserveMixfix;
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens;
extern usize l_String_toSubstring___closed__1;
obj* l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1;
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_mixfix_HasView_x_27;
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7;
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27;
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_mixfix;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_notationLike_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView;
obj* l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_reserveMixfix_HasView;
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27;
obj* l_List_reverse___rarg(obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3(obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
extern obj* l_Lean_Parser_TermParserM_Alternative;
obj* l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_Lean_Parser_command_mixfix_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
obj* l_Lean_Parser_command_reserveNotation_Parser___closed__1;
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol;
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_number_HasView;
obj* l_Option_get___main___at_Lean_Parser_run___spec__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedence;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_Substring_toString(obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1(obj*);
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_mixfix_HasView;
obj* l_Lean_Parser_command_NotationSpec_HasView;
obj* l_Lean_Parser_command_reserveNotation_HasView;
obj* l_Lean_Parser_command_notationLike;
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27;
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_scopedAction;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_mixfix_kind;
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_Combinators_recurse_view___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_NotationSpec_action_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
obj* l___private_init_lean_parser_parsec_2__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote;
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_action;
obj* l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1(obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_notationLike_HasView;
obj* l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_number;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1(obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol;
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_Parser___closed__1;
obj* l_Lean_Parser_raw_view___rarg___lambda__1(obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_actionKind;
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_rule_HasView;
obj* l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens;
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
obj* l_Lean_Parser_Term_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_argument;
obj* l_Lean_Parser_command_notation;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView;
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27;
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(obj*);
obj* l_Lean_Parser_command_NotationSpec_Parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat(obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_token_3__updateTrailing___main(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__2(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_NotationSpec_rule_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_foldAction_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_notation_HasView;
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_mixfix_kind_HasView;
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_reserveMixfix_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_command_NotationSpec_action_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4(obj*);
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27;
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___boxed(obj*);
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_NotationSpec_binders;
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4;
obj* l_String_trim(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_transition_HasView;
extern obj* l_Lean_Parser_TermParserM_Monad;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_command_NotationSpec_binder_HasView;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
obj* l_Lean_Parser_command_NotationSpec_binders_HasView;
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_reserveMixfix_Parser___closed__1;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_command_notationLike_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1;
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_NotationSpec_foldAction;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2;
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
obj* l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasView;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
extern obj* l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser;
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView;
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_notation_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_mixfix_kind_Parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_TermParserM_MonadExcept;
obj* l_String_quote(obj*);
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_rule;
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_notation_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_View;
obj* l_Lean_Parser_command_reserveNotation;
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedence_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_NotationSpec;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*);
obj* l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView;
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_number_View_toNat___main(obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2;
extern obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27;
obj* l_Lean_Parser_command_NotationSpec_action_HasView;
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasTokens;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_5(x_1, x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("Term");
return x_0;
}
}
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasView(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___spec__1), 6, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_Lean_Parser_TermParserM_Lean_Parser_MonadRec;
x_4 = l_Lean_Parser_Combinators_recurse_view___rarg(x_0, x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_7 = l_Lean_Parser_TermParserM_Alternative;
x_8 = l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1;
x_9 = l_Lean_Parser_Combinators_label_view___rarg(x_6, x_7, x_2, x_8, x_4);
lean::dec(x_2);
return x_9;
}
}
obj* _init_l_Lean_Parser_Term_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("Term");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_Term_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::apply_5(x_1, x_0, x_2, x_3, x_4, x_5);
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
x_12 = l_Lean_Parser_Term_Parser___closed__1;
x_13 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_7, x_12);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_9);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceLit");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_number_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceLit");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
lean::dec(x_39);
if (x_56 == 0)
{
obj* x_58; 
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_52);
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_63; obj* x_64; 
x_59 = l_Lean_Parser_number_HasView;
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
lean::dec(x_59);
x_63 = lean::apply_1(x_60, x_52);
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
}
else
{
obj* x_68; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_68 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_68;
}
}
}
}
}
}
}
else
{
obj* x_71; 
lean::dec(x_8);
lean::dec(x_17);
x_71 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_number_HasView;
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
x_14 = l_Lean_Parser_command_NotationSpec_precedenceLit;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_1);
x_20 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_21 = l_Lean_Parser_Syntax_mkNode(x_20, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_Lean_Parser_command_NotationSpec_precedenceLit;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("number");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_Lean_Parser_token(x_0, x_2, x_3);
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
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_2);
x_26 = lean::box(0);
x_27 = l_String_splitAux___main___closed__1;
x_28 = l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1;
x_29 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_27, x_28, x_25, x_26, x_0, x_14, x_9);
lean::dec(x_14);
lean::dec(x_0);
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
x_42 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_41, x_28);
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
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_0);
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
x_53 = l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1;
x_54 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_52, x_53);
x_55 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_54);
if (lean::is_scalar(x_11)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_11;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_9);
return x_56;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_0);
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
x_70 = l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_69, x_70);
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
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_4);
lean::inc(x_2);
x_8 = l_Lean_Parser_token(x_2, x_4, x_5);
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
obj* x_23; obj* x_25; obj* x_28; 
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_21 = x_28;
goto lbl_22;
}
case 1:
{
obj* x_29; obj* x_31; obj* x_34; obj* x_36; 
x_29 = lean::cnstr_get(x_14, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_34 = l_Lean_Parser_Substring_toString(x_31);
lean::dec(x_31);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_34);
x_21 = x_36;
goto lbl_22;
}
default:
{
obj* x_37; 
x_37 = lean::box(0);
x_21 = x_37;
goto lbl_22;
}
}
lbl_22:
{
uint8 x_38; 
if (lean::obj_tag(x_21) == 0)
{
uint8 x_40; 
x_40 = 1;
x_38 = x_40;
goto lbl_39;
}
else
{
obj* x_41; uint8 x_44; 
x_41 = lean::cnstr_get(x_21, 0);
lean::inc(x_41);
lean::dec(x_21);
x_44 = lean::string_dec_eq(x_41, x_0);
lean::dec(x_41);
if (x_44 == 0)
{
uint8 x_46; 
x_46 = 1;
x_38 = x_46;
goto lbl_39;
}
else
{
uint8 x_47; 
x_47 = 0;
x_38 = x_47;
goto lbl_39;
}
}
lbl_39:
{
if (x_38 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_51 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_20)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_20;
}
lean::cnstr_set(x_52, 0, x_14);
lean::cnstr_set(x_52, 1, x_16);
lean::cnstr_set(x_52, 2, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_52);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_53);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
if (lean::is_scalar(x_13)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_13;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_11);
return x_57;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_69; 
lean::dec(x_13);
lean::dec(x_20);
x_60 = l_String_quote(x_0);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_4);
x_63 = lean::box(0);
x_64 = l_String_splitAux___main___closed__1;
x_65 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_64, x_61, x_62, x_63, x_2, x_16, x_11);
lean::dec(x_16);
lean::dec(x_2);
lean::dec(x_62);
x_69 = lean::cnstr_get(x_65, 0);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_71 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 x_73 = x_65;
} else {
 lean::inc(x_71);
 lean::dec(x_65);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_69, 1);
x_76 = lean::cnstr_get(x_69, 2);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_78 = x_69;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_69);
 x_78 = lean::box(0);
}
x_79 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_14);
lean::cnstr_set(x_80, 1, x_74);
lean::cnstr_set(x_80, 2, x_79);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_82);
x_84 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_83);
if (lean::is_scalar(x_73)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_73;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_71);
return x_85;
}
else
{
obj* x_87; obj* x_89; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_14);
x_87 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 x_89 = x_65;
} else {
 lean::inc(x_87);
 lean::dec(x_65);
 x_89 = lean::box(0);
}
x_90 = lean::cnstr_get(x_69, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_93 = x_69;
} else {
 lean::inc(x_90);
 lean::dec(x_69);
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
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_95);
x_97 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_97, x_96);
x_99 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_98);
if (lean::is_scalar(x_89)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_89;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_87);
return x_100;
}
}
}
}
}
else
{
obj* x_104; obj* x_106; obj* x_107; uint8 x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_104 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_106 = x_8;
} else {
 lean::inc(x_104);
 lean::dec(x_8);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_9, 0);
x_109 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_110 = x_9;
} else {
 lean::inc(x_107);
 lean::dec(x_9);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set_scalar(x_111, sizeof(void*)*1, x_109);
x_112 = x_111;
x_113 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_114 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_112);
x_115 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_114);
if (lean::is_scalar(x_106)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_106;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_104);
return x_116;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Option_getOrElse___main___rarg(x_2, x_7);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_0);
lean::cnstr_set(x_10, 2, x_1);
lean::cnstr_set(x_10, 3, x_3);
x_11 = 0;
x_12 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
x_13 = x_12;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 9, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_11;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_16 = lean::cnstr_get(x_0, 0);
x_18 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_20 = x_0;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_0);
 x_20 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_25 = lean::apply_5(x_16, x_2, x_3, x_4, x_5, x_6);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 lean::cnstr_set(x_25, 1, lean::box(0));
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = lean::mk_nat_obj(1ul);
x_32 = lean::nat_add(x_1, x_31);
if (lean::obj_tag(x_26) == 0)
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_33 = lean::cnstr_get(x_26, 0);
x_35 = lean::cnstr_get(x_26, 1);
x_37 = lean::cnstr_get(x_26, 2);
if (lean::is_exclusive(x_26)) {
 x_39 = x_26;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_26);
 x_39 = lean::box(0);
}
x_40 = lean::box(0);
x_41 = lean_name_mk_numeral(x_40, x_1);
x_42 = lean::box(0);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_33);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_Parser_Syntax_mkNode(x_41, x_43);
x_45 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_39;
}
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_35);
lean::cnstr_set(x_46, 2, x_45);
x_47 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_54; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_30;
}
lean::cnstr_set(x_54, 0, x_47);
lean::cnstr_set(x_54, 1, x_28);
return x_54;
}
else
{
uint8 x_55; 
x_55 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (x_55 == 0)
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_30);
x_57 = lean::cnstr_get(x_47, 0);
lean::inc(x_57);
lean::dec(x_47);
x_60 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
x_61 = lean::cnstr_get(x_60, 0);
x_63 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_65 = x_60;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
x_66 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_57, x_61);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
return x_67;
}
else
{
obj* x_74; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_30;
}
lean::cnstr_set(x_74, 0, x_47);
lean::cnstr_set(x_74, 1, x_28);
return x_74;
}
}
}
else
{
uint8 x_77; 
lean::dec(x_20);
lean::dec(x_1);
x_77 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_30);
x_79 = lean::cnstr_get(x_26, 0);
lean::inc(x_79);
lean::dec(x_26);
x_82 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
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
x_88 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_79, x_83);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
x_96 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_98 = x_26;
} else {
 lean::inc(x_96);
 lean::dec(x_26);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_77);
x_100 = x_99;
if (lean::is_scalar(x_30)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_30;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_28);
return x_101;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_8; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_0);
lean::dec(x_4);
x_8 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
return x_8;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 1, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
x_9 = l_Lean_Parser_TermParserM_Monad;
x_10 = l_Lean_Parser_TermParserM_MonadExcept;
x_11 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_TermParserM_Alternative;
x_13 = l_Lean_Parser_command_NotationSpec_precedenceLit;
x_14 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_6);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_19 = x_2;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_2);
 x_19 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_26 = lean::apply_5(x_15, x_3, x_4, x_5, x_6, x_7);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; 
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_20 = x_27;
x_21 = x_29;
goto lbl_22;
}
else
{
uint8 x_32; 
x_32 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_32 == 0)
{
obj* x_33; obj* x_36; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
lean::dec(x_26);
x_36 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_38 = x_27;
} else {
 lean::inc(x_36);
 lean::dec(x_27);
 x_38 = lean::box(0);
}
x_39 = 0;
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_39);
x_41 = x_40;
x_20 = x_41;
x_21 = x_33;
goto lbl_22;
}
else
{
obj* x_42; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; 
x_42 = lean::cnstr_get(x_26, 1);
lean::inc(x_42);
lean::dec(x_26);
x_45 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_47 = x_27;
} else {
 lean::inc(x_45);
 lean::dec(x_27);
 x_47 = lean::box(0);
}
x_48 = 1;
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_48);
x_50 = x_49;
x_20 = x_50;
x_21 = x_42;
goto lbl_22;
}
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_51 = lean::cnstr_get(x_26, 1);
lean::inc(x_51);
lean::dec(x_26);
x_54 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_56 = x_27;
} else {
 lean::inc(x_54);
 lean::dec(x_27);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 3);
lean::inc(x_57);
x_59 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_57);
lean::dec(x_57);
lean::inc(x_1);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_1);
x_63 = lean::cnstr_get(x_54, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_54, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_54, 2);
lean::inc(x_67);
lean::dec(x_54);
x_70 = l_List_reverse___rarg(x_62);
lean::inc(x_0);
x_72 = l_Lean_Parser_Syntax_mkNode(x_0, x_70);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_63);
lean::cnstr_set(x_74, 1, x_65);
lean::cnstr_set(x_74, 2, x_67);
lean::cnstr_set(x_74, 3, x_73);
if (x_32 == 0)
{
uint8 x_75; obj* x_76; obj* x_77; 
x_75 = 0;
if (lean::is_scalar(x_56)) {
 x_76 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_76 = x_56;
}
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_75);
x_77 = x_76;
x_20 = x_77;
x_21 = x_51;
goto lbl_22;
}
else
{
uint8 x_78; obj* x_79; obj* x_80; 
x_78 = 1;
if (lean::is_scalar(x_56)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_56;
}
lean::cnstr_set(x_79, 0, x_74);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_78);
x_80 = x_79;
x_20 = x_80;
x_21 = x_51;
goto lbl_22;
}
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_81 = lean::cnstr_get(x_20, 0);
x_83 = lean::cnstr_get(x_20, 1);
x_85 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_87 = x_20;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_20);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_19;
}
lean::cnstr_set(x_88, 0, x_81);
lean::cnstr_set(x_88, 1, x_1);
x_89 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_87)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_87;
}
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_83);
lean::cnstr_set(x_90, 2, x_89);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_91, 2);
lean::inc(x_96);
lean::dec(x_91);
x_99 = l_List_mfoldl___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__2(x_0, x_92, x_17, x_3, x_4, x_5, x_94, x_21);
x_100 = lean::cnstr_get(x_99, 0);
x_102 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_104 = x_99;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_99);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_96, x_100);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_102);
return x_106;
}
else
{
obj* x_112; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_112 = lean::cnstr_get(x_91, 0);
x_114 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (lean::is_exclusive(x_91)) {
 x_115 = x_91;
} else {
 lean::inc(x_112);
 lean::dec(x_91);
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
lean::cnstr_set(x_118, 1, x_21);
return x_118;
}
}
else
{
obj* x_126; uint8 x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_126 = lean::cnstr_get(x_20, 0);
x_128 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_129 = x_20;
} else {
 lean::inc(x_126);
 lean::dec(x_20);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set_scalar(x_130, sizeof(void*)*1, x_128);
x_131 = x_130;
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_21);
return x_132;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::box(0);
lean::inc(x_0);
x_9 = l_List_mfoldl___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__2(x_0, x_7, x_1, x_2, x_3, x_4, x_5, x_6);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
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
x_22 = l_List_reverse___rarg(x_15);
x_23 = l_Lean_Parser_Syntax_mkNode(x_0, x_22);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_21;
}
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_17);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_25);
if (lean::is_scalar(x_14)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_14;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_12);
return x_27;
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_0);
x_29 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_31 = x_9;
} else {
 lean::inc(x_29);
 lean::dec(x_9);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_10, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_35 = x_10;
} else {
 lean::inc(x_32);
 lean::dec(x_10);
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
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 1, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_precedenceLit;
x_6 = l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_number_View_toNat___main(x_1);
return x_4;
}
else
{
obj* x_6; 
lean::dec(x_0);
x_6 = l_Lean_Parser_maxPrec;
return x_6;
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceOffsetOp");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceOffsetOp");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
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
x_11 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
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
x_23 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
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
x_31 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
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
x_50 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
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
x_59 = lean::mk_nat_obj(0ul);
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
x_68 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1;
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_56);
lean::dec(x_26);
x_71 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_56, 0);
lean::inc(x_72);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_26;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
case 3:
{
obj* x_78; 
lean::dec(x_26);
x_78 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2;
return x_78;
}
default:
{
obj* x_81; 
lean::dec(x_56);
lean::dec(x_26);
x_81 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2;
return x_81;
}
}
}
}
else
{
obj* x_86; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_86 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
return x_86;
}
}
}
}
}
}
}
else
{
obj* x_89; 
lean::dec(x_8);
lean::dec(x_17);
x_89 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3;
return x_89;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
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
x_10 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
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
x_10 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1;
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
x_18 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2;
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
x_36 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffset() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceOffset");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_number_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::apply_1(x_8, x_5);
x_12 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_6);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_0);
return x_13;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2;
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
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; 
x_36 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_28);
if (lean::obj_tag(x_27) == 0)
{
obj* x_44; 
x_44 = lean::box(3);
x_41 = x_27;
x_42 = x_44;
goto lbl_43;
}
else
{
obj* x_45; obj* x_47; 
x_45 = lean::cnstr_get(x_27, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_27, 1);
lean::inc(x_47);
lean::dec(x_27);
x_41 = x_47;
x_42 = x_45;
goto lbl_43;
}
lbl_43:
{
obj* x_50; obj* x_51; obj* x_54; 
x_50 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_42);
if (lean::obj_tag(x_41) == 0)
{
if (lean::obj_tag(x_41) == 0)
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::box(0);
x_56 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
x_57 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_57, 0, x_18);
lean::cnstr_set(x_57, 1, x_40);
lean::cnstr_set(x_57, 2, x_54);
lean::cnstr_set(x_57, 3, x_56);
lean::cnstr_set(x_57, 4, x_55);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_41, 0);
lean::inc(x_58);
lean::dec(x_41);
switch (lean::obj_tag(x_58)) {
case 0:
{
obj* x_61; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_61);
x_65 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
x_66 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_66, 0, x_18);
lean::cnstr_set(x_66, 1, x_40);
lean::cnstr_set(x_66, 2, x_54);
lean::cnstr_set(x_66, 3, x_65);
lean::cnstr_set(x_66, 4, x_64);
return x_66;
}
case 3:
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = lean::box(0);
x_68 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
x_69 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_69, 0, x_18);
lean::cnstr_set(x_69, 1, x_40);
lean::cnstr_set(x_69, 2, x_54);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set(x_69, 4, x_67);
return x_69;
}
default:
{
obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_58);
x_71 = lean::box(0);
x_72 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1;
x_73 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_73, 0, x_18);
lean::cnstr_set(x_73, 1, x_40);
lean::cnstr_set(x_73, 2, x_54);
lean::cnstr_set(x_73, 3, x_72);
lean::cnstr_set(x_73, 4, x_71);
return x_73;
}
}
}
}
else
{
obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_83; 
x_74 = lean::cnstr_get(x_41, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_41, 1);
lean::inc(x_76);
lean::dec(x_41);
x_79 = l_Lean_Parser_number_HasView;
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
lean::dec(x_79);
x_83 = lean::apply_1(x_80, x_74);
if (lean::obj_tag(x_76) == 0)
{
obj* x_84; obj* x_85; 
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_85, 0, x_18);
lean::cnstr_set(x_85, 1, x_40);
lean::cnstr_set(x_85, 2, x_54);
lean::cnstr_set(x_85, 3, x_83);
lean::cnstr_set(x_85, 4, x_84);
return x_85;
}
else
{
obj* x_86; 
x_86 = lean::cnstr_get(x_76, 0);
lean::inc(x_86);
lean::dec(x_76);
switch (lean::obj_tag(x_86)) {
case 0:
{
obj* x_89; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_86, 0);
lean::inc(x_89);
lean::dec(x_86);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_93, 0, x_18);
lean::cnstr_set(x_93, 1, x_40);
lean::cnstr_set(x_93, 2, x_54);
lean::cnstr_set(x_93, 3, x_83);
lean::cnstr_set(x_93, 4, x_92);
return x_93;
}
case 3:
{
obj* x_94; obj* x_95; 
x_94 = lean::box(0);
x_95 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_95, 0, x_18);
lean::cnstr_set(x_95, 1, x_40);
lean::cnstr_set(x_95, 2, x_54);
lean::cnstr_set(x_95, 3, x_83);
lean::cnstr_set(x_95, 4, x_94);
return x_95;
}
default:
{
obj* x_97; obj* x_98; 
lean::dec(x_86);
x_97 = lean::box(0);
x_98 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_98, 0, x_18);
lean::cnstr_set(x_98, 1, x_40);
lean::cnstr_set(x_98, 2, x_54);
lean::cnstr_set(x_98, 3, x_83);
lean::cnstr_set(x_98, 4, x_97);
return x_98;
}
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_16 = lean::apply_1(x_13, x_3);
x_17 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_5);
x_22 = l_Lean_Parser_number_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_7);
x_27 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_21);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_16);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
x_34 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_35 = l_Lean_Parser_Syntax_mkNode(x_34, x_33);
return x_35;
}
else
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_36 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_38 = x_9;
} else {
 lean::inc(x_36);
 lean::dec(x_9);
 x_38 = lean::box(0);
}
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_36);
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::box(3);
x_42 = l_Option_getOrElse___main___rarg(x_40, x_41);
lean::dec(x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_27);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_26);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_21);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_16);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_47);
x_50 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_54 = x_1;
} else {
 lean::inc(x_52);
 lean::dec(x_1);
 x_54 = lean::box(0);
}
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_52);
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::box(3);
x_58 = l_Option_getOrElse___main___rarg(x_56, x_57);
lean::dec(x_56);
if (lean::obj_tag(x_9) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_60 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_26);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_21);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_16);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_58);
lean::cnstr_set(x_64, 1, x_63);
x_65 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_66 = l_Lean_Parser_Syntax_mkNode(x_65, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_67 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_69 = x_9;
} else {
 lean::inc(x_67);
 lean::dec(x_9);
 x_69 = lean::box(0);
}
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_67);
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_70);
x_72 = l_Option_getOrElse___main___rarg(x_71, x_57);
lean::dec(x_71);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_27);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_26);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_21);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_16);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_58);
lean::cnstr_set(x_78, 1, x_77);
x_79 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_80 = l_Lean_Parser_Syntax_mkNode(x_79, x_78);
return x_80;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceTerm");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedenceTerm");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
lean::dec(x_39);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_58 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_52);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_68; obj* x_69; 
x_64 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_68 = lean::apply_1(x_65, x_52);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_73 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_73;
}
}
}
}
}
}
}
else
{
obj* x_76; 
lean::dec(x_8);
lean::dec(x_17);
x_76 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1;
return x_76;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_command_NotationSpec_precedenceLit_HasView;
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
x_14 = l_Lean_Parser_command_NotationSpec_precedenceTerm;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_NotationSpec_precedenceTerm;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; 
lean::inc(x_6);
lean::inc(x_4);
x_10 = l_Lean_Parser_token(x_4, x_6, x_7);
x_11 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_0);
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_11, 0);
x_20 = lean::cnstr_get(x_11, 1);
x_22 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_24 = x_11;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_11);
 x_24 = lean::box(0);
}
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_27; obj* x_29; uint8 x_32; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = lean::string_dec_eq(x_0, x_29);
lean::dec(x_0);
if (x_32 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_42; 
lean::dec(x_15);
lean::dec(x_24);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_6);
x_37 = lean::box(0);
x_38 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_29, x_2, x_36, x_37, x_4, x_20, x_13);
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_36);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_44 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_42, 1);
x_49 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_51 = x_42;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_18);
lean::cnstr_set(x_53, 1, x_47);
lean::cnstr_set(x_53, 2, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_55);
x_57 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_56, x_17);
x_58 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_57);
if (lean::is_scalar(x_46)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_46;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_44);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_18);
x_61 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_63 = x_38;
} else {
 lean::inc(x_61);
 lean::dec(x_38);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_42, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_67 = x_42;
} else {
 lean::inc(x_64);
 lean::dec(x_42);
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
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_69);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_70);
x_73 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_72, x_17);
x_74 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_29);
x_80 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_24)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_24;
}
lean::cnstr_set(x_81, 0, x_18);
lean::cnstr_set(x_81, 1, x_20);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_81);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_82);
x_85 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_84, x_17);
x_86 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_85);
if (lean::is_scalar(x_15)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_15;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_13);
return x_87;
}
}
case 3:
{
obj* x_91; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
x_91 = lean::box(0);
x_25 = x_91;
goto lbl_26;
}
default:
{
obj* x_96; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
lean::dec(x_18);
x_96 = lean::box(0);
x_25 = x_96;
goto lbl_26;
}
}
lbl_26:
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_25);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_6);
x_99 = lean::box(0);
x_100 = l_String_splitAux___main___closed__1;
x_101 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_100, x_2, x_98, x_99, x_4, x_20, x_13);
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_101, 0);
x_107 = lean::cnstr_get(x_101, 1);
if (lean::is_exclusive(x_101)) {
 x_109 = x_101;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_101);
 x_109 = lean::box(0);
}
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_105);
x_111 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_112 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_111, x_110);
x_113 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_112, x_17);
x_114 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_113);
if (lean::is_scalar(x_109)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_109;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_107);
return x_115;
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_120 = lean::cnstr_get(x_11, 0);
x_122 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_123 = x_11;
} else {
 lean::inc(x_120);
 lean::dec(x_11);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_122);
x_125 = x_124;
x_126 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_126, x_125);
x_128 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_127, x_17);
x_129 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_128);
if (lean::is_scalar(x_15)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_15;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_13);
return x_130;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; 
x_0 = lean::mk_string("(");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string(" + ");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::mk_string(" - ");
x_8 = l_Lean_Parser_symbol_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_10);
lean::dec(x_8);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_11);
lean::dec(x_11);
lean::dec(x_5);
x_16 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
x_18 = l_Lean_Parser_List_cons_tokens___rarg(x_16, x_10);
lean::dec(x_16);
x_20 = l_Lean_Parser_tokens___rarg(x_18);
lean::dec(x_18);
x_22 = lean::mk_string(")");
x_23 = l_Lean_Parser_symbol_tokens___rarg(x_22, x_1);
lean::dec(x_22);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_23, x_10);
lean::dec(x_23);
x_27 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_25);
lean::dec(x_25);
x_29 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_27);
lean::dec(x_27);
lean::dec(x_20);
x_32 = l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens;
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_32, x_29);
lean::dec(x_29);
x_35 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_33);
lean::dec(x_33);
lean::dec(x_2);
x_38 = l_Lean_Parser_tokens___rarg(x_35);
lean::dec(x_35);
x_40 = l_Lean_Parser_List_cons_tokens___rarg(x_38, x_10);
lean::dec(x_38);
x_42 = l_Lean_Parser_List_cons_tokens___rarg(x_32, x_40);
lean::dec(x_40);
x_44 = l_Lean_Parser_tokens___rarg(x_42);
lean::dec(x_42);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_44, x_10);
lean::dec(x_44);
x_48 = l_Lean_Parser_tokens___rarg(x_46);
lean::dec(x_46);
return x_48;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_5);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string(" + ");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::mk_string(" - ");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_5);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_5);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
x_24 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_23);
x_26 = lean::mk_string(")");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_30, 0, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_5);
lean::closure_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_19);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 1, 0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_25);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceLit_Parser), 5, 0);
lean::inc(x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_35);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_6);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_19);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_36);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_44, 0, x_43);
lean::closure_set(x_44, 1, x_5);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_19);
x_46 = l_Lean_Parser_TermParserM_Monad;
x_47 = l_Lean_Parser_TermParserM_MonadExcept;
x_48 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_49 = l_Lean_Parser_TermParserM_Alternative;
x_50 = l_Lean_Parser_command_NotationSpec_precedenceTerm;
x_51 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_52 = l_Lean_Parser_Combinators_node_view___rarg(x_46, x_47, x_48, x_49, x_50, x_45, x_51);
lean::dec(x_45);
return x_52;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string(" + ");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::mk_string(" - ");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_5);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_5);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
x_24 = l_Lean_Parser_command_NotationSpec_precedenceOffsetOp;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_23);
x_26 = lean::mk_string(")");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_30, 0, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_5);
lean::closure_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_19);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 1, 0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_25);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceLit_Parser), 5, 0);
lean::inc(x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_35);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_6);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_command_NotationSpec_precedenceOffset;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_19);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_36);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_44, 0, x_43);
lean::closure_set(x_44, 1, x_5);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_19);
return x_45;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_precedenceTerm;
x_6 = l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(x_1);
return x_4;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
x_13 = l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(x_11);
x_14 = lean::cnstr_get(x_5, 3);
lean::inc(x_14);
lean::dec(x_5);
x_17 = l_Lean_Parser_number_View_toNat___main(x_14);
x_18 = lean::nat_add(x_13, x_17);
lean::dec(x_17);
lean::dec(x_13);
return x_18;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_28; obj* x_29; 
lean::dec(x_8);
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
x_24 = l_Lean_Parser_command_NotationSpec_precedenceLit_View_toNat___main(x_22);
x_25 = lean::cnstr_get(x_5, 3);
lean::inc(x_25);
lean::dec(x_5);
x_28 = l_Lean_Parser_number_View_toNat___main(x_25);
x_29 = lean::nat_sub(x_24, x_28);
lean::dec(x_28);
lean::dec(x_24);
return x_29;
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("precedence");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_22; obj* x_23; 
x_22 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
x_27 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
lean::dec(x_27);
x_31 = lean::apply_1(x_28, x_24);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_21);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
case 3:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_33; 
x_33 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2;
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
lean::dec(x_1);
x_37 = lean::box(0);
x_38 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_34);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_37);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_45; 
x_45 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2;
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_54; obj* x_55; 
x_46 = lean::cnstr_get(x_1, 0);
lean::inc(x_46);
lean::dec(x_1);
x_49 = lean::box(0);
x_50 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_46);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_49);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_3);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
if (lean::obj_tag(x_1) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_Lean_Parser_command_NotationSpec_precedence;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_19 = x_1;
} else {
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::box(3);
x_23 = l_Option_getOrElse___main___rarg(x_21, x_22);
lean::dec(x_21);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_12);
x_26 = l_Lean_Parser_command_NotationSpec_precedence;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::mk_string(":");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_4);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_10 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string(":");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser), 5, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_TermParserM_Monad;
x_12 = l_Lean_Parser_TermParserM_MonadExcept;
x_13 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_14 = l_Lean_Parser_TermParserM_Alternative;
x_15 = l_Lean_Parser_command_NotationSpec_precedence;
x_16 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_17 = l_Lean_Parser_Combinators_node_view___rarg(x_11, x_12, x_13, x_14, x_15, x_10, x_16);
lean::dec(x_10);
return x_17;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string(":");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser), 5, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_precedence_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_precedence;
x_6 = l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
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
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = 96;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = lean::string_push(x_1, x_8);
x_15 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_0);
x_18 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__2(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
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
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = 96;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = lean::string_push(x_1, x_8);
x_15 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_0);
x_18 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__2(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_2 = l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___boxed), 3, 0);
x_4 = 0;
x_5 = l_Lean_Parser_raw_view___rarg(x_0, x_1, x_2, lean::box(0), x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
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
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = 96;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = lean::string_push(x_1, x_8);
x_15 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_0);
x_18 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__2(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_3);
x_6 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___rarg(x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_18 = l_Lean_Parser_mkRawRes(x_3, x_12);
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
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_11;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_9);
return x_24;
}
else
{
obj* x_26; obj* x_28; obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_3);
x_26 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_28 = x_6;
} else {
 lean::inc(x_26);
 lean::dec(x_6);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_7, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_32 = x_7;
} else {
 lean::inc(x_29);
 lean::dec(x_7);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_34);
if (lean::is_scalar(x_28)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_28;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_26);
return x_37;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("symbolQuote");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_0);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_0);
lean::cnstr_set(x_12, 2, x_0);
lean::cnstr_set(x_12, 3, x_0);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_15);
if (lean::is_scalar(x_7)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_7;
}
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_0);
lean::cnstr_set(x_24, 2, x_0);
lean::cnstr_set(x_24, 3, x_23);
return x_24;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_13);
x_28 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_0);
lean::cnstr_set(x_29, 2, x_0);
lean::cnstr_set(x_29, 3, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2;
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
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
switch (lean::obj_tag(x_28)) {
case 0:
{
obj* x_38; obj* x_41; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
x_36 = x_41;
goto lbl_37;
}
case 3:
{
obj* x_42; 
x_42 = lean::box(0);
x_36 = x_42;
goto lbl_37;
}
default:
{
obj* x_44; 
lean::dec(x_28);
x_44 = lean::box(0);
x_36 = x_44;
goto lbl_37;
}
}
lbl_37:
{
obj* x_45; obj* x_47; obj* x_48; 
if (lean::obj_tag(x_27) == 0)
{
obj* x_50; 
x_50 = lean::box(0);
if (lean::obj_tag(x_27) == 0)
{
x_45 = x_50;
goto lbl_46;
}
else
{
obj* x_51; 
x_51 = lean::cnstr_get(x_27, 0);
lean::inc(x_51);
lean::dec(x_27);
x_47 = x_50;
x_48 = x_51;
goto lbl_49;
}
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_27, 0);
lean::inc(x_54);
switch (lean::obj_tag(x_54)) {
case 0:
{
obj* x_56; obj* x_59; obj* x_62; 
x_56 = lean::cnstr_get(x_27, 1);
lean::inc(x_56);
lean::dec(x_27);
x_59 = lean::cnstr_get(x_54, 0);
lean::inc(x_59);
lean::dec(x_54);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_59);
if (lean::obj_tag(x_56) == 0)
{
x_45 = x_62;
goto lbl_46;
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
lean::dec(x_56);
x_47 = x_62;
x_48 = x_63;
goto lbl_49;
}
}
case 3:
{
obj* x_66; obj* x_69; 
x_66 = lean::cnstr_get(x_27, 1);
lean::inc(x_66);
lean::dec(x_27);
x_69 = lean::box(0);
if (lean::obj_tag(x_66) == 0)
{
x_45 = x_69;
goto lbl_46;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_66, 0);
lean::inc(x_70);
lean::dec(x_66);
x_47 = x_69;
x_48 = x_70;
goto lbl_49;
}
}
default:
{
obj* x_74; obj* x_77; 
lean::dec(x_54);
x_74 = lean::cnstr_get(x_27, 1);
lean::inc(x_74);
lean::dec(x_27);
x_77 = lean::box(0);
if (lean::obj_tag(x_74) == 0)
{
x_45 = x_77;
goto lbl_46;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_74, 0);
lean::inc(x_78);
lean::dec(x_74);
x_47 = x_77;
x_48 = x_78;
goto lbl_49;
}
}
}
}
lbl_46:
{
obj* x_81; obj* x_82; 
x_81 = lean::box(3);
x_82 = l_Lean_Parser_Syntax_asNode___main(x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_84; 
x_83 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_84, 0, x_18);
lean::cnstr_set(x_84, 1, x_36);
lean::cnstr_set(x_84, 2, x_45);
lean::cnstr_set(x_84, 3, x_83);
return x_84;
}
else
{
obj* x_85; obj* x_87; obj* x_88; 
x_85 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_87 = x_82;
} else {
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
if (lean::obj_tag(x_88) == 0)
{
obj* x_92; obj* x_93; 
lean::dec(x_87);
x_92 = lean::box(0);
x_93 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_93, 0, x_18);
lean::cnstr_set(x_93, 1, x_36);
lean::cnstr_set(x_93, 2, x_45);
lean::cnstr_set(x_93, 3, x_92);
return x_93;
}
else
{
obj* x_94; 
x_94 = lean::cnstr_get(x_88, 1);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_96; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
x_96 = lean::cnstr_get(x_88, 0);
lean::inc(x_96);
lean::dec(x_88);
x_99 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
lean::dec(x_99);
x_103 = lean::apply_1(x_100, x_96);
if (lean::is_scalar(x_87)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_87;
}
lean::cnstr_set(x_104, 0, x_103);
x_105 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_105, 0, x_18);
lean::cnstr_set(x_105, 1, x_36);
lean::cnstr_set(x_105, 2, x_45);
lean::cnstr_set(x_105, 3, x_104);
return x_105;
}
else
{
obj* x_109; obj* x_110; 
lean::dec(x_88);
lean::dec(x_94);
lean::dec(x_87);
x_109 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_110 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_110, 0, x_18);
lean::cnstr_set(x_110, 1, x_36);
lean::cnstr_set(x_110, 2, x_45);
lean::cnstr_set(x_110, 3, x_109);
return x_110;
}
}
}
}
lbl_49:
{
obj* x_111; 
x_111 = l_Lean_Parser_Syntax_asNode___main(x_48);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; obj* x_113; 
x_112 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_113 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_113, 0, x_18);
lean::cnstr_set(x_113, 1, x_36);
lean::cnstr_set(x_113, 2, x_47);
lean::cnstr_set(x_113, 3, x_112);
return x_113;
}
else
{
obj* x_114; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_set(x_111, 0, lean::box(0));
 x_116 = x_111;
} else {
 lean::inc(x_114);
 lean::dec(x_111);
 x_116 = lean::box(0);
}
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_122; 
lean::dec(x_116);
x_121 = lean::box(0);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_18);
lean::cnstr_set(x_122, 1, x_36);
lean::cnstr_set(x_122, 2, x_47);
lean::cnstr_set(x_122, 3, x_121);
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_117, 1);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_128; obj* x_129; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_117, 0);
lean::inc(x_125);
lean::dec(x_117);
x_128 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
lean::dec(x_128);
x_132 = lean::apply_1(x_129, x_125);
if (lean::is_scalar(x_116)) {
 x_133 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_133 = x_116;
}
lean::cnstr_set(x_133, 0, x_132);
x_134 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_134, 0, x_18);
lean::cnstr_set(x_134, 1, x_36);
lean::cnstr_set(x_134, 2, x_47);
lean::cnstr_set(x_134, 3, x_133);
return x_134;
}
else
{
obj* x_138; obj* x_139; 
lean::dec(x_123);
lean::dec(x_116);
lean::dec(x_117);
x_138 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_139 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_139, 0, x_18);
lean::cnstr_set(x_139, 1, x_36);
lean::cnstr_set(x_139, 2, x_47);
lean::cnstr_set(x_139, 3, x_138);
return x_139;
}
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
x_4 = l_Lean_Parser_noKind;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::inc(x_3);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
x_4 = l_Lean_Parser_noKind;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_13; 
x_13 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_11 = x_13;
goto lbl_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::box(3);
x_20 = l_Option_getOrElse___main___rarg(x_18, x_19);
lean::dec(x_18);
x_11 = x_20;
goto lbl_12;
}
lbl_12:
{
obj* x_22; obj* x_23; 
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
lean::dec(x_7);
x_32 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::apply_1(x_33, x_29);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_10);
x_38 = l_Lean_Parser_noKind;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_10);
x_41 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_11);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
return x_46;
}
}
else
{
obj* x_47; obj* x_50; 
x_47 = lean::cnstr_get(x_5, 0);
lean::inc(x_47);
lean::dec(x_5);
x_50 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_22 = x_50;
x_23 = x_47;
goto lbl_24;
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_51 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_53 = x_3;
} else {
 lean::inc(x_51);
 lean::dec(x_3);
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
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2;
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_11);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_63 = l_Lean_Parser_Syntax_mkNode(x_62, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_64 = lean::cnstr_get(x_7, 0);
lean::inc(x_64);
lean::dec(x_7);
x_67 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
lean::dec(x_67);
x_71 = lean::apply_1(x_68, x_64);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_10);
x_73 = l_Lean_Parser_noKind;
x_74 = l_Lean_Parser_Syntax_mkNode(x_73, x_72);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_10);
x_76 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_57);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_11);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_81 = l_Lean_Parser_Syntax_mkNode(x_80, x_79);
return x_81;
}
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_5, 0);
lean::inc(x_82);
lean::dec(x_5);
x_22 = x_57;
x_23 = x_82;
goto lbl_24;
}
}
lbl_24:
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_23);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
x_87 = lean::box(3);
x_88 = l_Option_getOrElse___main___rarg(x_86, x_87);
lean::dec(x_86);
if (lean::obj_tag(x_7) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_90 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_22);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_11);
lean::cnstr_set(x_93, 1, x_92);
x_94 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_95 = l_Lean_Parser_Syntax_mkNode(x_94, x_93);
return x_95;
}
else
{
obj* x_96; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_96 = lean::cnstr_get(x_7, 0);
lean::inc(x_96);
lean::dec(x_7);
x_99 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
lean::dec(x_99);
x_103 = lean::apply_1(x_100, x_96);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_10);
x_105 = l_Lean_Parser_noKind;
x_106 = l_Lean_Parser_Syntax_mkNode(x_105, x_104);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_10);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_88);
lean::cnstr_set(x_108, 1, x_107);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_22);
lean::cnstr_set(x_109, 1, x_108);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_11);
lean::cnstr_set(x_110, 1, x_109);
x_111 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_112 = l_Lean_Parser_Syntax_mkNode(x_111, x_110);
return x_112;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27;
return x_0;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_2(x_0, x_2, x_3);
return x_4;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_String_isEmpty(x_0);
if (x_7 == 0)
{
obj* x_8; obj* x_9; usize x_10; obj* x_12; obj* x_13; obj* x_15; 
x_8 = lean::string_length(x_0);
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_String_toSubstring___closed__1;
lean::inc(x_0);
x_12 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_10);
x_13 = x_12;
lean::inc(x_5);
x_15 = l___private_init_lean_parser_parsec_2__strAux___main(x_8, x_13, x_5);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = l_String_splitAux___main___closed__1;
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_19, 2, x_1);
lean::cnstr_set(x_19, 3, x_17);
x_20 = 0;
x_21 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*1, x_20);
x_22 = x_21;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_5);
lean::dec(x_1);
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
lean::dec(x_15);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_26);
lean::cnstr_set(x_30, 2, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_6);
return x_31;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
x_34 = l_String_splitAux___main___closed__1;
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_5);
lean::cnstr_set(x_36, 2, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_6);
return x_37;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_10; obj* x_11; 
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_10 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::apply_6(x_1, x_16, x_2, x_3, x_4, x_18, x_13);
x_24 = lean::cnstr_get(x_23, 0);
x_26 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 x_28 = x_23;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_24);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_26);
return x_30;
}
else
{
obj* x_35; obj* x_37; obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_37 = x_10;
} else {
 lean::inc(x_35);
 lean::dec(x_10);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_11, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_41 = x_11;
} else {
 lean::inc(x_38);
 lean::dec(x_11);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_37;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_4);
x_7 = l_Lean_Parser_whitespace(x_2, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_4);
lean::cnstr_set(x_19, 1, x_13);
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
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_22);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
x_29 = lean::cnstr_get(x_24, 2);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_24);
 x_31 = lean::box(0);
}
x_32 = l___private_init_lean_parser_token_3__updateTrailing___main(x_25, x_0);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_27);
lean::cnstr_set(x_33, 2, x_23);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_33);
if (lean::is_scalar(x_12)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_12;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_10);
return x_35;
}
else
{
obj* x_37; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_0);
x_37 = lean::cnstr_get(x_24, 0);
x_39 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_exclusive(x_24)) {
 x_40 = x_24;
} else {
 lean::inc(x_37);
 lean::dec(x_24);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = x_41;
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
obj* x_45; obj* x_47; obj* x_48; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_4);
x_45 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_47 = x_7;
} else {
 lean::inc(x_45);
 lean::dec(x_7);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_8, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_51 = x_8;
} else {
 lean::inc(x_48);
 lean::dec(x_8);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_48);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_50);
x_53 = x_52;
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_53);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_55, 0);
x_58 = lean::cnstr_get(x_55, 1);
x_60 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 x_62 = x_55;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_55);
 x_62 = lean::box(0);
}
x_63 = l___private_init_lean_parser_token_3__updateTrailing___main(x_56, x_0);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_54);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_64);
if (lean::is_scalar(x_47)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_47;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_45);
return x_66;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_0);
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
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_45);
return x_74;
}
}
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
if (x_1 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_10 = lean::box(0);
lean::inc(x_5);
x_15 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
x_25 = lean::cnstr_get(x_16, 2);
if (lean::is_exclusive(x_16)) {
 x_27 = x_16;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_21);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_27)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_27;
}
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_23);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_30);
x_11 = x_31;
x_12 = x_18;
goto lbl_13;
}
else
{
obj* x_32; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_15, 1);
lean::inc(x_32);
lean::dec(x_15);
x_35 = lean::cnstr_get(x_16, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 x_38 = x_16;
} else {
 lean::inc(x_35);
 lean::dec(x_16);
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
x_11 = x_40;
x_12 = x_32;
goto lbl_13;
}
}
else
{
obj* x_41; obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_41 = lean::cnstr_get(x_15, 1);
lean::inc(x_41);
lean::dec(x_15);
x_44 = lean::cnstr_get(x_16, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_47 = x_16;
} else {
 lean::inc(x_44);
 lean::dec(x_16);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_44, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_44, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_44, 3);
lean::inc(x_54);
lean::dec(x_44);
x_57 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_54);
lean::dec(x_54);
x_59 = lean::box(0);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
x_61 = l_Lean_Parser_noKind;
x_62 = l_Lean_Parser_Syntax_mkNode(x_61, x_60);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_48);
lean::cnstr_set(x_64, 1, x_50);
lean::cnstr_set(x_64, 2, x_52);
lean::cnstr_set(x_64, 3, x_63);
if (x_46 == 0)
{
uint8 x_65; obj* x_66; obj* x_67; 
x_65 = 0;
if (lean::is_scalar(x_47)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_47;
}
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_65);
x_67 = x_66;
x_11 = x_67;
x_12 = x_41;
goto lbl_13;
}
else
{
uint8 x_68; obj* x_69; obj* x_70; 
x_68 = 1;
if (lean::is_scalar(x_47)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_47;
}
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_68);
x_70 = x_69;
x_11 = x_70;
x_12 = x_41;
goto lbl_13;
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_5);
x_7 = x_11;
x_8 = x_12;
goto lbl_9;
}
else
{
uint8 x_72; 
x_72 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (x_72 == 0)
{
obj* x_73; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_11, 0);
lean::inc(x_73);
lean::dec(x_11);
x_76 = lean::cnstr_get(x_73, 2);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_mjoin___rarg___closed__1;
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_80, 0, x_76);
lean::closure_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_10);
lean::cnstr_set(x_82, 1, x_5);
lean::cnstr_set(x_82, 2, x_81);
x_7 = x_82;
x_8 = x_12;
goto lbl_9;
}
else
{
lean::dec(x_5);
x_7 = x_11;
x_8 = x_12;
goto lbl_9;
}
}
}
}
else
{
obj* x_84; 
x_84 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_84;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_85; 
x_85 = lean::cnstr_get(x_7, 0);
lean::inc(x_85);
if (lean::obj_tag(x_85) == 0)
{
obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_87 = lean::cnstr_get(x_7, 1);
x_89 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_91 = x_7;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_7);
 x_91 = lean::box(0);
}
x_92 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_93 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_91)) {
 x_94 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_94 = x_91;
}
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_87);
lean::cnstr_set(x_94, 2, x_93);
x_95 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_89, x_94);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_8);
return x_96;
}
else
{
obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_97 = lean::cnstr_get(x_7, 1);
x_99 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_101 = x_7;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_7);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_85, 0);
lean::inc(x_102);
lean::dec(x_85);
x_105 = lean::box(0);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set(x_106, 1, x_105);
x_107 = l_Lean_Parser_noKind;
x_108 = l_Lean_Parser_Syntax_mkNode(x_107, x_106);
x_109 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_101)) {
 x_110 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_110 = x_101;
}
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set(x_110, 1, x_97);
lean::cnstr_set(x_110, 2, x_109);
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_110);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_8);
return x_112;
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_113 = lean::cnstr_get(x_7, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_116 = x_7;
} else {
 lean::inc(x_113);
 lean::dec(x_7);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_8);
return x_119;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_0);
lean::dec(x_2);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_3);
lean::dec(x_3);
x_7 = l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_5);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_8);
lean::dec(x_8);
x_12 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
return x_12;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
x_8 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7(x_0, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("`");
return x_0;
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1;
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4(x_7, x_0, x_2, x_3, x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
lean::inc(x_14);
x_20 = l_Lean_Parser_mkRawRes(x_1, x_14);
x_21 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_18)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_18;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_14);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
if (lean::is_scalar(x_13)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_13;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_11);
return x_24;
}
else
{
obj* x_26; obj* x_28; obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_28 = x_8;
} else {
 lean::inc(x_26);
 lean::dec(x_8);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_9, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_32 = x_9;
} else {
 lean::inc(x_29);
 lean::dec(x_9);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_28)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_28;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
return x_35;
}
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1;
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__4(x_7, x_0, x_2, x_3, x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
lean::dec(x_9);
lean::inc(x_14);
x_20 = l_Lean_Parser_mkRawRes(x_1, x_14);
x_21 = l_Lean_Parser_withTrailing___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__6(x_20, x_2, x_3, x_4, x_14, x_11);
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
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_22);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_28);
if (lean::is_scalar(x_26)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_26;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_24);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
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
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_0 = lean::mk_string("`");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg___boxed), 6, 1);
lean::closure_set(x_6, 0, x_5);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___boxed), 7, 1);
lean::closure_set(x_8, 0, x_2);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg), 7, 2);
lean::closure_set(x_10, 0, x_6);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2___boxed), 7, 1);
lean::closure_set(x_11, 0, x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg), 7, 2);
lean::closure_set(x_12, 0, x_6);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_14 = 0;
x_15 = lean::box(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___boxed), 5, 0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_TermParserM_Monad;
x_24 = l_Lean_Parser_TermParserM_MonadExcept;
x_25 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_26 = l_Lean_Parser_TermParserM_Alternative;
x_27 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_28 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
x_29 = l_Lean_Parser_Combinators_node_view___rarg(x_23, x_24, x_25, x_26, x_27, x_22, x_28);
lean::dec(x_22);
return x_29;
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_0 = lean::mk_string("`");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__3___rarg___boxed), 6, 1);
lean::closure_set(x_6, 0, x_5);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___boxed), 7, 1);
lean::closure_set(x_8, 0, x_2);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg), 7, 2);
lean::closure_set(x_10, 0, x_6);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__2___boxed), 7, 1);
lean::closure_set(x_11, 0, x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__5___rarg), 7, 2);
lean::closure_set(x_12, 0, x_6);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_14 = 0;
x_15 = lean::box(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser___boxed), 5, 0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
obj* l_Lean_Parser_command_NotationSpec_symbolQuote_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_symbolQuote;
x_6 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("symbol");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_1);
x_7 = l_Lean_Parser_token(x_1, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
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
switch (lean::obj_tag(x_13)) {
case 0:
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_1);
lean::dec(x_3);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_19;
}
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_15);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_25);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_26);
x_28 = l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1;
x_29 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_27, x_28);
x_30 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_29);
if (lean::is_scalar(x_12)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_12;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_10);
return x_31;
}
case 3:
{
obj* x_34; 
lean::dec(x_12);
lean::dec(x_19);
x_34 = lean::box(0);
x_20 = x_34;
goto lbl_21;
}
default:
{
obj* x_38; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_19);
x_38 = lean::box(0);
x_20 = x_38;
goto lbl_21;
}
}
lbl_21:
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_20);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_3);
x_41 = lean::box(0);
x_42 = l_String_splitAux___main___closed__1;
x_43 = l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1;
x_44 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_42, x_43, x_40, x_41, x_0, x_1, x_2, x_15, x_10);
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_44, 0);
x_50 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_52 = x_44;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_44);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_48);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_53);
x_56 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_55, x_43);
x_57 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_56);
if (lean::is_scalar(x_52)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_52;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_50);
return x_58;
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_1);
lean::dec(x_3);
x_61 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_63 = x_7;
} else {
 lean::inc(x_61);
 lean::dec(x_7);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_8, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_67 = x_8;
} else {
 lean::inc(x_64);
 lean::dec(x_8);
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
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_69);
x_72 = l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1;
x_73 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_71, x_72);
x_74 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
}
}
obj* l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_View() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("notationSymbol");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("notationSymbol");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_40; uint8 x_41; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
lean::dec(x_27);
x_40 = lean::box(0);
x_41 = lean_name_dec_eq(x_37, x_40);
lean::dec(x_37);
if (x_41 == 0)
{
obj* x_44; 
lean::dec(x_34);
x_44 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_44;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_45; 
x_45 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_34, 1);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_48; obj* x_51; obj* x_52; obj* x_55; 
x_48 = lean::cnstr_get(x_34, 0);
lean::inc(x_48);
lean::dec(x_34);
x_51 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
lean::dec(x_51);
x_55 = lean::apply_1(x_52, x_48);
return x_55;
}
else
{
obj* x_58; 
lean::dec(x_46);
lean::dec(x_34);
x_58 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_58;
}
}
}
}
}
}
}
else
{
obj* x_61; 
lean::dec(x_8);
lean::dec(x_17);
x_61 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1;
return x_61;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_1);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_command_NotationSpec_notationSymbol;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_0);
x_3 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_0);
lean::dec(x_3);
x_7 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_TermParserM_Monad;
x_7 = l_Lean_Parser_TermParserM_MonadExcept;
x_8 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_9 = l_Lean_Parser_TermParserM_Alternative;
x_10 = l_Lean_Parser_command_NotationSpec_notationSymbol;
x_11 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_12 = l_Lean_Parser_Combinators_node_view___rarg(x_6, x_7, x_8, x_9, x_10, x_5, x_11);
lean::dec(x_5);
return x_12;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
}
}
obj* l_Lean_Parser_command_NotationSpec_notationSymbol_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_notationSymbol;
x_6 = l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("mixfixSymbol");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("mixfixSymbol");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_11 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_23 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_31 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_50 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_59 = lean::mk_nat_obj(0ul);
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
x_68 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1;
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_56);
lean::dec(x_26);
x_71 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_77; obj* x_78; 
lean::dec(x_26);
x_73 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
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
x_83 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
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
x_86 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2;
return x_86;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
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
x_10 = l_Lean_Parser_command_NotationSpec_mixfixSymbol;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView;
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
x_14 = l_Lean_Parser_command_NotationSpec_mixfixSymbol;
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
x_19 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1;
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
x_32 = l_Lean_Parser_command_NotationSpec_mixfixSymbol;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens;
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_0);
x_3 = l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_2);
lean::dec(x_2);
x_6 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_0);
lean::dec(x_6);
x_10 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_TermParserM_Monad;
x_9 = l_Lean_Parser_TermParserM_MonadExcept;
x_10 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_TermParserM_Alternative;
x_12 = l_Lean_Parser_command_NotationSpec_mixfixSymbol;
x_13 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_mixfixSymbol;
x_6 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldActionFolder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("foldActionFolder");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_1);
lean::cnstr_set(x_3, 3, x_0);
lean::cnstr_set(x_3, 4, x_2);
lean::cnstr_set(x_3, 5, x_0);
return x_3;
}
}
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1;
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
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
switch (lean::obj_tag(x_28)) {
case 1:
{
obj* x_38; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_36 = x_38;
goto lbl_37;
}
case 3:
{
obj* x_41; 
x_41 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_36 = x_41;
goto lbl_37;
}
default:
{
obj* x_43; 
lean::dec(x_28);
x_43 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_36 = x_43;
goto lbl_37;
}
}
lbl_37:
{
obj* x_44; obj* x_45; 
if (lean::obj_tag(x_27) == 0)
{
obj* x_47; 
x_47 = lean::box(3);
x_44 = x_27;
x_45 = x_47;
goto lbl_46;
}
else
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_27, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_27, 1);
lean::inc(x_50);
lean::dec(x_27);
x_44 = x_50;
x_45 = x_48;
goto lbl_46;
}
lbl_46:
{
obj* x_53; 
switch (lean::obj_tag(x_45)) {
case 1:
{
obj* x_55; 
x_55 = lean::cnstr_get(x_45, 0);
lean::inc(x_55);
lean::dec(x_45);
x_53 = x_55;
goto lbl_54;
}
case 3:
{
obj* x_58; 
x_58 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_53 = x_58;
goto lbl_54;
}
default:
{
obj* x_60; 
lean::dec(x_45);
x_60 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_53 = x_60;
goto lbl_54;
}
}
lbl_54:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; 
if (lean::obj_tag(x_44) == 0)
{
obj* x_68; 
x_68 = lean::box(3);
x_65 = x_44;
x_66 = x_68;
goto lbl_67;
}
else
{
obj* x_69; obj* x_71; 
x_69 = lean::cnstr_get(x_44, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_44, 1);
lean::inc(x_71);
lean::dec(x_44);
x_65 = x_71;
x_66 = x_69;
goto lbl_67;
}
lbl_64:
{
if (lean::obj_tag(x_63) == 0)
{
obj* x_74; obj* x_75; 
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_75, 0, x_18);
lean::cnstr_set(x_75, 1, x_36);
lean::cnstr_set(x_75, 2, x_53);
lean::cnstr_set(x_75, 3, x_61);
lean::cnstr_set(x_75, 4, x_62);
lean::cnstr_set(x_75, 5, x_74);
return x_75;
}
else
{
obj* x_76; 
x_76 = lean::cnstr_get(x_63, 0);
lean::inc(x_76);
lean::dec(x_63);
switch (lean::obj_tag(x_76)) {
case 0:
{
obj* x_79; obj* x_82; obj* x_83; 
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_79);
x_83 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_83, 0, x_18);
lean::cnstr_set(x_83, 1, x_36);
lean::cnstr_set(x_83, 2, x_53);
lean::cnstr_set(x_83, 3, x_61);
lean::cnstr_set(x_83, 4, x_62);
lean::cnstr_set(x_83, 5, x_82);
return x_83;
}
case 3:
{
obj* x_84; obj* x_85; 
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_85, 0, x_18);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_53);
lean::cnstr_set(x_85, 3, x_61);
lean::cnstr_set(x_85, 4, x_62);
lean::cnstr_set(x_85, 5, x_84);
return x_85;
}
default:
{
obj* x_87; obj* x_88; 
lean::dec(x_76);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_88, 0, x_18);
lean::cnstr_set(x_88, 1, x_36);
lean::cnstr_set(x_88, 2, x_53);
lean::cnstr_set(x_88, 3, x_61);
lean::cnstr_set(x_88, 4, x_62);
lean::cnstr_set(x_88, 5, x_87);
return x_88;
}
}
}
}
lbl_67:
{
obj* x_89; 
switch (lean::obj_tag(x_66)) {
case 0:
{
obj* x_91; obj* x_94; 
x_91 = lean::cnstr_get(x_66, 0);
lean::inc(x_91);
lean::dec(x_66);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_91);
if (lean::obj_tag(x_65) == 0)
{
x_89 = x_94;
goto lbl_90;
}
else
{
obj* x_95; obj* x_97; 
x_95 = lean::cnstr_get(x_65, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_65, 1);
lean::inc(x_97);
lean::dec(x_65);
x_61 = x_94;
x_62 = x_95;
x_63 = x_97;
goto lbl_64;
}
}
case 3:
{
obj* x_100; 
x_100 = lean::box(0);
if (lean::obj_tag(x_65) == 0)
{
x_89 = x_100;
goto lbl_90;
}
else
{
obj* x_101; obj* x_103; 
x_101 = lean::cnstr_get(x_65, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_65, 1);
lean::inc(x_103);
lean::dec(x_65);
x_61 = x_100;
x_62 = x_101;
x_63 = x_103;
goto lbl_64;
}
}
default:
{
obj* x_107; 
lean::dec(x_66);
x_107 = lean::box(0);
if (lean::obj_tag(x_65) == 0)
{
x_89 = x_107;
goto lbl_90;
}
else
{
obj* x_108; obj* x_110; 
x_108 = lean::cnstr_get(x_65, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_65, 1);
lean::inc(x_110);
lean::dec(x_65);
x_61 = x_107;
x_62 = x_108;
x_63 = x_110;
goto lbl_64;
}
}
}
lbl_90:
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_113; obj* x_114; obj* x_115; 
x_113 = lean::box(0);
x_114 = lean::box(3);
x_115 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_115, 0, x_18);
lean::cnstr_set(x_115, 1, x_36);
lean::cnstr_set(x_115, 2, x_53);
lean::cnstr_set(x_115, 3, x_89);
lean::cnstr_set(x_115, 4, x_114);
lean::cnstr_set(x_115, 5, x_113);
return x_115;
}
else
{
obj* x_116; 
x_116 = lean::cnstr_get(x_65, 0);
lean::inc(x_116);
lean::dec(x_65);
switch (lean::obj_tag(x_116)) {
case 0:
{
obj* x_119; obj* x_122; obj* x_123; obj* x_124; 
x_119 = lean::cnstr_get(x_116, 0);
lean::inc(x_119);
lean::dec(x_116);
x_122 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_122, 0, x_119);
x_123 = lean::box(3);
x_124 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_124, 0, x_18);
lean::cnstr_set(x_124, 1, x_36);
lean::cnstr_set(x_124, 2, x_53);
lean::cnstr_set(x_124, 3, x_89);
lean::cnstr_set(x_124, 4, x_123);
lean::cnstr_set(x_124, 5, x_122);
return x_124;
}
case 3:
{
obj* x_125; obj* x_126; obj* x_127; 
x_125 = lean::box(0);
x_126 = lean::box(3);
x_127 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_127, 0, x_18);
lean::cnstr_set(x_127, 1, x_36);
lean::cnstr_set(x_127, 2, x_53);
lean::cnstr_set(x_127, 3, x_89);
lean::cnstr_set(x_127, 4, x_126);
lean::cnstr_set(x_127, 5, x_125);
return x_127;
}
default:
{
obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_116);
x_129 = lean::box(0);
x_130 = lean::box(3);
x_131 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_131, 0, x_18);
lean::cnstr_set(x_131, 1, x_36);
lean::cnstr_set(x_131, 2, x_53);
lean::cnstr_set(x_131, 3, x_89);
lean::cnstr_set(x_131, 4, x_130);
lean::cnstr_set(x_131, 5, x_129);
return x_131;
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_3);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
x_16 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_22; 
x_22 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_17 = x_22;
goto lbl_18;
}
else
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_7, 0);
lean::inc(x_23);
lean::dec(x_7);
x_26 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_19 = x_26;
x_20 = x_23;
goto lbl_21;
}
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_29 = x_1;
} else {
 lean::inc(x_27);
 lean::dec(x_1);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::box(3);
x_33 = l_Option_getOrElse___main___rarg(x_31, x_32);
lean::dec(x_31);
if (lean::obj_tag(x_7) == 0)
{
x_17 = x_33;
goto lbl_18;
}
else
{
obj* x_35; 
x_35 = lean::cnstr_get(x_7, 0);
lean::inc(x_35);
lean::dec(x_7);
x_19 = x_33;
x_20 = x_35;
goto lbl_21;
}
}
lbl_18:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_38 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_9);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_15);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_14);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_17);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
return x_46;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_47 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_49 = x_11;
} else {
 lean::inc(x_47);
 lean::dec(x_11);
 x_49 = lean::box(0);
}
x_50 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::box(3);
x_53 = l_Option_getOrElse___main___rarg(x_51, x_52);
lean::dec(x_51);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_16);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_9);
lean::cnstr_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_15);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_14);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_17);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_63 = l_Lean_Parser_Syntax_mkNode(x_62, x_61);
return x_63;
}
}
lbl_21:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_20);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::box(3);
x_67 = l_Option_getOrElse___main___rarg(x_65, x_66);
lean::dec(x_65);
if (lean::obj_tag(x_11) == 0)
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_69 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_9);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_15);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_14);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_19);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_76 = l_Lean_Parser_Syntax_mkNode(x_75, x_74);
return x_76;
}
else
{
obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_77 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_79 = x_11;
} else {
 lean::inc(x_77);
 lean::dec(x_11);
 x_79 = lean::box(0);
}
x_80 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_79)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_79;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = l_Option_getOrElse___main___rarg(x_81, x_66);
lean::dec(x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_16);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_9);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_67);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_15);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_14);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_19);
lean::cnstr_set(x_89, 1, x_88);
x_90 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_91 = l_Lean_Parser_Syntax_mkNode(x_90, x_89);
return x_91;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("foldAction");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::apply_1(x_8, x_5);
x_12 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_5);
lean::cnstr_set(x_13, 2, x_6);
lean::cnstr_set(x_13, 3, x_11);
lean::cnstr_set(x_13, 4, x_5);
lean::cnstr_set(x_13, 5, x_12);
lean::cnstr_set(x_13, 6, x_0);
return x_13;
}
}
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2;
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
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; obj* x_37; 
if (lean::obj_tag(x_27) == 0)
{
obj* x_39; 
x_39 = lean::box(3);
x_36 = x_27;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; obj* x_42; 
x_40 = lean::cnstr_get(x_27, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_27, 1);
lean::inc(x_42);
lean::dec(x_27);
x_36 = x_42;
x_37 = x_40;
goto lbl_38;
}
lbl_38:
{
obj* x_45; obj* x_46; obj* x_50; obj* x_51; obj* x_52; 
x_45 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
lean::dec(x_45);
lean::inc(x_46);
x_50 = lean::apply_1(x_46, x_37);
if (lean::obj_tag(x_36) == 0)
{
obj* x_54; 
x_54 = lean::box(3);
x_51 = x_36;
x_52 = x_54;
goto lbl_53;
}
else
{
obj* x_55; obj* x_57; 
x_55 = lean::cnstr_get(x_36, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_36, 1);
lean::inc(x_57);
lean::dec(x_36);
x_51 = x_57;
x_52 = x_55;
goto lbl_53;
}
lbl_53:
{
obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; 
x_60 = l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::apply_1(x_61, x_52);
if (lean::obj_tag(x_51) == 0)
{
obj* x_68; 
x_68 = lean::box(3);
x_65 = x_51;
x_66 = x_68;
goto lbl_67;
}
else
{
obj* x_69; obj* x_71; 
x_69 = lean::cnstr_get(x_51, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_51, 1);
lean::inc(x_71);
lean::dec(x_51);
x_65 = x_71;
x_66 = x_69;
goto lbl_67;
}
lbl_67:
{
if (lean::obj_tag(x_65) == 0)
{
lean::dec(x_46);
if (lean::obj_tag(x_65) == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = lean::box(0);
x_76 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_77 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_77, 0, x_18);
lean::cnstr_set(x_77, 1, x_28);
lean::cnstr_set(x_77, 2, x_50);
lean::cnstr_set(x_77, 3, x_64);
lean::cnstr_set(x_77, 4, x_66);
lean::cnstr_set(x_77, 5, x_76);
lean::cnstr_set(x_77, 6, x_75);
return x_77;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_65, 0);
lean::inc(x_78);
lean::dec(x_65);
switch (lean::obj_tag(x_78)) {
case 0:
{
obj* x_81; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_81);
x_85 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_86 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_86, 0, x_18);
lean::cnstr_set(x_86, 1, x_28);
lean::cnstr_set(x_86, 2, x_50);
lean::cnstr_set(x_86, 3, x_64);
lean::cnstr_set(x_86, 4, x_66);
lean::cnstr_set(x_86, 5, x_85);
lean::cnstr_set(x_86, 6, x_84);
return x_86;
}
case 3:
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = lean::box(0);
x_88 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_89 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_89, 0, x_18);
lean::cnstr_set(x_89, 1, x_28);
lean::cnstr_set(x_89, 2, x_50);
lean::cnstr_set(x_89, 3, x_64);
lean::cnstr_set(x_89, 4, x_66);
lean::cnstr_set(x_89, 5, x_88);
lean::cnstr_set(x_89, 6, x_87);
return x_89;
}
default:
{
obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_78);
x_91 = lean::box(0);
x_92 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_93 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_93, 0, x_18);
lean::cnstr_set(x_93, 1, x_28);
lean::cnstr_set(x_93, 2, x_50);
lean::cnstr_set(x_93, 3, x_64);
lean::cnstr_set(x_93, 4, x_66);
lean::cnstr_set(x_93, 5, x_92);
lean::cnstr_set(x_93, 6, x_91);
return x_93;
}
}
}
}
else
{
obj* x_94; obj* x_96; obj* x_99; 
x_94 = lean::cnstr_get(x_65, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_65, 1);
lean::inc(x_96);
lean::dec(x_65);
x_99 = lean::apply_1(x_46, x_94);
if (lean::obj_tag(x_96) == 0)
{
obj* x_100; obj* x_101; 
x_100 = lean::box(0);
x_101 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_101, 0, x_18);
lean::cnstr_set(x_101, 1, x_28);
lean::cnstr_set(x_101, 2, x_50);
lean::cnstr_set(x_101, 3, x_64);
lean::cnstr_set(x_101, 4, x_66);
lean::cnstr_set(x_101, 5, x_99);
lean::cnstr_set(x_101, 6, x_100);
return x_101;
}
else
{
obj* x_102; 
x_102 = lean::cnstr_get(x_96, 0);
lean::inc(x_102);
lean::dec(x_96);
switch (lean::obj_tag(x_102)) {
case 0:
{
obj* x_105; obj* x_108; obj* x_109; 
x_105 = lean::cnstr_get(x_102, 0);
lean::inc(x_105);
lean::dec(x_102);
x_108 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_108, 0, x_105);
x_109 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_109, 0, x_18);
lean::cnstr_set(x_109, 1, x_28);
lean::cnstr_set(x_109, 2, x_50);
lean::cnstr_set(x_109, 3, x_64);
lean::cnstr_set(x_109, 4, x_66);
lean::cnstr_set(x_109, 5, x_99);
lean::cnstr_set(x_109, 6, x_108);
return x_109;
}
case 3:
{
obj* x_110; obj* x_111; 
x_110 = lean::box(0);
x_111 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_111, 0, x_18);
lean::cnstr_set(x_111, 1, x_28);
lean::cnstr_set(x_111, 2, x_50);
lean::cnstr_set(x_111, 3, x_64);
lean::cnstr_set(x_111, 4, x_66);
lean::cnstr_set(x_111, 5, x_99);
lean::cnstr_set(x_111, 6, x_110);
return x_111;
}
default:
{
obj* x_113; obj* x_114; 
lean::dec(x_102);
x_113 = lean::box(0);
x_114 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_114, 0, x_18);
lean::cnstr_set(x_114, 1, x_28);
lean::cnstr_set(x_114, 2, x_50);
lean::cnstr_set(x_114, 3, x_64);
lean::cnstr_set(x_114, 4, x_66);
lean::cnstr_set(x_114, 5, x_99);
lean::cnstr_set(x_114, 6, x_113);
return x_114;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
lean::inc(x_17);
x_21 = lean::apply_1(x_17, x_5);
x_22 = l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_7);
x_27 = lean::apply_1(x_17, x_11);
x_28 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_29 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_26);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_21);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_3);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = l_Lean_Parser_command_NotationSpec_foldAction;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_39 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_41 = x_13;
} else {
 lean::inc(x_39);
 lean::dec(x_13);
 x_41 = lean::box(0);
}
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::box(3);
x_45 = l_Option_getOrElse___main___rarg(x_43, x_44);
lean::dec(x_43);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_28);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_27);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_9);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_26);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_21);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_3);
lean::cnstr_set(x_52, 1, x_51);
x_53 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_Lean_Parser_command_NotationSpec_foldAction;
x_56 = l_Lean_Parser_Syntax_mkNode(x_55, x_54);
return x_56;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_57 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_59 = x_1;
} else {
 lean::inc(x_57);
 lean::dec(x_1);
 x_59 = lean::box(0);
}
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_57);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::box(3);
x_63 = l_Option_getOrElse___main___rarg(x_61, x_62);
lean::dec(x_61);
if (lean::obj_tag(x_13) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_65 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_27);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_9);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_26);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_21);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_3);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_63);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_Lean_Parser_command_NotationSpec_foldAction;
x_73 = l_Lean_Parser_Syntax_mkNode(x_72, x_71);
return x_73;
}
else
{
obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_74 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_76 = x_13;
} else {
 lean::inc(x_74);
 lean::dec(x_13);
 x_76 = lean::box(0);
}
x_77 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_77, 0, x_74);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = l_Option_getOrElse___main___rarg(x_78, x_62);
lean::dec(x_78);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_28);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_27);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_9);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_26);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_21);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_3);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_63);
lean::cnstr_set(x_87, 1, x_86);
x_88 = l_Lean_Parser_command_NotationSpec_foldAction;
x_89 = l_Lean_Parser_Syntax_mkNode(x_88, x_87);
return x_89;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27;
return x_0;
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_11; obj* x_12; 
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_11 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
} else {
 lean::inc(x_19);
 lean::dec(x_11);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
else
{
uint8 x_23; 
x_23 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_24 = lean::cnstr_get(x_11, 1);
lean::inc(x_24);
lean::dec(x_11);
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
lean::dec(x_12);
x_30 = lean::apply_5(x_1, x_2, x_3, x_4, x_5, x_24);
x_31 = lean::cnstr_get(x_30, 0);
x_33 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
x_36 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_27, x_31);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
return x_37;
}
else
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_43 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_45 = x_11;
} else {
 lean::inc(x_43);
 lean::dec(x_11);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_12);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
}
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___rarg), 7, 0);
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; 
x_7 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___rarg), 7, 2);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_8);
x_0 = x_13;
x_1 = x_10;
goto _start;
}
}
}
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
x_7 = l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
else
{
obj* x_14; obj* x_16; obj* x_19; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_List_foldl___main___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__3(x_14, x_16, x_1, x_2, x_3, x_4, x_5);
return x_19;
}
}
}
obj* _init_l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_Lean_Parser_token(x_0, x_2, x_3);
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
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
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
x_27 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_28 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_26, x_27);
x_29 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_28);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
return x_30;
}
case 3:
{
obj* x_33; 
lean::dec(x_11);
lean::dec(x_18);
x_33 = lean::box(0);
x_19 = x_33;
goto lbl_20;
}
default:
{
obj* x_37; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_37 = lean::box(0);
x_19 = x_37;
goto lbl_20;
}
}
lbl_20:
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_19);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_2);
x_40 = lean::box(0);
x_41 = l_String_splitAux___main___closed__1;
x_42 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_43 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_41, x_42, x_39, x_40, x_0, x_14, x_9);
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_39);
x_47 = lean::cnstr_get(x_43, 0);
x_49 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_51 = x_43;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_43);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_47);
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_52);
x_55 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_54, x_42);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
if (lean::is_scalar(x_51)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_51;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_49);
return x_57;
}
}
else
{
obj* x_60; obj* x_62; obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_2);
x_60 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_62 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_7, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_66 = x_7;
} else {
 lean::inc(x_63);
 lean::dec(x_7);
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
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_68);
x_71 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_70, x_71);
x_73 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_72);
if (lean::is_scalar(x_62)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_62;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_60);
return x_74;
}
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 4, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_41; obj* x_44; obj* x_47; 
x_0 = lean::mk_string("(");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_4);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_5);
lean::dec(x_5);
x_8 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
x_10 = lean::mk_string(",");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_1);
lean::dec(x_10);
x_13 = lean::mk_string(")");
x_14 = l_Lean_Parser_symbol_tokens___rarg(x_13, x_1);
lean::dec(x_13);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_4);
lean::dec(x_14);
x_18 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_16);
x_20 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_19);
lean::dec(x_19);
lean::dec(x_11);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_20);
lean::dec(x_20);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_23);
lean::dec(x_23);
x_27 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_25);
lean::dec(x_25);
x_29 = l_Lean_Parser_tokens___rarg(x_27);
lean::dec(x_27);
x_31 = l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens;
x_32 = l_Lean_Parser_List_cons_tokens___rarg(x_31, x_16);
lean::dec(x_16);
x_34 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_32);
lean::dec(x_32);
x_36 = l_Lean_Parser_List_cons_tokens___rarg(x_29, x_34);
lean::dec(x_34);
lean::dec(x_29);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_31, x_36);
lean::dec(x_36);
x_41 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_39);
lean::dec(x_39);
lean::dec(x_8);
x_44 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_41);
lean::dec(x_41);
lean::dec(x_2);
x_47 = l_Lean_Parser_tokens___rarg(x_44);
lean::dec(x_44);
return x_47;
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_orelse___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("foldl");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("foldr");
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__1), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_string(",");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_21, 0, x_5);
x_22 = lean::mk_string(")");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_26, 0, x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_27, 0, x_23);
lean::closure_set(x_27, 1, x_5);
lean::closure_set(x_27, 2, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_11);
lean::inc(x_28);
lean::inc(x_21);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set(x_31, 1, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_20);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
lean::inc(x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_32);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
lean::inc(x_6);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_6);
lean::cnstr_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_40, 0, x_39);
lean::closure_set(x_40, 1, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
lean::inc(x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_28);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_21);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_14);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_6);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_Lean_Parser_TermParserM_Monad;
x_50 = l_Lean_Parser_TermParserM_MonadExcept;
x_51 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_52 = l_Lean_Parser_TermParserM_Alternative;
x_53 = l_Lean_Parser_command_NotationSpec_foldAction;
x_54 = l_Lean_Parser_command_NotationSpec_foldAction_HasView;
x_55 = l_Lean_Parser_Combinators_node_view___rarg(x_49, x_50, x_51, x_52, x_53, x_48, x_54);
lean::dec(x_48);
return x_55;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("foldl");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("foldr");
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__1), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_string(",");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_21, 0, x_5);
x_22 = lean::mk_string(")");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_26, 0, x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_27, 0, x_23);
lean::closure_set(x_27, 1, x_5);
lean::closure_set(x_27, 2, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_11);
lean::inc(x_28);
lean::inc(x_21);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set(x_31, 1, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_20);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
lean::inc(x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_32);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
lean::inc(x_6);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_6);
lean::cnstr_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_command_NotationSpec_foldActionFolder;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_40, 0, x_39);
lean::closure_set(x_40, 1, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
lean::inc(x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_28);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_21);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_14);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_6);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
obj* l_Lean_Parser_command_NotationSpec_foldAction_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_foldAction;
x_6 = l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_scopedAction() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("scopedAction");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_3 = lean::box(3);
x_4 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_1 = x_5;
goto lbl_2;
}
else
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_8);
x_1 = x_0;
goto lbl_2;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_9, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
lean::dec(x_9);
x_18 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_15);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_22);
x_1 = x_23;
goto lbl_2;
}
else
{
obj* x_27; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_9);
x_27 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_1 = x_27;
goto lbl_2;
}
}
}
lbl_2:
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::box(3);
x_29 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_30 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_1);
lean::cnstr_set(x_30, 3, x_29);
lean::cnstr_set(x_30, 4, x_0);
lean::cnstr_set(x_30, 5, x_28);
lean::cnstr_set(x_30, 6, x_0);
return x_30;
}
}
}
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1;
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
else
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_23) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_1 = x_20;
x_2 = x_24;
goto lbl_3;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_1 = x_27;
x_2 = x_25;
goto lbl_3;
}
}
else
{
obj* x_30; obj* x_33; obj* x_36; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_List_append___rarg(x_33, x_20);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(3);
x_1 = x_36;
x_2 = x_37;
goto lbl_3;
}
else
{
obj* x_38; obj* x_40; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_1 = x_40;
x_2 = x_38;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_43; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_2, 0);
lean::inc(x_45);
lean::dec(x_2);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_45);
x_43 = x_48;
goto lbl_44;
}
case 3:
{
obj* x_49; 
x_49 = lean::box(0);
x_43 = x_49;
goto lbl_44;
}
default:
{
obj* x_51; 
lean::dec(x_2);
x_51 = lean::box(0);
x_43 = x_51;
goto lbl_44;
}
}
lbl_44:
{
obj* x_52; obj* x_53; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_55; 
x_55 = lean::box(3);
x_52 = x_1;
x_53 = x_55;
goto lbl_54;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_1, 1);
lean::inc(x_58);
lean::dec(x_1);
x_52 = x_58;
x_53 = x_56;
goto lbl_54;
}
lbl_54:
{
obj* x_61; obj* x_62; 
if (lean::obj_tag(x_52) == 0)
{
obj* x_64; 
x_64 = lean::box(3);
x_61 = x_52;
x_62 = x_64;
goto lbl_63;
}
else
{
obj* x_65; obj* x_67; 
x_65 = lean::cnstr_get(x_52, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_52, 1);
lean::inc(x_67);
lean::dec(x_52);
x_61 = x_67;
x_62 = x_65;
goto lbl_63;
}
lbl_63:
{
obj* x_70; obj* x_72; 
x_72 = l_Lean_Parser_Syntax_asNode___main(x_62);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; 
x_73 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_70 = x_73;
goto lbl_71;
}
else
{
obj* x_74; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_set(x_72, 0, lean::box(0));
 x_76 = x_72;
} else {
 lean::inc(x_74);
 lean::dec(x_72);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; 
lean::dec(x_76);
x_81 = lean::box(0);
x_70 = x_81;
goto lbl_71;
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_77, 1);
lean::inc(x_82);
if (lean::obj_tag(x_82) == 0)
{
obj* x_84; obj* x_87; obj* x_88; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_77, 0);
lean::inc(x_84);
lean::dec(x_77);
x_87 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
lean::dec(x_87);
x_91 = lean::apply_1(x_88, x_84);
if (lean::is_scalar(x_76)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_76;
}
lean::cnstr_set(x_92, 0, x_91);
x_70 = x_92;
goto lbl_71;
}
else
{
obj* x_96; 
lean::dec(x_82);
lean::dec(x_76);
lean::dec(x_77);
x_96 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_70 = x_96;
goto lbl_71;
}
}
}
lbl_71:
{
obj* x_97; obj* x_98; 
if (lean::obj_tag(x_61) == 0)
{
obj* x_100; 
x_100 = lean::box(3);
x_97 = x_61;
x_98 = x_100;
goto lbl_99;
}
else
{
obj* x_101; obj* x_103; 
x_101 = lean::cnstr_get(x_61, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_61, 1);
lean::inc(x_103);
lean::dec(x_61);
x_97 = x_103;
x_98 = x_101;
goto lbl_99;
}
lbl_99:
{
obj* x_106; 
switch (lean::obj_tag(x_98)) {
case 1:
{
obj* x_108; 
x_108 = lean::cnstr_get(x_98, 0);
lean::inc(x_108);
lean::dec(x_98);
x_106 = x_108;
goto lbl_107;
}
case 3:
{
obj* x_111; 
x_111 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_106 = x_111;
goto lbl_107;
}
default:
{
obj* x_113; 
lean::dec(x_98);
x_113 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_106 = x_113;
goto lbl_107;
}
}
lbl_107:
{
obj* x_114; obj* x_115; obj* x_116; obj* x_118; obj* x_119; 
if (lean::obj_tag(x_97) == 0)
{
obj* x_121; 
x_121 = lean::box(3);
x_118 = x_97;
x_119 = x_121;
goto lbl_120;
}
else
{
obj* x_122; obj* x_124; 
x_122 = lean::cnstr_get(x_97, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_97, 1);
lean::inc(x_124);
lean::dec(x_97);
x_118 = x_124;
x_119 = x_122;
goto lbl_120;
}
lbl_117:
{
if (lean::obj_tag(x_116) == 0)
{
obj* x_127; obj* x_128; 
x_127 = lean::box(0);
x_128 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_128, 0, x_43);
lean::cnstr_set(x_128, 1, x_53);
lean::cnstr_set(x_128, 2, x_70);
lean::cnstr_set(x_128, 3, x_106);
lean::cnstr_set(x_128, 4, x_114);
lean::cnstr_set(x_128, 5, x_115);
lean::cnstr_set(x_128, 6, x_127);
return x_128;
}
else
{
obj* x_129; 
x_129 = lean::cnstr_get(x_116, 0);
lean::inc(x_129);
lean::dec(x_116);
switch (lean::obj_tag(x_129)) {
case 0:
{
obj* x_132; obj* x_135; obj* x_136; 
x_132 = lean::cnstr_get(x_129, 0);
lean::inc(x_132);
lean::dec(x_129);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_132);
x_136 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_136, 0, x_43);
lean::cnstr_set(x_136, 1, x_53);
lean::cnstr_set(x_136, 2, x_70);
lean::cnstr_set(x_136, 3, x_106);
lean::cnstr_set(x_136, 4, x_114);
lean::cnstr_set(x_136, 5, x_115);
lean::cnstr_set(x_136, 6, x_135);
return x_136;
}
case 3:
{
obj* x_137; obj* x_138; 
x_137 = lean::box(0);
x_138 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_138, 0, x_43);
lean::cnstr_set(x_138, 1, x_53);
lean::cnstr_set(x_138, 2, x_70);
lean::cnstr_set(x_138, 3, x_106);
lean::cnstr_set(x_138, 4, x_114);
lean::cnstr_set(x_138, 5, x_115);
lean::cnstr_set(x_138, 6, x_137);
return x_138;
}
default:
{
obj* x_140; obj* x_141; 
lean::dec(x_129);
x_140 = lean::box(0);
x_141 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_141, 0, x_43);
lean::cnstr_set(x_141, 1, x_53);
lean::cnstr_set(x_141, 2, x_70);
lean::cnstr_set(x_141, 3, x_106);
lean::cnstr_set(x_141, 4, x_114);
lean::cnstr_set(x_141, 5, x_115);
lean::cnstr_set(x_141, 6, x_140);
return x_141;
}
}
}
}
lbl_120:
{
obj* x_142; 
switch (lean::obj_tag(x_119)) {
case 0:
{
obj* x_144; obj* x_147; 
x_144 = lean::cnstr_get(x_119, 0);
lean::inc(x_144);
lean::dec(x_119);
x_147 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_147, 0, x_144);
if (lean::obj_tag(x_118) == 0)
{
x_142 = x_147;
goto lbl_143;
}
else
{
obj* x_148; obj* x_150; 
x_148 = lean::cnstr_get(x_118, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_118, 1);
lean::inc(x_150);
lean::dec(x_118);
x_114 = x_147;
x_115 = x_148;
x_116 = x_150;
goto lbl_117;
}
}
case 3:
{
obj* x_153; 
x_153 = lean::box(0);
if (lean::obj_tag(x_118) == 0)
{
x_142 = x_153;
goto lbl_143;
}
else
{
obj* x_154; obj* x_156; 
x_154 = lean::cnstr_get(x_118, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_118, 1);
lean::inc(x_156);
lean::dec(x_118);
x_114 = x_153;
x_115 = x_154;
x_116 = x_156;
goto lbl_117;
}
}
default:
{
obj* x_160; 
lean::dec(x_119);
x_160 = lean::box(0);
if (lean::obj_tag(x_118) == 0)
{
x_142 = x_160;
goto lbl_143;
}
else
{
obj* x_161; obj* x_163; 
x_161 = lean::cnstr_get(x_118, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_118, 1);
lean::inc(x_163);
lean::dec(x_118);
x_114 = x_160;
x_115 = x_161;
x_116 = x_163;
goto lbl_117;
}
}
}
lbl_143:
{
if (lean::obj_tag(x_118) == 0)
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::box(0);
x_167 = lean::box(3);
x_168 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_168, 0, x_43);
lean::cnstr_set(x_168, 1, x_53);
lean::cnstr_set(x_168, 2, x_70);
lean::cnstr_set(x_168, 3, x_106);
lean::cnstr_set(x_168, 4, x_142);
lean::cnstr_set(x_168, 5, x_167);
lean::cnstr_set(x_168, 6, x_166);
return x_168;
}
else
{
obj* x_169; 
x_169 = lean::cnstr_get(x_118, 0);
lean::inc(x_169);
lean::dec(x_118);
switch (lean::obj_tag(x_169)) {
case 0:
{
obj* x_172; obj* x_175; obj* x_176; obj* x_177; 
x_172 = lean::cnstr_get(x_169, 0);
lean::inc(x_172);
lean::dec(x_169);
x_175 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_175, 0, x_172);
x_176 = lean::box(3);
x_177 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_177, 0, x_43);
lean::cnstr_set(x_177, 1, x_53);
lean::cnstr_set(x_177, 2, x_70);
lean::cnstr_set(x_177, 3, x_106);
lean::cnstr_set(x_177, 4, x_142);
lean::cnstr_set(x_177, 5, x_176);
lean::cnstr_set(x_177, 6, x_175);
return x_177;
}
case 3:
{
obj* x_178; obj* x_179; obj* x_180; 
x_178 = lean::box(0);
x_179 = lean::box(3);
x_180 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_180, 0, x_43);
lean::cnstr_set(x_180, 1, x_53);
lean::cnstr_set(x_180, 2, x_70);
lean::cnstr_set(x_180, 3, x_106);
lean::cnstr_set(x_180, 4, x_142);
lean::cnstr_set(x_180, 5, x_179);
lean::cnstr_set(x_180, 6, x_178);
return x_180;
}
default:
{
obj* x_182; obj* x_183; obj* x_184; 
lean::dec(x_169);
x_182 = lean::box(0);
x_183 = lean::box(3);
x_184 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_184, 0, x_43);
lean::cnstr_set(x_184, 1, x_53);
lean::cnstr_set(x_184, 2, x_70);
lean::cnstr_set(x_184, 3, x_106);
lean::cnstr_set(x_184, 4, x_142);
lean::cnstr_set(x_184, 5, x_183);
lean::cnstr_set(x_184, 6, x_182);
return x_184;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_7);
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; 
x_21 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_19 = x_21;
goto lbl_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_24 = x_1;
} else {
 lean::inc(x_22);
 lean::dec(x_1);
 x_24 = lean::box(0);
}
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::box(3);
x_28 = l_Option_getOrElse___main___rarg(x_26, x_27);
lean::dec(x_26);
x_19 = x_28;
goto lbl_20;
}
lbl_20:
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_17);
x_31 = l_Lean_Parser_noKind;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_38; 
x_38 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_33 = x_38;
goto lbl_34;
}
else
{
obj* x_39; obj* x_42; 
x_39 = lean::cnstr_get(x_9, 0);
lean::inc(x_39);
lean::dec(x_9);
x_42 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_35 = x_42;
x_36 = x_39;
goto lbl_37;
}
}
else
{
obj* x_43; obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_5, 0);
lean::inc(x_43);
lean::dec(x_5);
x_46 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_43);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_16);
x_52 = l_Lean_Parser_Syntax_mkNode(x_31, x_51);
if (lean::obj_tag(x_9) == 0)
{
x_33 = x_52;
goto lbl_34;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_9, 0);
lean::inc(x_53);
lean::dec(x_9);
x_35 = x_52;
x_36 = x_53;
goto lbl_37;
}
}
lbl_34:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_56 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_11);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_18);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_33);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_32);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_64 = l_Lean_Parser_Syntax_mkNode(x_63, x_62);
return x_64;
}
else
{
obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_65 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_67 = x_13;
} else {
 lean::inc(x_65);
 lean::dec(x_13);
 x_67 = lean::box(0);
}
x_68 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_68, 0, x_65);
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::box(3);
x_71 = l_Option_getOrElse___main___rarg(x_69, x_70);
lean::dec(x_69);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_16);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_11);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_18);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_33);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_32);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_81 = l_Lean_Parser_Syntax_mkNode(x_80, x_79);
return x_81;
}
}
lbl_37:
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_82 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_82, 0, x_36);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_84 = lean::box(3);
x_85 = l_Option_getOrElse___main___rarg(x_83, x_84);
lean::dec(x_83);
if (lean::obj_tag(x_13) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_87 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_11);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_18);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_35);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_32);
lean::cnstr_set(x_92, 1, x_91);
x_93 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_94 = l_Lean_Parser_Syntax_mkNode(x_93, x_92);
return x_94;
}
else
{
obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_95 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_97 = x_13;
} else {
 lean::inc(x_95);
 lean::dec(x_13);
 x_97 = lean::box(0);
}
x_98 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_98, 0, x_95);
if (lean::is_scalar(x_97)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_97;
}
lean::cnstr_set(x_99, 0, x_98);
x_100 = l_Option_getOrElse___main___rarg(x_99, x_84);
lean::dec(x_99);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_16);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_11);
lean::cnstr_set(x_103, 1, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_85);
lean::cnstr_set(x_104, 1, x_103);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_18);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_35);
lean::cnstr_set(x_106, 1, x_105);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_32);
lean::cnstr_set(x_107, 1, x_106);
x_108 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_109 = l_Lean_Parser_Syntax_mkNode(x_108, x_107);
return x_109;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_actionKind() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("actionKind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("actionKind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = lean::mk_nat_obj(1ul);
x_58 = lean::nat_dec_eq(x_39, x_57);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; 
x_59 = lean::mk_nat_obj(2ul);
x_60 = lean::nat_dec_eq(x_39, x_59);
lean::dec(x_39);
if (x_60 == 0)
{
obj* x_62; obj* x_63; obj* x_66; obj* x_67; 
x_62 = l_Lean_Parser_command_NotationSpec_foldAction_HasView;
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
lean::dec(x_62);
x_66 = lean::apply_1(x_63, x_52);
x_67 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_72; obj* x_73; 
x_68 = l_Lean_Parser_command_NotationSpec_scopedAction_HasView;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_52);
x_73 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
else
{
obj* x_75; 
lean::dec(x_39);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_52);
return x_75;
}
}
else
{
obj* x_77; obj* x_78; obj* x_81; obj* x_82; 
lean::dec(x_39);
x_77 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
lean::dec(x_77);
x_81 = lean::apply_1(x_78, x_52);
x_82 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
}
else
{
obj* x_86; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_86 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_86;
}
}
}
}
}
}
}
else
{
obj* x_89; 
lean::dec(x_8);
lean::dec(x_17);
x_89 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1;
return x_89;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView;
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
x_14 = l_Lean_Parser_command_NotationSpec_actionKind;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_1);
x_20 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_21 = l_Lean_Parser_Syntax_mkNode(x_20, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_Lean_Parser_command_NotationSpec_actionKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
case 2:
{
obj* x_25; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = l_Lean_Parser_command_NotationSpec_scopedAction_HasView;
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
lean::dec(x_28);
x_32 = lean::apply_1(x_29, x_25);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_1);
x_34 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
x_35 = l_Lean_Parser_Syntax_mkNode(x_34, x_33);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_1);
x_37 = l_Lean_Parser_command_NotationSpec_actionKind;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
default:
{
obj* x_39; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
lean::dec(x_0);
x_42 = l_Lean_Parser_command_NotationSpec_foldAction_HasView;
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_46 = lean::apply_1(x_43, x_39);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_1);
x_48 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_1);
x_51 = l_Lean_Parser_command_NotationSpec_actionKind;
x_52 = l_Lean_Parser_Syntax_mkNode(x_51, x_50);
return x_52;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("action");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_22; obj* x_23; 
x_22 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
x_27 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
lean::dec(x_27);
x_31 = lean::apply_1(x_28, x_24);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_21);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
case 3:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_33; 
x_33 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2;
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
lean::dec(x_1);
x_37 = lean::box(0);
x_38 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_34);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_37);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_45; 
x_45 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2;
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_54; obj* x_55; 
x_46 = lean::cnstr_get(x_1, 0);
lean::inc(x_46);
lean::dec(x_1);
x_49 = lean::box(0);
x_50 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_46);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_49);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_command_NotationSpec_actionKind_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_3);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
if (lean::obj_tag(x_1) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_Lean_Parser_command_NotationSpec_action;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_19 = x_1;
} else {
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::box(3);
x_23 = l_Option_getOrElse___main___rarg(x_21, x_22);
lean::dec(x_21);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_12);
x_26 = l_Lean_Parser_command_NotationSpec_action;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_action_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_34; obj* x_36; obj* x_39; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_65; 
x_0 = lean::mk_string(":");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::box(0);
x_7 = lean::mk_string("(");
x_8 = l_Lean_Parser_symbol_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_6);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_10);
lean::dec(x_10);
lean::dec(x_8);
x_14 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
x_16 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
x_18 = l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens;
x_19 = l_Lean_Parser_tokens___rarg(x_18);
x_20 = lean::mk_string(", ");
x_21 = l_Lean_Parser_symbol_tokens___rarg(x_20, x_1);
lean::dec(x_20);
x_23 = lean::mk_string(")");
x_24 = l_Lean_Parser_symbol_tokens___rarg(x_23, x_1);
lean::dec(x_23);
x_26 = l_Lean_Parser_List_cons_tokens___rarg(x_24, x_6);
lean::dec(x_24);
x_28 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
x_29 = l_Lean_Parser_List_cons_tokens___rarg(x_28, x_26);
lean::dec(x_26);
x_31 = l_Lean_Parser_List_cons_tokens___rarg(x_21, x_29);
lean::dec(x_29);
lean::dec(x_21);
x_34 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_31);
lean::dec(x_31);
x_36 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_34);
lean::dec(x_34);
lean::dec(x_19);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_16, x_36);
lean::dec(x_36);
lean::dec(x_16);
x_42 = l_Lean_Parser_tokens___rarg(x_39);
lean::dec(x_39);
x_44 = l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens;
x_45 = l_Lean_Parser_List_cons_tokens___rarg(x_44, x_6);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_42, x_45);
lean::dec(x_45);
lean::dec(x_42);
x_49 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_46);
lean::dec(x_46);
x_51 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_49);
lean::dec(x_49);
lean::dec(x_5);
x_54 = l_Lean_Parser_tokens___rarg(x_51);
lean::dec(x_51);
x_56 = l_Lean_Parser_List_cons_tokens___rarg(x_54, x_6);
lean::dec(x_54);
x_58 = l_Lean_Parser_tokens___rarg(x_56);
lean::dec(x_56);
x_60 = l_Lean_Parser_List_cons_tokens___rarg(x_58, x_6);
lean::dec(x_58);
x_62 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_60);
lean::dec(x_60);
lean::dec(x_2);
x_65 = l_Lean_Parser_tokens___rarg(x_62);
lean::dec(x_62);
return x_65;
}
}
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_Lean_Parser_command_NotationSpec_precedenceTerm;
x_6 = l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_12 = x_7;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_8);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
obj* l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_6, x_0, x_1, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_12 = x_7;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_8);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_0 = lean::mk_string(":");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("prev");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("(");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_5);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::mk_string("scoped");
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_22 = 0;
x_23 = lean::box(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_24, 0, x_21);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::mk_string(", ");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_31, 0, x_5);
x_32 = lean::mk_string(")");
x_33 = l_String_trim(x_32);
lean::dec(x_32);
lean::inc(x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_36, 0, x_33);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_37, 0, x_33);
lean::closure_set(x_37, 1, x_5);
lean::closure_set(x_37, 2, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_17);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_31);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_24);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_20);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_46, 0, x_45);
lean::closure_set(x_46, 1, x_44);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldAction_Parser), 5, 0);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_17);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_8);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__1), 5, 0);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_53, 0, x_52);
lean::closure_set(x_53, 1, x_5);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_17);
x_55 = l_Lean_Parser_command_NotationSpec_actionKind;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_56, 0, x_55);
lean::closure_set(x_56, 1, x_54);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_17);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_6);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_Parser_TermParserM_Monad;
x_60 = l_Lean_Parser_TermParserM_MonadExcept;
x_61 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_62 = l_Lean_Parser_TermParserM_Alternative;
x_63 = l_Lean_Parser_command_NotationSpec_action;
x_64 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_65 = l_Lean_Parser_Combinators_node_view___rarg(x_59, x_60, x_61, x_62, x_63, x_58, x_64);
lean::dec(x_58);
return x_65;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_action_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_0 = lean::mk_string(":");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("prev");
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("(");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_5);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::mk_string("scoped");
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_22 = 0;
x_23 = lean::box(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_24, 0, x_21);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::mk_string(", ");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_31, 0, x_5);
x_32 = lean::mk_string(")");
x_33 = l_String_trim(x_32);
lean::dec(x_32);
lean::inc(x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_36, 0, x_33);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_37, 0, x_33);
lean::closure_set(x_37, 1, x_5);
lean::closure_set(x_37, 2, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_17);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_31);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_24);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_20);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_NotationSpec_scopedAction;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_46, 0, x_45);
lean::closure_set(x_46, 1, x_44);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_foldAction_Parser), 5, 0);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_17);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_8);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__1), 5, 0);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_53, 0, x_52);
lean::closure_set(x_53, 1, x_5);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_17);
x_55 = l_Lean_Parser_command_NotationSpec_actionKind;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_56, 0, x_55);
lean::closure_set(x_56, 1, x_54);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_17);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_6);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
obj* l_Lean_Parser_command_NotationSpec_action_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_action;
x_6 = l_Lean_Parser_command_NotationSpec_action_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("binder");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_6);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_15);
if (lean::is_scalar(x_6)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_6;
}
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_13);
x_28 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1;
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::box(3);
x_19 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 x_24 = x_19;
} else {
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_24);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_25, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_33);
if (lean::is_scalar(x_24)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_24;
}
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_2);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
lean::dec(x_24);
lean::dec(x_25);
x_46 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_2);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_51 = l_Lean_Parser_Syntax_asNode___main(x_48);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; 
x_52 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_2);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_56 = x_51;
} else {
 lean::inc(x_54);
 lean::dec(x_51);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_56);
x_61 = lean::box(0);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_2);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_57, 1);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_65; obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_74; 
x_65 = lean::cnstr_get(x_57, 0);
lean::inc(x_65);
lean::dec(x_57);
x_68 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_65);
if (lean::is_scalar(x_56)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_56;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_2);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
else
{
obj* x_78; obj* x_79; 
lean::dec(x_56);
lean::dec(x_57);
lean::dec(x_63);
x_78 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_2);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_command_NotationSpec_binder;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_13);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_16);
x_23 = l_Lean_Parser_noKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_NotationSpec_binder;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_binder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binders() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("binders");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_6);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_15);
if (lean::is_scalar(x_6)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_6;
}
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_13);
x_28 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1;
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::box(3);
x_19 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 x_24 = x_19;
} else {
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_24);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_25, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_33);
if (lean::is_scalar(x_24)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_24;
}
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_2);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
lean::dec(x_24);
lean::dec(x_25);
x_46 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_2);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
lean::dec(x_1);
x_51 = l_Lean_Parser_Syntax_asNode___main(x_48);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; 
x_52 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_2);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_56 = x_51;
} else {
 lean::inc(x_54);
 lean::dec(x_51);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_56);
x_61 = lean::box(0);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_2);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_57, 1);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_65; obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_74; 
x_65 = lean::cnstr_get(x_57, 0);
lean::inc(x_65);
lean::dec(x_57);
x_68 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_65);
if (lean::is_scalar(x_56)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_56;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_2);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
else
{
obj* x_78; obj* x_79; 
lean::dec(x_56);
lean::dec(x_57);
lean::dec(x_63);
x_78 = l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1;
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_2);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_command_NotationSpec_binders;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_13);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_16);
x_23 = l_Lean_Parser_noKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_NotationSpec_binders;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binders_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_binders_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_binders_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("argument");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_8 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::box(3);
x_13 = lean::apply_1(x_9, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1;
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
x_10 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
x_20 = lean::apply_1(x_17, x_13);
if (lean::is_scalar(x_5)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_5;
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_27; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_5);
x_27 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1;
return x_27;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_action_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3;
return x_0;
}
}
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5;
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
case 1:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
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
lean::cnstr_set(x_35, 0, x_20);
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
x_41 = l_Lean_Parser_command_NotationSpec_action_HasView;
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
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_29);
x_51 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_20);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_56; obj* x_59; 
x_53 = lean::cnstr_get(x_2, 0);
lean::inc(x_53);
lean::dec(x_2);
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
lean::dec(x_1);
x_59 = l_Lean_Parser_Syntax_asNode___main(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; 
x_60 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4;
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_53);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
else
{
obj* x_62; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_set(x_59, 0, lean::box(0));
 x_64 = x_59;
} else {
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
if (lean::obj_tag(x_65) == 0)
{
obj* x_69; obj* x_70; 
lean::dec(x_64);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_53);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_65, 1);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_76; obj* x_77; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_65, 0);
lean::inc(x_73);
lean::dec(x_65);
x_76 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
lean::dec(x_76);
x_80 = lean::apply_1(x_77, x_73);
if (lean::is_scalar(x_64)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_64;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_53);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
else
{
obj* x_86; obj* x_87; 
lean::dec(x_64);
lean::dec(x_65);
lean::dec(x_71);
x_86 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4;
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_53);
lean::cnstr_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
case 3:
{
obj* x_88; 
x_88 = lean::box(0);
x_18 = x_88;
goto lbl_19;
}
default:
{
obj* x_90; 
lean::dec(x_2);
x_90 = lean::box(0);
x_18 = x_90;
goto lbl_19;
}
}
lbl_19:
{
lean::dec(x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_92; 
x_92 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3;
return x_92;
}
else
{
obj* x_93; obj* x_96; 
x_93 = lean::cnstr_get(x_1, 0);
lean::inc(x_93);
lean::dec(x_1);
x_96 = l_Lean_Parser_Syntax_asNode___main(x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; 
x_97 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1;
return x_97;
}
else
{
obj* x_98; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_set(x_96, 0, lean::box(0));
 x_100 = x_96;
} else {
 lean::inc(x_98);
 lean::dec(x_96);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
if (lean::obj_tag(x_101) == 0)
{
obj* x_105; 
lean::dec(x_100);
x_105 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2;
return x_105;
}
else
{
obj* x_106; 
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_108; obj* x_111; obj* x_112; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_108 = lean::cnstr_get(x_101, 0);
lean::inc(x_108);
lean::dec(x_101);
x_111 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
lean::dec(x_111);
x_115 = lean::apply_1(x_112, x_108);
if (lean::is_scalar(x_100)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_100;
}
lean::cnstr_set(x_116, 0, x_115);
x_117 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
else
{
obj* x_122; 
lean::dec(x_100);
lean::dec(x_106);
lean::dec(x_101);
x_122 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1;
return x_122;
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_command_NotationSpec_argument;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_command_NotationSpec_action_HasView;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_11);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
x_21 = l_Lean_Parser_noKind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_14);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_command_NotationSpec_argument;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
return x_26;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_argument_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_argument_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("transition");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_binder_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("transition");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = lean::mk_nat_obj(1ul);
x_58 = lean::nat_dec_eq(x_39, x_57);
lean::dec(x_39);
if (x_58 == 0)
{
obj* x_60; obj* x_61; obj* x_64; obj* x_65; 
x_60 = l_Lean_Parser_command_NotationSpec_argument_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::apply_1(x_61, x_52);
x_65 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_70; obj* x_71; 
x_66 = l_Lean_Parser_command_NotationSpec_binders_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
lean::dec(x_66);
x_70 = lean::apply_1(x_67, x_52);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
else
{
obj* x_73; obj* x_74; obj* x_77; obj* x_78; 
lean::dec(x_39);
x_73 = l_Lean_Parser_command_NotationSpec_binder_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_52);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
else
{
obj* x_82; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_82 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_82;
}
}
}
}
}
}
}
else
{
obj* x_85; 
lean::dec(x_8);
lean::dec(x_17);
x_85 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1;
return x_85;
}
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_NotationSpec_binder_HasView;
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
x_14 = l_Lean_Parser_command_NotationSpec_transition;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_NotationSpec_binders_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_NotationSpec_transition;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
default:
{
obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_Parser_command_NotationSpec_argument_HasView;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::apply_1(x_34, x_30);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_1);
x_42 = l_Lean_Parser_command_NotationSpec_transition;
x_43 = l_Lean_Parser_Syntax_mkNode(x_42, x_41);
return x_43;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_transition_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_26; obj* x_28; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_0);
lean::dec(x_2);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_3);
lean::dec(x_3);
x_7 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
x_9 = l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens;
x_10 = l_Lean_Parser_tokens___rarg(x_9);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_0);
lean::dec(x_10);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_11);
lean::dec(x_11);
x_15 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_15, x_0);
lean::dec(x_15);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_17);
lean::dec(x_17);
x_21 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_19);
lean::dec(x_19);
lean::dec(x_7);
x_24 = l_Lean_Parser_tokens___rarg(x_21);
lean::dec(x_21);
x_26 = l_Lean_Parser_List_cons_tokens___rarg(x_24, x_0);
lean::dec(x_24);
x_28 = l_Lean_Parser_tokens___rarg(x_26);
lean::dec(x_26);
return x_28;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_0 = lean::mk_string("binder");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_3 = 0;
x_4 = lean::box(x_3);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::inc(x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Parser_command_NotationSpec_binder;
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::mk_string("binders");
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
x_16 = l_Lean_Parser_command_NotationSpec_binders;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser), 5, 0);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_4);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_command_NotationSpec_argument;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_7);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_12);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_nat_obj(0ul);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
x_31 = l_Lean_Parser_TermParserM_Monad;
x_32 = l_Lean_Parser_TermParserM_MonadExcept;
x_33 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_34 = l_Lean_Parser_TermParserM_Alternative;
x_35 = l_Lean_Parser_command_NotationSpec_transition;
x_36 = l_Lean_Parser_command_NotationSpec_transition_HasView;
x_37 = l_Lean_Parser_Combinators_node_view___rarg(x_31, x_32, x_33, x_34, x_35, x_30, x_36);
lean::dec(x_30);
return x_37;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = lean::mk_string("binder");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_precedence_Parser), 5, 0);
x_3 = 0;
x_4 = lean::box(x_3);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::inc(x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Parser_command_NotationSpec_binder;
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::mk_string("binders");
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
x_16 = l_Lean_Parser_command_NotationSpec_binders;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser), 5, 0);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_4);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_command_NotationSpec_argument;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_7);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_12);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_nat_obj(0ul);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
return x_30;
}
}
obj* l_Lean_Parser_command_NotationSpec_transition_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_transition;
x_6 = l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("rule");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_transition_HasView;
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
obj* _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_NotationSpec_transition_HasView;
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
x_33 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2;
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
x_18 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
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
x_25 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
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
x_41 = l_Lean_Parser_command_NotationSpec_transition_HasView;
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
x_51 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
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
x_57 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
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
x_73 = l_Lean_Parser_command_NotationSpec_transition_HasView;
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
x_83 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1;
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
obj* l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
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
x_13 = l_Lean_Parser_command_NotationSpec_rule;
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
x_19 = l_Lean_Parser_command_NotationSpec_transition_HasView;
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
x_29 = l_Lean_Parser_command_NotationSpec_rule;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_rule_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_0 = l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = lean::box(0);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_3);
lean::dec(x_3);
x_8 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_transition_Parser), 5, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_TermParserM_Monad;
x_9 = l_Lean_Parser_TermParserM_MonadExcept;
x_10 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_TermParserM_Alternative;
x_12 = l_Lean_Parser_command_NotationSpec_rule;
x_13 = l_Lean_Parser_command_NotationSpec_rule_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_transition_Parser), 5, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_Lean_Parser_command_NotationSpec_rule_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec_rule;
x_6 = l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("NotationSpec");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_command_NotationSpec_rule_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_NotationSpec_rule_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::box(3);
x_10 = l_Lean_Parser_Syntax_asNode___main(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
x_11 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
x_20 = l_List_map___main___rarg(x_19, x_16);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
x_12 = l_List_map___main___rarg(x_11, x_8);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_4;
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; 
lean::dec(x_3);
x_11 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5;
return x_11;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
switch (lean::obj_tag(x_14)) {
case 1:
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
if (lean::obj_tag(x_3) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_7);
x_21 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_3);
x_24 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
x_25 = l_List_map___main___rarg(x_24, x_7);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
case 3:
{
obj* x_29; 
lean::dec(x_7);
lean::dec(x_3);
x_29 = lean::box(0);
x_0 = x_29;
goto lbl_1;
}
default:
{
obj* x_33; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_14);
x_33 = lean::box(0);
x_0 = x_33;
goto lbl_1;
}
}
}
else
{
obj* x_37; 
lean::dec(x_12);
lean::dec(x_7);
lean::dec(x_3);
x_37 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_37;
}
}
}
lbl_1:
{
obj* x_39; 
lean::dec(x_0);
x_39 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_39;
}
}
}
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6;
return x_8;
}
else
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; 
x_15 = lean::box(3);
x_4 = x_12;
x_5 = x_15;
goto lbl_6;
}
else
{
obj* x_16; obj* x_18; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_12, 1);
lean::inc(x_18);
lean::dec(x_12);
x_4 = x_18;
x_5 = x_16;
goto lbl_6;
}
}
lbl_3:
{
obj* x_21; 
x_21 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; 
x_22 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
x_31 = l_List_map___main___rarg(x_30, x_27);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
lbl_6:
{
obj* x_33; obj* x_35; 
x_35 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_35) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_36; 
x_36 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_36;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::dec(x_4);
x_40 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4;
x_1 = x_40;
x_2 = x_37;
goto lbl_3;
}
}
else
{
obj* x_41; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
 x_43 = x_35;
} else {
 lean::inc(x_41);
 lean::dec(x_35);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::obj_tag(x_44) == 0)
{
lean::dec(x_43);
if (lean::obj_tag(x_4) == 0)
{
obj* x_48; 
x_48 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5;
return x_48;
}
else
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_4, 0);
lean::inc(x_49);
lean::dec(x_4);
x_52 = lean::box(0);
x_1 = x_52;
x_2 = x_49;
goto lbl_3;
}
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_44, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; 
x_55 = lean::cnstr_get(x_44, 0);
lean::inc(x_55);
lean::dec(x_44);
switch (lean::obj_tag(x_55)) {
case 1:
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_55, 0);
lean::inc(x_58);
lean::dec(x_55);
if (lean::is_scalar(x_43)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_43;
}
lean::cnstr_set(x_61, 0, x_58);
if (lean::obj_tag(x_4) == 0)
{
obj* x_62; obj* x_63; 
x_62 = lean::box(3);
x_63 = l_Lean_Parser_Syntax_asNode___main(x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; 
x_64 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1;
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
else
{
obj* x_66; obj* x_69; obj* x_72; obj* x_73; obj* x_74; 
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
lean::dec(x_63);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2;
x_73 = l_List_map___main___rarg(x_72, x_69);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_61);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
}
else
{
obj* x_75; 
x_75 = lean::cnstr_get(x_4, 0);
lean::inc(x_75);
lean::dec(x_4);
x_1 = x_61;
x_2 = x_75;
goto lbl_3;
}
}
case 3:
{
obj* x_79; 
lean::dec(x_43);
x_79 = lean::box(0);
x_33 = x_79;
goto lbl_34;
}
default:
{
obj* x_82; 
lean::dec(x_55);
lean::dec(x_43);
x_82 = lean::box(0);
x_33 = x_82;
goto lbl_34;
}
}
}
else
{
lean::dec(x_53);
lean::dec(x_43);
lean::dec(x_44);
if (lean::obj_tag(x_4) == 0)
{
obj* x_86; 
x_86 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_86;
}
else
{
obj* x_87; obj* x_90; 
x_87 = lean::cnstr_get(x_4, 0);
lean::inc(x_87);
lean::dec(x_4);
x_90 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4;
x_1 = x_90;
x_2 = x_87;
goto lbl_3;
}
}
}
}
lbl_34:
{
lean::dec(x_33);
if (lean::obj_tag(x_4) == 0)
{
obj* x_92; 
x_92 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3;
return x_92;
}
else
{
obj* x_93; obj* x_96; 
x_93 = lean::cnstr_get(x_4, 0);
lean::inc(x_93);
lean::dec(x_4);
x_96 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4;
x_1 = x_96;
x_2 = x_93;
goto lbl_3;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_NotationSpec_rule_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1;
x_7 = l_List_map___main___rarg(x_6, x_3);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
if (lean::obj_tag(x_1) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_Parser_command_NotationSpec;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_10);
x_21 = l_Lean_Parser_Syntax_mkNode(x_8, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_11);
x_23 = l_Lean_Parser_command_NotationSpec;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_NotationSpec_HasView_x_27;
return x_0;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0ul);
x_9 = lean::nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_19; obj* x_20; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_sub(x_2, x_10);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_5(x_0, x_3, x_4, x_5, x_6, x_7);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; 
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_12 = x_20;
x_13 = x_22;
goto lbl_14;
}
else
{
obj* x_25; obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_25 = lean::cnstr_get(x_19, 1);
lean::inc(x_25);
lean::dec(x_19);
x_28 = lean::cnstr_get(x_20, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_31 = x_20;
} else {
 lean::inc(x_28);
 lean::dec(x_20);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_28, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_28, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_28, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_28, 3);
lean::inc(x_38);
lean::dec(x_28);
x_41 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_38);
lean::dec(x_38);
lean::inc(x_1);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_1);
x_45 = lean::box(3);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = l_List_reverse___rarg(x_46);
x_48 = l_Lean_Parser_noKind;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_32);
lean::cnstr_set(x_51, 1, x_34);
lean::cnstr_set(x_51, 2, x_36);
lean::cnstr_set(x_51, 3, x_50);
if (x_30 == 0)
{
uint8 x_52; obj* x_53; obj* x_54; 
x_52 = 0;
if (lean::is_scalar(x_31)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_31;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_52);
x_54 = x_53;
x_12 = x_54;
x_13 = x_25;
goto lbl_14;
}
else
{
uint8 x_55; obj* x_56; obj* x_57; 
x_55 = 1;
if (lean::is_scalar(x_31)) {
 x_56 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_56 = x_31;
}
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set_scalar(x_56, sizeof(void*)*1, x_55);
x_57 = x_56;
x_12 = x_57;
x_13 = x_25;
goto lbl_14;
}
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_68; obj* x_70; 
x_58 = lean::cnstr_get(x_12, 0);
x_60 = lean::cnstr_get(x_12, 1);
x_62 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 lean::cnstr_set(x_12, 2, lean::box(0));
 x_64 = x_12;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_12);
 x_64 = lean::box(0);
}
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_58);
lean::cnstr_set(x_65, 1, x_1);
lean::inc(x_60);
lean::inc(x_65);
x_68 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3(x_0, x_65, x_11, x_3, x_4, x_5, x_60, x_13);
lean::dec(x_11);
x_70 = lean::cnstr_get(x_68, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_60);
lean::dec(x_65);
lean::dec(x_64);
x_75 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_77 = x_68;
} else {
 lean::inc(x_75);
 lean::dec(x_68);
 x_77 = lean::box(0);
}
x_78 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_70);
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
uint8 x_80; 
x_80 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_80 == 0)
{
obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_81 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_83 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_70, 0);
lean::inc(x_84);
lean::dec(x_70);
x_87 = l_List_reverse___rarg(x_65);
x_88 = l_Lean_Parser_noKind;
x_89 = l_Lean_Parser_Syntax_mkNode(x_88, x_87);
x_90 = lean::cnstr_get(x_84, 2);
lean::inc(x_90);
lean::dec(x_84);
x_93 = l_mjoin___rarg___closed__1;
x_94 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_94, 0, x_90);
lean::closure_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_64)) {
 x_96 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_96 = x_64;
}
lean::cnstr_set(x_96, 0, x_89);
lean::cnstr_set(x_96, 1, x_60);
lean::cnstr_set(x_96, 2, x_95);
x_97 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_96);
if (lean::is_scalar(x_83)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_83;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_81);
return x_98;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_60);
lean::dec(x_65);
lean::dec(x_64);
x_102 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_104 = x_68;
} else {
 lean::inc(x_102);
 lean::dec(x_68);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_70);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_102);
return x_106;
}
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_113 = lean::cnstr_get(x_12, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_116 = x_12;
} else {
 lean::inc(x_113);
 lean::dec(x_12);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_13);
return x_119;
}
}
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_1);
lean::dec(x_0);
x_122 = lean::box(0);
x_123 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_124 = l_mjoin___rarg___closed__1;
x_125 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_123, x_124, x_122, x_122, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_125;
}
}
}
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = lean::box(0);
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_6);
x_11 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3(x_0, x_7, x_9, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 x_17 = x_11;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_11);
 x_17 = lean::box(0);
}
x_18 = l_Lean_Parser_finishCommentBlock___closed__2;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_13);
if (lean::is_scalar(x_17)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_17;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_15);
return x_20;
}
}
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_4);
x_7 = l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
else
{
uint8 x_15; 
x_15 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_15 == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_16 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_18 = x_7;
} else {
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_mjoin___rarg___closed__1;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_22);
lean::closure_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_18)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_18;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_16);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_4);
x_32 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_34 = x_7;
} else {
 lean::inc(x_32);
 lean::dec(x_7);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_8);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_tokens___rarg(x_2);
x_4 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_0);
lean::dec(x_3);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_4);
lean::dec(x_4);
lean::dec(x_1);
x_9 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
return x_9;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_rule_Parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__1), 6, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_TermParserM_Monad;
x_10 = l_Lean_Parser_TermParserM_MonadExcept;
x_11 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_TermParserM_Alternative;
x_13 = l_Lean_Parser_command_NotationSpec;
x_14 = l_Lean_Parser_command_NotationSpec_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* _init_l_Lean_Parser_command_NotationSpec_Parser___closed__1() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___boxed), 1, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_rule_Parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens___spec__1), 6, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_NotationSpec_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_NotationSpec;
x_6 = l_Lean_Parser_command_NotationSpec_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_notation() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("notation");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_4;
goto lbl_1;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::box(0);
x_0 = x_12;
goto lbl_1;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_0 = x_22;
goto lbl_1;
}
case 3:
{
obj* x_24; 
lean::dec(x_7);
x_24 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_24;
goto lbl_1;
}
default:
{
obj* x_27; 
lean::dec(x_7);
lean::dec(x_15);
x_27 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_27;
goto lbl_1;
}
}
}
else
{
obj* x_31; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_7);
x_31 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_31;
goto lbl_1;
}
}
}
lbl_1:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::box(0);
x_33 = l_Lean_Parser_command_NotationSpec_HasView;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::box(3);
x_38 = lean::apply_1(x_34, x_37);
x_39 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_39, 0, x_0);
lean::cnstr_set(x_39, 1, x_32);
lean::cnstr_set(x_39, 2, x_38);
lean::cnstr_set(x_39, 3, x_32);
lean::cnstr_set(x_39, 4, x_37);
return x_39;
}
}
}
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2;
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
else
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_23) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_1 = x_20;
x_2 = x_24;
goto lbl_3;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_1 = x_27;
x_2 = x_25;
goto lbl_3;
}
}
else
{
obj* x_30; obj* x_33; obj* x_36; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_List_append___rarg(x_33, x_20);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(3);
x_1 = x_36;
x_2 = x_37;
goto lbl_3;
}
else
{
obj* x_38; obj* x_40; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_1 = x_40;
x_2 = x_38;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_43; obj* x_45; 
x_45 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_46;
goto lbl_44;
}
else
{
obj* x_47; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_set(x_45, 0, lean::box(0));
 x_49 = x_45;
} else {
 lean::inc(x_47);
 lean::dec(x_45);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; 
lean::dec(x_49);
x_54 = lean::box(0);
x_43 = x_54;
goto lbl_44;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; 
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_63; obj* x_64; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
lean::dec(x_57);
if (lean::is_scalar(x_49)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_49;
}
lean::cnstr_set(x_63, 0, x_60);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_43 = x_64;
goto lbl_44;
}
case 3:
{
obj* x_66; 
lean::dec(x_49);
x_66 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_66;
goto lbl_44;
}
default:
{
obj* x_69; 
lean::dec(x_49);
lean::dec(x_57);
x_69 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_69;
goto lbl_44;
}
}
}
else
{
obj* x_73; 
lean::dec(x_49);
lean::dec(x_55);
lean::dec(x_50);
x_73 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_73;
goto lbl_44;
}
}
}
lbl_44:
{
obj* x_74; obj* x_75; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_77; 
x_77 = lean::box(3);
x_74 = x_1;
x_75 = x_77;
goto lbl_76;
}
else
{
obj* x_78; obj* x_80; 
x_78 = lean::cnstr_get(x_1, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_1, 1);
lean::inc(x_80);
lean::dec(x_1);
x_74 = x_80;
x_75 = x_78;
goto lbl_76;
}
lbl_76:
{
obj* x_83; 
switch (lean::obj_tag(x_75)) {
case 0:
{
obj* x_85; obj* x_88; 
x_85 = lean::cnstr_get(x_75, 0);
lean::inc(x_85);
lean::dec(x_75);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_85);
x_83 = x_88;
goto lbl_84;
}
case 3:
{
obj* x_89; 
x_89 = lean::box(0);
x_83 = x_89;
goto lbl_84;
}
default:
{
obj* x_91; 
lean::dec(x_75);
x_91 = lean::box(0);
x_83 = x_91;
goto lbl_84;
}
}
lbl_84:
{
obj* x_92; obj* x_93; 
if (lean::obj_tag(x_74) == 0)
{
obj* x_95; 
x_95 = lean::box(3);
x_92 = x_74;
x_93 = x_95;
goto lbl_94;
}
else
{
obj* x_96; obj* x_98; 
x_96 = lean::cnstr_get(x_74, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_74, 1);
lean::inc(x_98);
lean::dec(x_74);
x_92 = x_98;
x_93 = x_96;
goto lbl_94;
}
lbl_94:
{
obj* x_101; obj* x_102; obj* x_105; 
x_101 = l_Lean_Parser_command_NotationSpec_HasView;
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
lean::dec(x_101);
x_105 = lean::apply_1(x_102, x_93);
if (lean::obj_tag(x_92) == 0)
{
obj* x_106; 
x_106 = lean::box(0);
if (lean::obj_tag(x_92) == 0)
{
obj* x_107; obj* x_108; 
x_107 = lean::box(3);
x_108 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_108, 0, x_43);
lean::cnstr_set(x_108, 1, x_83);
lean::cnstr_set(x_108, 2, x_105);
lean::cnstr_set(x_108, 3, x_106);
lean::cnstr_set(x_108, 4, x_107);
return x_108;
}
else
{
obj* x_109; obj* x_112; 
x_109 = lean::cnstr_get(x_92, 0);
lean::inc(x_109);
lean::dec(x_92);
x_112 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_112, 0, x_43);
lean::cnstr_set(x_112, 1, x_83);
lean::cnstr_set(x_112, 2, x_105);
lean::cnstr_set(x_112, 3, x_106);
lean::cnstr_set(x_112, 4, x_109);
return x_112;
}
}
else
{
obj* x_113; 
x_113 = lean::cnstr_get(x_92, 0);
lean::inc(x_113);
switch (lean::obj_tag(x_113)) {
case 0:
{
obj* x_115; obj* x_118; obj* x_121; 
x_115 = lean::cnstr_get(x_92, 1);
lean::inc(x_115);
lean::dec(x_92);
x_118 = lean::cnstr_get(x_113, 0);
lean::inc(x_118);
lean::dec(x_113);
x_121 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_121, 0, x_118);
if (lean::obj_tag(x_115) == 0)
{
obj* x_122; obj* x_123; 
x_122 = lean::box(3);
x_123 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_123, 0, x_43);
lean::cnstr_set(x_123, 1, x_83);
lean::cnstr_set(x_123, 2, x_105);
lean::cnstr_set(x_123, 3, x_121);
lean::cnstr_set(x_123, 4, x_122);
return x_123;
}
else
{
obj* x_124; obj* x_127; 
x_124 = lean::cnstr_get(x_115, 0);
lean::inc(x_124);
lean::dec(x_115);
x_127 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_127, 0, x_43);
lean::cnstr_set(x_127, 1, x_83);
lean::cnstr_set(x_127, 2, x_105);
lean::cnstr_set(x_127, 3, x_121);
lean::cnstr_set(x_127, 4, x_124);
return x_127;
}
}
case 3:
{
obj* x_128; obj* x_131; 
x_128 = lean::cnstr_get(x_92, 1);
lean::inc(x_128);
lean::dec(x_92);
x_131 = lean::box(0);
if (lean::obj_tag(x_128) == 0)
{
obj* x_132; obj* x_133; 
x_132 = lean::box(3);
x_133 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_133, 0, x_43);
lean::cnstr_set(x_133, 1, x_83);
lean::cnstr_set(x_133, 2, x_105);
lean::cnstr_set(x_133, 3, x_131);
lean::cnstr_set(x_133, 4, x_132);
return x_133;
}
else
{
obj* x_134; obj* x_137; 
x_134 = lean::cnstr_get(x_128, 0);
lean::inc(x_134);
lean::dec(x_128);
x_137 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_137, 0, x_43);
lean::cnstr_set(x_137, 1, x_83);
lean::cnstr_set(x_137, 2, x_105);
lean::cnstr_set(x_137, 3, x_131);
lean::cnstr_set(x_137, 4, x_134);
return x_137;
}
}
default:
{
obj* x_139; obj* x_142; 
lean::dec(x_113);
x_139 = lean::cnstr_get(x_92, 1);
lean::inc(x_139);
lean::dec(x_92);
x_142 = lean::box(0);
if (lean::obj_tag(x_139) == 0)
{
obj* x_143; obj* x_144; 
x_143 = lean::box(3);
x_144 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_144, 0, x_43);
lean::cnstr_set(x_144, 1, x_83);
lean::cnstr_set(x_144, 2, x_105);
lean::cnstr_set(x_144, 3, x_142);
lean::cnstr_set(x_144, 4, x_143);
return x_144;
}
else
{
obj* x_145; obj* x_148; 
x_145 = lean::cnstr_get(x_139, 0);
lean::inc(x_145);
lean::dec(x_139);
x_148 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_148, 0, x_43);
lean::cnstr_set(x_148, 1, x_83);
lean::cnstr_set(x_148, 2, x_105);
lean::cnstr_set(x_148, 3, x_142);
lean::cnstr_set(x_148, 4, x_145);
return x_148;
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1() {
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
x_5 = l_Lean_Parser_noKind;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_command_NotationSpec_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::apply_1(x_14, x_5);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_12);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_24; 
x_24 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_19 = x_24;
goto lbl_20;
}
else
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
x_28 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_21 = x_28;
x_22 = x_25;
goto lbl_23;
}
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
lean::dec(x_1);
if (lean::obj_tag(x_29) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1;
x_19 = x_32;
goto lbl_20;
}
else
{
obj* x_33; obj* x_36; 
x_33 = lean::cnstr_get(x_3, 0);
lean::inc(x_33);
lean::dec(x_3);
x_36 = l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1;
x_21 = x_36;
x_22 = x_33;
goto lbl_23;
}
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_39 = x_29;
} else {
 lean::inc(x_37);
 lean::dec(x_29);
 x_39 = lean::box(0);
}
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
if (lean::is_scalar(x_39)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_39;
}
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::box(3);
x_43 = l_Option_getOrElse___main___rarg(x_41, x_42);
lean::dec(x_41);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_12);
x_46 = l_Lean_Parser_noKind;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
if (lean::obj_tag(x_3) == 0)
{
x_19 = x_47;
goto lbl_20;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_3, 0);
lean::inc(x_48);
lean::dec(x_3);
x_21 = x_47;
x_22 = x_48;
goto lbl_23;
}
}
}
lbl_20:
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_19);
lean::cnstr_set(x_52, 1, x_51);
x_53 = l_Lean_Parser_noKind;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
if (lean::obj_tag(x_7) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_18);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_17);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_Parser_command_notation;
x_60 = l_Lean_Parser_Syntax_mkNode(x_59, x_58);
return x_60;
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_61 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_63 = x_7;
} else {
 lean::inc(x_61);
 lean::dec(x_7);
 x_63 = lean::box(0);
}
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::box(3);
x_67 = l_Option_getOrElse___main___rarg(x_65, x_66);
lean::dec(x_65);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_18);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_17);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_54);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_Lean_Parser_command_notation;
x_73 = l_Lean_Parser_Syntax_mkNode(x_72, x_71);
return x_73;
}
}
lbl_23:
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_74 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_74, 0, x_22);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::box(3);
x_77 = l_Option_getOrElse___main___rarg(x_75, x_76);
lean::dec(x_75);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_12);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_21);
lean::cnstr_set(x_80, 1, x_79);
x_81 = l_Lean_Parser_noKind;
x_82 = l_Lean_Parser_Syntax_mkNode(x_81, x_80);
if (lean::obj_tag(x_7) == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_18);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_17);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_82);
lean::cnstr_set(x_86, 1, x_85);
x_87 = l_Lean_Parser_command_notation;
x_88 = l_Lean_Parser_Syntax_mkNode(x_87, x_86);
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_89 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_91 = x_7;
} else {
 lean::inc(x_89);
 lean::dec(x_7);
 x_91 = lean::box(0);
}
x_92 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
if (lean::is_scalar(x_91)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_91;
}
lean::cnstr_set(x_93, 0, x_92);
x_94 = l_Option_getOrElse___main___rarg(x_93, x_76);
lean::dec(x_93);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_18);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_17);
lean::cnstr_set(x_97, 1, x_96);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_82);
lean::cnstr_set(x_98, 1, x_97);
x_99 = l_Lean_Parser_command_notation;
x_100 = l_Lean_Parser_Syntax_mkNode(x_99, x_98);
return x_100;
}
}
}
}
obj* _init_l_Lean_Parser_command_notation_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notation_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notation_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_notation_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_notation_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_33; 
x_0 = lean::mk_string("local ");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_6 = lean::mk_string("notation");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_1);
lean::dec(x_6);
x_9 = lean::box(0);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_9);
lean::dec(x_7);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
x_15 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
x_17 = l_Lean_Parser_tokens___rarg(x_15);
lean::dec(x_15);
x_19 = lean::mk_string(":=");
x_20 = l_Lean_Parser_symbol_tokens___rarg(x_19, x_1);
lean::dec(x_19);
x_22 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_9);
x_24 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_23);
lean::dec(x_23);
lean::dec(x_20);
x_27 = l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens;
x_28 = l_Lean_Parser_List_cons_tokens___rarg(x_27, x_24);
lean::dec(x_24);
x_30 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_28);
lean::dec(x_28);
lean::dec(x_17);
x_33 = l_Lean_Parser_tokens___rarg(x_30);
lean::dec(x_30);
return x_33;
}
}
obj* _init_l_Lean_Parser_command_notation_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_0 = lean::mk_string("local ");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::mk_string("notation");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_14, 0, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_15, 0, x_11);
lean::closure_set(x_15, 1, x_5);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(":=");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_24, 0, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_25, 0, x_21);
lean::closure_set(x_25, 1, x_5);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_26, 0, x_5);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_16);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_Parser), 5, 0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_19);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_TermParserM_Monad;
x_33 = l_Lean_Parser_TermParserM_MonadExcept;
x_34 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_35 = l_Lean_Parser_TermParserM_Alternative;
x_36 = l_Lean_Parser_command_notation;
x_37 = l_Lean_Parser_command_notation_HasView;
x_38 = l_Lean_Parser_Combinators_node_view___rarg(x_32, x_33, x_34, x_35, x_36, x_31, x_37);
lean::dec(x_31);
return x_38;
}
}
obj* _init_l_Lean_Parser_command_notation_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_0 = lean::mk_string("local ");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::mk_string("notation");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_14, 0, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_15, 0, x_11);
lean::closure_set(x_15, 1, x_5);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::mk_string(":=");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_24, 0, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_25, 0, x_21);
lean::closure_set(x_25, 1, x_5);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_26, 0, x_5);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_16);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_Parser), 5, 0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_19);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
obj* l_Lean_Parser_command_notation_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_notation;
x_6 = l_Lean_Parser_command_notation_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("reserveNotation");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_NotationSpec_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1;
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2;
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
else
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_23) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_1 = x_20;
x_2 = x_24;
goto lbl_3;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_1 = x_27;
x_2 = x_25;
goto lbl_3;
}
}
else
{
obj* x_30; obj* x_33; obj* x_36; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_List_append___rarg(x_33, x_20);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(3);
x_1 = x_36;
x_2 = x_37;
goto lbl_3;
}
else
{
obj* x_38; obj* x_40; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_1 = x_40;
x_2 = x_38;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_43; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_2, 0);
lean::inc(x_45);
lean::dec(x_2);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_45);
x_43 = x_48;
goto lbl_44;
}
case 3:
{
obj* x_49; 
x_49 = lean::box(0);
x_43 = x_49;
goto lbl_44;
}
default:
{
obj* x_51; 
lean::dec(x_2);
x_51 = lean::box(0);
x_43 = x_51;
goto lbl_44;
}
}
lbl_44:
{
obj* x_52; obj* x_53; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_55; 
x_55 = lean::box(3);
x_52 = x_1;
x_53 = x_55;
goto lbl_54;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_1, 1);
lean::inc(x_58);
lean::dec(x_1);
x_52 = x_58;
x_53 = x_56;
goto lbl_54;
}
lbl_54:
{
switch (lean::obj_tag(x_53)) {
case 0:
{
obj* x_61; obj* x_64; 
x_61 = lean::cnstr_get(x_53, 0);
lean::inc(x_61);
lean::dec(x_53);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_61);
if (lean::obj_tag(x_52) == 0)
{
obj* x_65; obj* x_66; 
x_65 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1;
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_43);
lean::cnstr_set(x_66, 1, x_64);
lean::cnstr_set(x_66, 2, x_65);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_71; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_52, 0);
lean::inc(x_67);
lean::dec(x_52);
x_70 = l_Lean_Parser_command_NotationSpec_HasView;
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
lean::dec(x_70);
x_74 = lean::apply_1(x_71, x_67);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_43);
lean::cnstr_set(x_75, 1, x_64);
lean::cnstr_set(x_75, 2, x_74);
return x_75;
}
}
case 3:
{
obj* x_76; 
x_76 = lean::box(0);
if (lean::obj_tag(x_52) == 0)
{
obj* x_77; obj* x_78; 
x_77 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1;
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_43);
lean::cnstr_set(x_78, 1, x_76);
lean::cnstr_set(x_78, 2, x_77);
return x_78;
}
else
{
obj* x_79; obj* x_82; obj* x_83; obj* x_86; obj* x_87; 
x_79 = lean::cnstr_get(x_52, 0);
lean::inc(x_79);
lean::dec(x_52);
x_82 = l_Lean_Parser_command_NotationSpec_HasView;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
lean::dec(x_82);
x_86 = lean::apply_1(x_83, x_79);
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_43);
lean::cnstr_set(x_87, 1, x_76);
lean::cnstr_set(x_87, 2, x_86);
return x_87;
}
}
default:
{
obj* x_89; 
lean::dec(x_53);
x_89 = lean::box(0);
if (lean::obj_tag(x_52) == 0)
{
obj* x_90; obj* x_91; 
x_90 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1;
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_43);
lean::cnstr_set(x_91, 1, x_89);
lean::cnstr_set(x_91, 2, x_90);
return x_91;
}
else
{
obj* x_92; obj* x_95; obj* x_96; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_52, 0);
lean::inc(x_92);
lean::dec(x_52);
x_95 = l_Lean_Parser_command_NotationSpec_HasView;
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
lean::dec(x_95);
x_99 = lean::apply_1(x_96, x_92);
x_100 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_100, 0, x_43);
lean::cnstr_set(x_100, 1, x_89);
lean::cnstr_set(x_100, 2, x_99);
return x_100;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
obj* l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_command_NotationSpec_HasView;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_13 = lean::apply_1(x_10, x_5);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_command_reserveNotation;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_19 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_21 = x_3;
} else {
 lean::inc(x_19);
 lean::dec(x_3);
 x_21 = lean::box(0);
}
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::box(3);
x_25 = l_Option_getOrElse___main___rarg(x_23, x_24);
lean::dec(x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_8);
x_28 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = l_Lean_Parser_noKind;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_14);
x_33 = l_Lean_Parser_command_reserveNotation;
x_34 = l_Lean_Parser_Syntax_mkNode(x_33, x_32);
return x_34;
}
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_37 = x_1;
} else {
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_35);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::box(3);
x_41 = l_Option_getOrElse___main___rarg(x_39, x_40);
lean::dec(x_39);
if (lean::obj_tag(x_3) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_43 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_noKind;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_14);
x_48 = l_Lean_Parser_command_reserveNotation;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_50 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_52 = x_3;
} else {
 lean::inc(x_50);
 lean::dec(x_3);
 x_52 = lean::box(0);
}
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
x_55 = l_Option_getOrElse___main___rarg(x_54, x_40);
lean::dec(x_54);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_8);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_41);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_Parser_noKind;
x_60 = l_Lean_Parser_Syntax_mkNode(x_59, x_58);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_14);
x_62 = l_Lean_Parser_command_reserveNotation;
x_63 = l_Lean_Parser_Syntax_mkNode(x_62, x_61);
return x_63;
}
}
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_reserveNotation_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; 
x_0 = lean::mk_string("reserve");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string("notation");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_7);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
x_13 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_15 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
x_17 = l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens;
x_18 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_7);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_15, x_18);
lean::dec(x_18);
lean::dec(x_15);
x_22 = l_Lean_Parser_tokens___rarg(x_19);
lean::dec(x_19);
return x_22;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string("reserve");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("notation");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_Parser), 5, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_Lean_Parser_TermParserM_Monad;
x_21 = l_Lean_Parser_TermParserM_MonadExcept;
x_22 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_23 = l_Lean_Parser_TermParserM_Alternative;
x_24 = l_Lean_Parser_command_reserveNotation;
x_25 = l_Lean_Parser_command_reserveNotation_HasView;
x_26 = l_Lean_Parser_Combinators_node_view___rarg(x_20, x_21, x_22, x_23, x_24, x_19, x_25);
lean::dec(x_19);
return x_26;
}
}
obj* _init_l_Lean_Parser_command_reserveNotation_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::mk_string("reserve");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("notation");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_Parser), 5, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
obj* l_Lean_Parser_command_reserveNotation_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_reserveNotation;
x_6 = l_Lean_Parser_command_reserveNotation_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("mixfix");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("mixfix");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
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
x_11 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
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
x_23 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
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
x_31 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
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
x_50 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
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
x_59 = lean::mk_nat_obj(0ul);
x_60 = lean::nat_dec_eq(x_41, x_59);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::mk_nat_obj(1ul);
x_62 = lean::nat_dec_eq(x_41, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(2ul);
x_64 = lean::nat_dec_eq(x_41, x_63);
if (x_64 == 0)
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(3ul);
x_66 = lean::nat_dec_eq(x_41, x_65);
lean::dec(x_41);
if (x_66 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_68; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_56, 0);
lean::inc(x_68);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_26;
}
lean::cnstr_set(x_71, 0, x_68);
x_72 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
case 3:
{
obj* x_74; 
lean::dec(x_26);
x_74 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1;
return x_74;
}
default:
{
obj* x_77; 
lean::dec(x_56);
lean::dec(x_26);
x_77 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1;
return x_77;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_78; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_56, 0);
lean::inc(x_78);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_26;
}
lean::cnstr_set(x_81, 0, x_78);
x_82 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
case 3:
{
obj* x_84; 
lean::dec(x_26);
x_84 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2;
return x_84;
}
default:
{
obj* x_87; 
lean::dec(x_56);
lean::dec(x_26);
x_87 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2;
return x_87;
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
obj* x_89; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_56, 0);
lean::inc(x_89);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_26;
}
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
case 3:
{
obj* x_95; 
lean::dec(x_26);
x_95 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3;
return x_95;
}
default:
{
obj* x_98; 
lean::dec(x_56);
lean::dec(x_26);
x_98 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3;
return x_98;
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
obj* x_100; obj* x_103; obj* x_104; 
x_100 = lean::cnstr_get(x_56, 0);
lean::inc(x_100);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_26;
}
lean::cnstr_set(x_103, 0, x_100);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
case 3:
{
obj* x_106; 
lean::dec(x_26);
x_106 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4;
return x_106;
}
default:
{
obj* x_109; 
lean::dec(x_56);
lean::dec(x_26);
x_109 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4;
return x_109;
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
obj* x_111; obj* x_114; obj* x_115; 
x_111 = lean::cnstr_get(x_56, 0);
lean::inc(x_111);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_114 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_114 = x_26;
}
lean::cnstr_set(x_114, 0, x_111);
x_115 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_115, 0, x_114);
return x_115;
}
case 3:
{
obj* x_117; 
lean::dec(x_26);
x_117 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5;
return x_117;
}
default:
{
obj* x_120; 
lean::dec(x_56);
lean::dec(x_26);
x_120 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5;
return x_120;
}
}
}
}
else
{
obj* x_125; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_125 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
return x_125;
}
}
}
}
}
}
}
else
{
obj* x_128; 
lean::dec(x_8);
lean::dec(x_17);
x_128 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6;
return x_128;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
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
x_10 = l_Lean_Parser_command_mixfix_kind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
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
x_10 = l_Lean_Parser_command_mixfix_kind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2ul);
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
x_10 = l_Lean_Parser_command_mixfix_kind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(3ul);
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
x_10 = l_Lean_Parser_command_mixfix_kind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(4ul);
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
x_10 = l_Lean_Parser_command_mixfix_kind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(4ul);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1;
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
x_18 = l_Lean_Parser_command_mixfix_kind;
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
x_23 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2;
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
x_36 = l_Lean_Parser_command_mixfix_kind;
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
x_41 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3;
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
x_54 = l_Lean_Parser_command_mixfix_kind;
x_55 = l_Lean_Parser_Syntax_mkNode(x_54, x_53);
return x_55;
}
}
case 3:
{
obj* x_56; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
lean::dec(x_0);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; 
x_59 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4;
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
x_72 = l_Lean_Parser_command_mixfix_kind;
x_73 = l_Lean_Parser_Syntax_mkNode(x_72, x_71);
return x_73;
}
}
default:
{
obj* x_74; 
x_74 = lean::cnstr_get(x_0, 0);
lean::inc(x_74);
lean::dec(x_0);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; 
x_77 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5;
return x_77;
}
else
{
obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_78 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_80 = x_74;
} else {
 lean::inc(x_78);
 lean::dec(x_74);
 x_80 = lean::box(0);
}
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_80)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_80;
}
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::box(3);
x_84 = l_Option_getOrElse___main___rarg(x_82, x_83);
lean::dec(x_82);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_1);
x_87 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6;
x_88 = l_Lean_Parser_Syntax_mkNode(x_87, x_86);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_1);
x_90 = l_Lean_Parser_command_mixfix_kind;
x_91 = l_Lean_Parser_Syntax_mkNode(x_90, x_89);
return x_91;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_mixfix_kind_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_31; obj* x_33; obj* x_35; 
x_0 = lean::mk_string("prefix");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string("infix");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::mk_string("infixl");
x_8 = l_Lean_Parser_symbol_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_10 = lean::mk_string("infixr");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_1);
lean::dec(x_10);
x_13 = lean::mk_string("postfix");
x_14 = l_Lean_Parser_symbol_tokens___rarg(x_13, x_1);
lean::dec(x_13);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_16);
lean::dec(x_14);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_19);
lean::dec(x_19);
lean::dec(x_8);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_25);
lean::dec(x_25);
lean::dec(x_2);
x_31 = l_Lean_Parser_tokens___rarg(x_28);
lean::dec(x_28);
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_31, x_16);
lean::dec(x_31);
x_35 = l_Lean_Parser_tokens___rarg(x_33);
lean::dec(x_33);
return x_35;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_0 = lean::mk_string("prefix");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("infix");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::mk_string("infixl");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_5);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::mk_string("infixr");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_23, 0, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_5);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::mk_string("postfix");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_18);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_5);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
x_39 = l_Lean_Parser_TermParserM_Monad;
x_40 = l_Lean_Parser_TermParserM_MonadExcept;
x_41 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_42 = l_Lean_Parser_TermParserM_Alternative;
x_43 = l_Lean_Parser_command_mixfix_kind;
x_44 = l_Lean_Parser_command_mixfix_kind_HasView;
x_45 = l_Lean_Parser_Combinators_node_view___rarg(x_39, x_40, x_41, x_42, x_43, x_38, x_44);
lean::dec(x_38);
return x_45;
}
}
obj* _init_l_Lean_Parser_command_mixfix_kind_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_0 = lean::mk_string("prefix");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("infix");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::mk_string("infixl");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_5);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::mk_string("infixr");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_23, 0, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_5);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::mk_string("postfix");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_18);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_5);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
}
obj* l_Lean_Parser_command_mixfix_kind_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_mixfix_kind;
x_6 = l_Lean_Parser_command_mixfix_kind_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_mixfix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("mixfix");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_4;
goto lbl_1;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::box(0);
x_0 = x_12;
goto lbl_1;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_0 = x_22;
goto lbl_1;
}
case 3:
{
obj* x_24; 
lean::dec(x_7);
x_24 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_24;
goto lbl_1;
}
default:
{
obj* x_27; 
lean::dec(x_7);
lean::dec(x_15);
x_27 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_27;
goto lbl_1;
}
}
}
else
{
obj* x_31; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_7);
x_31 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_31;
goto lbl_1;
}
}
}
lbl_1:
{
obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; 
x_32 = l_Lean_Parser_command_mixfix_kind_HasView;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::box(3);
x_37 = lean::apply_1(x_33, x_36);
x_38 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_36);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_44, 0, x_0);
lean::cnstr_set(x_44, 1, x_37);
lean::cnstr_set(x_44, 2, x_42);
lean::cnstr_set(x_44, 3, x_43);
lean::cnstr_set(x_44, 4, x_36);
return x_44;
}
}
}
obj* l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1;
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
else
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_23) == 0)
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_1 = x_20;
x_2 = x_24;
goto lbl_3;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_1 = x_27;
x_2 = x_25;
goto lbl_3;
}
}
else
{
obj* x_30; obj* x_33; obj* x_36; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_List_append___rarg(x_33, x_20);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(3);
x_1 = x_36;
x_2 = x_37;
goto lbl_3;
}
else
{
obj* x_38; obj* x_40; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_1 = x_40;
x_2 = x_38;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_43; obj* x_45; 
x_45 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_46;
goto lbl_44;
}
else
{
obj* x_47; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_set(x_45, 0, lean::box(0));
 x_49 = x_45;
} else {
 lean::inc(x_47);
 lean::dec(x_45);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; 
lean::dec(x_49);
x_54 = lean::box(0);
x_43 = x_54;
goto lbl_44;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; 
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_60; obj* x_63; obj* x_64; 
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
lean::dec(x_57);
if (lean::is_scalar(x_49)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_49;
}
lean::cnstr_set(x_63, 0, x_60);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_43 = x_64;
goto lbl_44;
}
case 3:
{
obj* x_66; 
lean::dec(x_49);
x_66 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_66;
goto lbl_44;
}
default:
{
obj* x_69; 
lean::dec(x_49);
lean::dec(x_57);
x_69 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_69;
goto lbl_44;
}
}
}
else
{
obj* x_73; 
lean::dec(x_49);
lean::dec(x_55);
lean::dec(x_50);
x_73 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_43 = x_73;
goto lbl_44;
}
}
}
lbl_44:
{
obj* x_74; obj* x_75; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_77; 
x_77 = lean::box(3);
x_74 = x_1;
x_75 = x_77;
goto lbl_76;
}
else
{
obj* x_78; obj* x_80; 
x_78 = lean::cnstr_get(x_1, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_1, 1);
lean::inc(x_80);
lean::dec(x_1);
x_74 = x_80;
x_75 = x_78;
goto lbl_76;
}
lbl_76:
{
obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; 
x_83 = l_Lean_Parser_command_mixfix_kind_HasView;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
lean::dec(x_83);
x_87 = lean::apply_1(x_84, x_75);
if (lean::obj_tag(x_74) == 0)
{
obj* x_91; 
x_91 = lean::box(3);
x_88 = x_74;
x_89 = x_91;
goto lbl_90;
}
else
{
obj* x_92; obj* x_94; 
x_92 = lean::cnstr_get(x_74, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_74, 1);
lean::inc(x_94);
lean::dec(x_74);
x_88 = x_94;
x_89 = x_92;
goto lbl_90;
}
lbl_90:
{
obj* x_97; obj* x_98; obj* x_101; 
x_97 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView;
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
lean::dec(x_97);
x_101 = lean::apply_1(x_98, x_89);
if (lean::obj_tag(x_88) == 0)
{
obj* x_102; 
x_102 = lean::box(0);
if (lean::obj_tag(x_88) == 0)
{
obj* x_103; obj* x_104; 
x_103 = lean::box(3);
x_104 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_104, 0, x_43);
lean::cnstr_set(x_104, 1, x_87);
lean::cnstr_set(x_104, 2, x_101);
lean::cnstr_set(x_104, 3, x_102);
lean::cnstr_set(x_104, 4, x_103);
return x_104;
}
else
{
obj* x_105; obj* x_108; 
x_105 = lean::cnstr_get(x_88, 0);
lean::inc(x_105);
lean::dec(x_88);
x_108 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_108, 0, x_43);
lean::cnstr_set(x_108, 1, x_87);
lean::cnstr_set(x_108, 2, x_101);
lean::cnstr_set(x_108, 3, x_102);
lean::cnstr_set(x_108, 4, x_105);
return x_108;
}
}
else
{
obj* x_109; 
x_109 = lean::cnstr_get(x_88, 0);
lean::inc(x_109);
switch (lean::obj_tag(x_109)) {
case 0:
{
obj* x_111; obj* x_114; obj* x_117; 
x_111 = lean::cnstr_get(x_88, 1);
lean::inc(x_111);
lean::dec(x_88);
x_114 = lean::cnstr_get(x_109, 0);
lean::inc(x_114);
lean::dec(x_109);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_114);
if (lean::obj_tag(x_111) == 0)
{
obj* x_118; obj* x_119; 
x_118 = lean::box(3);
x_119 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_119, 0, x_43);
lean::cnstr_set(x_119, 1, x_87);
lean::cnstr_set(x_119, 2, x_101);
lean::cnstr_set(x_119, 3, x_117);
lean::cnstr_set(x_119, 4, x_118);
return x_119;
}
else
{
obj* x_120; obj* x_123; 
x_120 = lean::cnstr_get(x_111, 0);
lean::inc(x_120);
lean::dec(x_111);
x_123 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_123, 0, x_43);
lean::cnstr_set(x_123, 1, x_87);
lean::cnstr_set(x_123, 2, x_101);
lean::cnstr_set(x_123, 3, x_117);
lean::cnstr_set(x_123, 4, x_120);
return x_123;
}
}
case 3:
{
obj* x_124; obj* x_127; 
x_124 = lean::cnstr_get(x_88, 1);
lean::inc(x_124);
lean::dec(x_88);
x_127 = lean::box(0);
if (lean::obj_tag(x_124) == 0)
{
obj* x_128; obj* x_129; 
x_128 = lean::box(3);
x_129 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_129, 0, x_43);
lean::cnstr_set(x_129, 1, x_87);
lean::cnstr_set(x_129, 2, x_101);
lean::cnstr_set(x_129, 3, x_127);
lean::cnstr_set(x_129, 4, x_128);
return x_129;
}
else
{
obj* x_130; obj* x_133; 
x_130 = lean::cnstr_get(x_124, 0);
lean::inc(x_130);
lean::dec(x_124);
x_133 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_133, 0, x_43);
lean::cnstr_set(x_133, 1, x_87);
lean::cnstr_set(x_133, 2, x_101);
lean::cnstr_set(x_133, 3, x_127);
lean::cnstr_set(x_133, 4, x_130);
return x_133;
}
}
default:
{
obj* x_135; obj* x_138; 
lean::dec(x_109);
x_135 = lean::cnstr_get(x_88, 1);
lean::inc(x_135);
lean::dec(x_88);
x_138 = lean::box(0);
if (lean::obj_tag(x_135) == 0)
{
obj* x_139; obj* x_140; 
x_139 = lean::box(3);
x_140 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_140, 0, x_43);
lean::cnstr_set(x_140, 1, x_87);
lean::cnstr_set(x_140, 2, x_101);
lean::cnstr_set(x_140, 3, x_138);
lean::cnstr_set(x_140, 4, x_139);
return x_140;
}
else
{
obj* x_141; obj* x_144; 
x_141 = lean::cnstr_get(x_135, 0);
lean::inc(x_141);
lean::dec(x_135);
x_144 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_144, 0, x_43);
lean::cnstr_set(x_144, 1, x_87);
lean::cnstr_set(x_144, 2, x_101);
lean::cnstr_set(x_144, 3, x_138);
lean::cnstr_set(x_144, 4, x_141);
return x_144;
}
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_mixfix_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Parser_command_mixfix_kind_HasView;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_16 = lean::apply_1(x_13, x_3);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_5);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_9);
lean::cnstr_set(x_24, 1, x_17);
if (lean::obj_tag(x_1) == 0)
{
obj* x_27; 
x_27 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_25 = x_27;
goto lbl_26;
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; 
x_31 = l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1;
x_25 = x_31;
goto lbl_26;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
x_32 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_34 = x_28;
} else {
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::box(3);
x_38 = l_Option_getOrElse___main___rarg(x_36, x_37);
lean::dec(x_36);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_17);
x_41 = l_Lean_Parser_noKind;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
x_25 = x_42;
goto lbl_26;
}
}
lbl_26:
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_25);
lean::cnstr_set(x_43, 1, x_18);
x_44 = l_Lean_Parser_noKind;
x_45 = l_Lean_Parser_Syntax_mkNode(x_44, x_43);
if (lean::obj_tag(x_7) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_24);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_23);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_command_mixfix;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_52 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_54 = x_7;
} else {
 lean::inc(x_52);
 lean::dec(x_7);
 x_54 = lean::box(0);
}
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_52);
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::box(3);
x_58 = l_Option_getOrElse___main___rarg(x_56, x_57);
lean::dec(x_56);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_24);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_23);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_45);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_Lean_Parser_command_mixfix;
x_64 = l_Lean_Parser_Syntax_mkNode(x_63, x_62);
return x_64;
}
}
}
}
obj* _init_l_Lean_Parser_command_mixfix_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_mixfix_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_mixfix_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; obj* x_30; 
x_0 = lean::mk_string("local ");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
x_12 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
x_14 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
x_16 = lean::mk_string(":=");
x_17 = l_Lean_Parser_symbol_tokens___rarg(x_16, x_1);
lean::dec(x_16);
x_19 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1;
x_20 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_6);
x_21 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_20);
lean::dec(x_20);
lean::dec(x_17);
x_24 = l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens;
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_24, x_21);
lean::dec(x_21);
x_27 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_25);
lean::dec(x_25);
lean::dec(x_14);
x_30 = l_Lean_Parser_tokens___rarg(x_27);
lean::dec(x_27);
return x_30;
}
}
obj* _init_l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_0 = lean::mk_string("local ");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_Parser), 5, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_string(":=");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_21, 0, x_5);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser), 5, 0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_TermParserM_Monad;
x_28 = l_Lean_Parser_TermParserM_MonadExcept;
x_29 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_30 = l_Lean_Parser_TermParserM_Alternative;
x_31 = l_Lean_Parser_command_mixfix;
x_32 = l_Lean_Parser_command_mixfix_HasView;
x_33 = l_Lean_Parser_Combinators_node_view___rarg(x_27, x_28, x_29, x_30, x_31, x_26, x_32);
lean::dec(x_26);
return x_33;
}
}
obj* _init_l_Lean_Parser_command_mixfix_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string("local ");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__7___boxed), 7, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_Parser), 5, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_string(":=");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_21, 0, x_5);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser), 5, 0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* l_Lean_Parser_command_mixfix_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_mixfix;
x_6 = l_Lean_Parser_command_mixfix_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_notationLike() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("notationLike");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_notation_HasView;
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
obj* _init_l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("notationLike");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
lean::dec(x_39);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_58 = l_Lean_Parser_command_mixfix_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_52);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_68; obj* x_69; 
x_64 = l_Lean_Parser_command_notation_HasView;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_68 = lean::apply_1(x_65, x_52);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_73 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_73;
}
}
}
}
}
}
}
else
{
obj* x_76; 
lean::dec(x_8);
lean::dec(x_17);
x_76 = l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1;
return x_76;
}
}
}
}
}
}
obj* l_Lean_Parser_command_notationLike_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_command_notation_HasView;
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
x_14 = l_Lean_Parser_command_notationLike;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_mixfix_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_notationLike;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_Lean_Parser_command_notationLike_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_notationLike_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_notationLike_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_0);
x_3 = l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_2);
lean::dec(x_2);
x_6 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_0);
lean::dec(x_6);
x_10 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notation_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_TermParserM_Monad;
x_9 = l_Lean_Parser_TermParserM_MonadExcept;
x_10 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_TermParserM_Alternative;
x_12 = l_Lean_Parser_command_notationLike;
x_13 = l_Lean_Parser_command_notationLike_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_notationLike_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notation_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__3), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
}
}
obj* l_Lean_Parser_command_notationLike_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_notationLike;
x_6 = l_Lean_Parser_command_notationLike_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("reserveMixfix");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_mixfix_kind_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1;
x_2 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
else
{
obj* x_22; obj* x_24; obj* x_27; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_13, 1);
lean::inc(x_24);
lean::dec(x_13);
x_27 = l_Lean_Parser_Syntax_asNode___main(x_22);
if (lean::obj_tag(x_27) == 0)
{
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; 
x_28 = lean::box(3);
x_5 = x_24;
x_6 = x_28;
goto lbl_7;
}
else
{
obj* x_29; obj* x_31; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_24, 1);
lean::inc(x_31);
lean::dec(x_24);
x_5 = x_31;
x_6 = x_29;
goto lbl_7;
}
}
else
{
obj* x_34; obj* x_37; obj* x_40; 
x_34 = lean::cnstr_get(x_27, 0);
lean::inc(x_34);
lean::dec(x_27);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_List_append___rarg(x_37, x_24);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; 
x_41 = lean::box(3);
x_5 = x_40;
x_6 = x_41;
goto lbl_7;
}
else
{
obj* x_42; obj* x_44; 
x_42 = lean::cnstr_get(x_40, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_40, 1);
lean::inc(x_44);
lean::dec(x_40);
x_5 = x_44;
x_6 = x_42;
goto lbl_7;
}
}
}
}
lbl_4:
{
obj* x_47; obj* x_48; obj* x_51; 
x_47 = l_Lean_Parser_command_mixfix_kind_HasView;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::apply_1(x_48, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_52; obj* x_53; 
x_52 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_51);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; 
x_54 = lean::cnstr_get(x_3, 0);
lean::inc(x_54);
lean::dec(x_3);
x_57 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
lean::dec(x_57);
x_61 = lean::apply_1(x_58, x_54);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_1);
lean::cnstr_set(x_62, 1, x_51);
lean::cnstr_set(x_62, 2, x_61);
return x_62;
}
}
lbl_7:
{
obj* x_63; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_65; obj* x_68; 
x_65 = lean::cnstr_get(x_6, 0);
lean::inc(x_65);
lean::dec(x_6);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_65);
if (lean::obj_tag(x_5) == 0)
{
x_63 = x_68;
goto lbl_64;
}
else
{
obj* x_69; obj* x_71; 
x_69 = lean::cnstr_get(x_5, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_5, 1);
lean::inc(x_71);
lean::dec(x_5);
x_1 = x_68;
x_2 = x_69;
x_3 = x_71;
goto lbl_4;
}
}
case 3:
{
obj* x_74; 
x_74 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_63 = x_74;
goto lbl_64;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_5, 1);
lean::inc(x_77);
lean::dec(x_5);
x_1 = x_74;
x_2 = x_75;
x_3 = x_77;
goto lbl_4;
}
}
default:
{
obj* x_81; 
lean::dec(x_6);
x_81 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_63 = x_81;
goto lbl_64;
}
else
{
obj* x_82; obj* x_84; 
x_82 = lean::cnstr_get(x_5, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_5, 1);
lean::inc(x_84);
lean::dec(x_5);
x_1 = x_81;
x_2 = x_82;
x_3 = x_84;
goto lbl_4;
}
}
}
lbl_64:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1;
x_88 = l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1;
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_63);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set(x_89, 2, x_88);
return x_89;
}
else
{
obj* x_90; obj* x_93; obj* x_94; obj* x_97; obj* x_98; obj* x_99; 
x_90 = lean::cnstr_get(x_5, 0);
lean::inc(x_90);
lean::dec(x_5);
x_93 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
lean::dec(x_93);
x_97 = lean::apply_1(x_94, x_90);
x_98 = l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1;
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_63);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set(x_99, 2, x_97);
return x_99;
}
}
}
}
}
obj* l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_mixfix_kind_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_command_NotationSpec_notationSymbol_HasView;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_5);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
x_23 = l_Lean_Parser_noKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_20);
x_26 = l_Lean_Parser_command_reserveMixfix;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_28 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_30 = x_1;
} else {
 lean::inc(x_28);
 lean::dec(x_1);
 x_30 = lean::box(0);
}
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::box(3);
x_34 = l_Option_getOrElse___main___rarg(x_32, x_33);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_14);
x_37 = l_Lean_Parser_noKind;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_20);
x_40 = l_Lean_Parser_command_reserveMixfix;
x_41 = l_Lean_Parser_Syntax_mkNode(x_40, x_39);
return x_41;
}
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_reserveMixfix_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_19; 
x_0 = lean::mk_string("reserve");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_4);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_10 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
x_12 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_14 = l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens;
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_4);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_15);
lean::dec(x_15);
lean::dec(x_12);
x_19 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
return x_19;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_0 = lean::mk_string("reserve");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_Parser), 5, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_TermParserM_Monad;
x_16 = l_Lean_Parser_TermParserM_MonadExcept;
x_17 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_18 = l_Lean_Parser_TermParserM_Alternative;
x_19 = l_Lean_Parser_command_reserveMixfix;
x_20 = l_Lean_Parser_command_reserveMixfix_HasView;
x_21 = l_Lean_Parser_Combinators_node_view___rarg(x_15, x_16, x_17, x_18, x_19, x_14, x_20);
lean::dec(x_14);
return x_21;
}
}
obj* _init_l_Lean_Parser_command_reserveMixfix_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::mk_string("reserve");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_mixfix_kind_Parser), 5, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser), 5, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_command_reserveMixfix_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_reserveMixfix;
x_6 = l_Lean_Parser_command_reserveMixfix_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* initialize_init_lean_parser_token(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_notation(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_token(w);
 l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1 = _init_l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens___closed__1);
 l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1 = _init_l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_Parser_Lean_Parser_HasView___closed__1);
 l_Lean_Parser_Term_Parser___closed__1 = _init_l_Lean_Parser_Term_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Term_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceLit = _init_l_Lean_Parser_command_NotationSpec_precedenceLit();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit);
 l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_precedenceLit_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_HasView);
 l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1 = _init_l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_number_Parser___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens___spec__1___rarg___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceLit_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffsetOp_HasView);
 l_Lean_Parser_command_NotationSpec_precedenceOffset = _init_l_Lean_Parser_command_NotationSpec_precedenceOffset();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffset);
 l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceOffset_HasView);
 l_Lean_Parser_command_NotationSpec_precedenceTerm = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_HasView);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedenceTerm_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_precedence = _init_l_Lean_Parser_command_NotationSpec_precedence();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence);
 l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_precedence_HasView = _init_l_Lean_Parser_command_NotationSpec_precedence_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_HasView);
 l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_precedence_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_quotedSymbol_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_symbolQuote = _init_l_Lean_Parser_command_NotationSpec_symbolQuote();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_symbolQuote_HasView = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_HasView);
 l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_symbolQuote_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_unquotedSymbol_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens = _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_unquotedSymbol_tokens);
 l_Lean_Parser_command_NotationSpec_unquotedSymbol_View = _init_l_Lean_Parser_command_NotationSpec_unquotedSymbol_View();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_unquotedSymbol_View);
 l_Lean_Parser_command_NotationSpec_notationSymbol = _init_l_Lean_Parser_command_NotationSpec_notationSymbol();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol);
 l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_notationSymbol_HasView = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_HasView);
 l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_notationSymbol_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_HasView);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_mixfixSymbol_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_foldActionFolder = _init_l_Lean_Parser_command_NotationSpec_foldActionFolder();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldActionFolder);
 l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView = _init_l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldActionFolder_HasView);
 l_Lean_Parser_command_NotationSpec_foldAction = _init_l_Lean_Parser_command_NotationSpec_foldAction();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction);
 l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_foldAction_HasView = _init_l_Lean_Parser_command_NotationSpec_foldAction_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_HasView);
 l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1 = _init_l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1);
 l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_foldAction_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_scopedAction = _init_l_Lean_Parser_command_NotationSpec_scopedAction();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_scopedAction);
 l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_scopedAction_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_scopedAction_HasView = _init_l_Lean_Parser_command_NotationSpec_scopedAction_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_scopedAction_HasView);
 l_Lean_Parser_command_NotationSpec_actionKind = _init_l_Lean_Parser_command_NotationSpec_actionKind();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_actionKind);
 l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_actionKind_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_actionKind_HasView = _init_l_Lean_Parser_command_NotationSpec_actionKind_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_actionKind_HasView);
 l_Lean_Parser_command_NotationSpec_action = _init_l_Lean_Parser_command_NotationSpec_action();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action);
 l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_action_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_action_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_action_HasView = _init_l_Lean_Parser_command_NotationSpec_action_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_HasView);
 l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_action_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_action_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_action_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_binder = _init_l_Lean_Parser_command_NotationSpec_binder();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binder);
 l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_binder_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_binder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binder_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_binder_HasView = _init_l_Lean_Parser_command_NotationSpec_binder_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binder_HasView);
 l_Lean_Parser_command_NotationSpec_binders = _init_l_Lean_Parser_command_NotationSpec_binders();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binders);
 l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binders_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_binders_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_binders_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binders_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_binders_HasView = _init_l_Lean_Parser_command_NotationSpec_binders_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_binders_HasView);
 l_Lean_Parser_command_NotationSpec_argument = _init_l_Lean_Parser_command_NotationSpec_argument();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_NotationSpec_argument_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_argument_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_argument_HasView = _init_l_Lean_Parser_command_NotationSpec_argument_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_argument_HasView);
 l_Lean_Parser_command_NotationSpec_transition = _init_l_Lean_Parser_command_NotationSpec_transition();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition);
 l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_transition_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_transition_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_transition_HasView = _init_l_Lean_Parser_command_NotationSpec_transition_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_HasView);
 l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_transition_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec_rule = _init_l_Lean_Parser_command_NotationSpec_rule();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule);
 l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_rule_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_rule_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_rule_HasView = _init_l_Lean_Parser_command_NotationSpec_rule_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_HasView);
 l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_rule_Parser___closed__1);
 l_Lean_Parser_command_NotationSpec = _init_l_Lean_Parser_command_NotationSpec();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_NotationSpec_HasView_x_27 = _init_l_Lean_Parser_command_NotationSpec_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView_x_27);
 l_Lean_Parser_command_NotationSpec_HasView = _init_l_Lean_Parser_command_NotationSpec_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_HasView);
 l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_NotationSpec_Parser___closed__1 = _init_l_Lean_Parser_command_NotationSpec_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_NotationSpec_Parser___closed__1);
 l_Lean_Parser_command_notation = _init_l_Lean_Parser_command_notation();
lean::mark_persistent(l_Lean_Parser_command_notation);
 l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_notation_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_notation_HasView_x_27 = _init_l_Lean_Parser_command_notation_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_notation_HasView_x_27);
 l_Lean_Parser_command_notation_HasView = _init_l_Lean_Parser_command_notation_HasView();
lean::mark_persistent(l_Lean_Parser_command_notation_HasView);
 l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_notation_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_notation_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_notation_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_notation_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_notation_Parser___closed__1 = _init_l_Lean_Parser_command_notation_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_notation_Parser___closed__1);
 l_Lean_Parser_command_reserveNotation = _init_l_Lean_Parser_command_reserveNotation();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation);
 l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_reserveNotation_HasView_x_27 = _init_l_Lean_Parser_command_reserveNotation_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_HasView_x_27);
 l_Lean_Parser_command_reserveNotation_HasView = _init_l_Lean_Parser_command_reserveNotation_HasView();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_HasView);
 l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_reserveNotation_Parser___closed__1 = _init_l_Lean_Parser_command_reserveNotation_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_reserveNotation_Parser___closed__1);
 l_Lean_Parser_command_mixfix_kind = _init_l_Lean_Parser_command_mixfix_kind();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__1___closed__7);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__3);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__4);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__5);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27___lambda__2___closed__6);
 l_Lean_Parser_command_mixfix_kind_HasView_x_27 = _init_l_Lean_Parser_command_mixfix_kind_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView_x_27);
 l_Lean_Parser_command_mixfix_kind_HasView = _init_l_Lean_Parser_command_mixfix_kind_HasView();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_HasView);
 l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_mixfix_kind_Parser___closed__1 = _init_l_Lean_Parser_command_mixfix_kind_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_mixfix_kind_Parser___closed__1);
 l_Lean_Parser_command_mixfix = _init_l_Lean_Parser_command_mixfix();
lean::mark_persistent(l_Lean_Parser_command_mixfix);
 l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_mixfix_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_mixfix_HasView_x_27 = _init_l_Lean_Parser_command_mixfix_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_mixfix_HasView_x_27);
 l_Lean_Parser_command_mixfix_HasView = _init_l_Lean_Parser_command_mixfix_HasView();
lean::mark_persistent(l_Lean_Parser_command_mixfix_HasView);
 l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_mixfix_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_mixfix_Parser___closed__1 = _init_l_Lean_Parser_command_mixfix_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_mixfix_Parser___closed__1);
 l_Lean_Parser_command_notationLike = _init_l_Lean_Parser_command_notationLike();
lean::mark_persistent(l_Lean_Parser_command_notationLike);
 l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_notationLike_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_notationLike_HasView_x_27 = _init_l_Lean_Parser_command_notationLike_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_notationLike_HasView_x_27);
 l_Lean_Parser_command_notationLike_HasView = _init_l_Lean_Parser_command_notationLike_HasView();
lean::mark_persistent(l_Lean_Parser_command_notationLike_HasView);
 l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_notationLike_Parser___closed__1 = _init_l_Lean_Parser_command_notationLike_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_notationLike_Parser___closed__1);
 l_Lean_Parser_command_reserveMixfix = _init_l_Lean_Parser_command_reserveMixfix();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix);
 l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_reserveMixfix_HasView_x_27 = _init_l_Lean_Parser_command_reserveMixfix_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_HasView_x_27);
 l_Lean_Parser_command_reserveMixfix_HasView = _init_l_Lean_Parser_command_reserveMixfix_HasView();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_HasView);
 l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_reserveMixfix_Parser___closed__1 = _init_l_Lean_Parser_command_reserveMixfix_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_reserveMixfix_Parser___closed__1);
return w;
}
