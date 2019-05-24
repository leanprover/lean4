// Lean compiler output
// Module: init.lean.parser.level
// Imports: init.lean.parser.pratt
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
obj* l_Lean_Parser_Level_leading_Parser___closed__1;
obj* l_Lean_Parser_prattParser_View___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_LevelParserM_Monad;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___boxed(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_trailingLevelParserCoe(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix___rarg(obj*, obj*);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Level_paren;
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_Lean_Parser_MonadRec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5;
extern obj* l_mjoin___rarg___closed__1;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_HasView_x27;
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l_Lean_Parser_LevelParserM_MonadExcept;
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
obj* l_Lean_Parser_TrailingLevelParserM_Alternative;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1;
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__2(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3;
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3(obj*);
obj* l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Level_leading_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5(obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren_Parser___closed__1;
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Parser_Level_app;
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_Level_addLit;
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
obj* l_Lean_Parser_Level_paren_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_toString(obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_HasView;
obj* l_Lean_Parser_LevelParserM_MonadReader;
obj* l_Lean_Parser_levelParserCoe;
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_currLbp___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3;
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_Level_trailing_Parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Level_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadReader;
obj* l_Lean_Parser_Combinators_recurse_view___rarg(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_number;
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*);
obj* l_Lean_Parser_TrailingLevelParserM_MonadExcept;
obj* l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_HasView_x27;
obj* l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser;
obj* l_Lean_Parser_Level_getLeading(obj*, obj*, obj*, obj*, obj*);
obj* l_hasMonadLiftTTrans___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1;
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_Level_trailing_Parser___closed__1;
obj* l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView;
obj* l_hasMonadLiftTRefl___boxed(obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
obj* l_Lean_Parser_Level_paren_HasView_x27;
obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1(obj*);
extern obj* l_Lean_Parser_matchToken___closed__1;
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_LevelParserM_Alternative;
obj* l_Lean_Parser_Level_addLit_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Level_paren_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x27;
extern obj* l_Lean_Parser_peekToken___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(obj*);
obj* l_Lean_Parser_Level_paren_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___boxed(obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_addLit_Parser___closed__1;
obj* l_Lean_Parser_Level_trailing;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Level_leading;
obj* l_Lean_Parser_Combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_HasView;
extern obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_Level_Parser___closed__1;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2;
obj* l_String_trim(obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_trailingLevelParserCoe___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
obj* l_Lean_Parser_Level_Lean_Parser_HasView;
obj* l_Lean_Parser_TrailingLevelParserM_MonadReader;
obj* l_ReaderT_MonadExcept___rarg(obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x27;
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_app_Parser___closed__1;
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___boxed(obj*);
obj* l_Lean_Parser_Level_getLeading___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
obj* l_Lean_Parser_levelParser_run(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_addLit_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Parser_Level_app_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
extern obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1;
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_Level_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
obj* l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2;
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Monad;
extern obj* l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1;
obj* _init_l_Lean_Parser_LevelParserM_Monad() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Alternative() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = l_Lean_Parser_BasicParserM_Alternative;
x_3 = l_ReaderT_Alternative___rarg(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_LevelParserM_MonadReader() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_BasicParserM_MonadReader;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___rarg___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_3 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_LevelParserM_MonadExcept() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_BasicParserM_MonadExcept;
x_2 = l_ReaderT_MonadExcept___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTRefl___boxed), 2, 1);
lean::closure_set(x_3, 0, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg), 4, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Monad() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Alternative() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = l_Lean_Parser_LevelParserM_Alternative;
x_3 = l_ReaderT_Alternative___rarg(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_MonadReader() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_3, 0, lean::box(0));
lean::closure_set(x_3, 1, lean::box(0));
lean::closure_set(x_3, 2, lean::box(0));
lean::closure_set(x_3, 3, x_1);
lean::closure_set(x_3, 4, x_1);
x_4 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_5 = l_Lean_Parser_monadParsecTrans___rarg(x_2, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_MonadExcept() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_LevelParserM_MonadExcept;
x_2 = l_ReaderT_MonadExcept___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadRec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
lean::closure_set(x_4, 2, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_LevelParserM_Monad;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_1);
x_3 = l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg), 4, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_trailingLevelParserCoe(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_trailingLevelParserCoe___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_trailingLevelParserCoe(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_2, x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
return x_2;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("universe Level");
return x_1;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
x_4 = l_Lean_Parser_Combinators_recurse_view___rarg(x_1, x_3);
lean::dec(x_1);
x_5 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_6 = l_Lean_Parser_LevelParserM_Alternative;
x_7 = l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1;
x_8 = l_Lean_Parser_Combinators_label_view___rarg(x_5, x_6, x_2, x_7, x_4);
lean::dec(x_2);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("universe Level");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Level_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::apply_4(x_2, x_1, x_3, x_4, x_5);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_Lean_Parser_Level_Parser___closed__1;
x_10 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_8, x_9);
lean::cnstr_set(x_6, 0, x_10);
return x_6;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 0);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_6);
x_13 = l_Lean_Parser_Level_Parser___closed__1;
x_14 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_11, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
}
}
obj* l_Lean_Parser_Level_getLeading(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_Lean_Parser_Level_getLeading___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Level_getLeading(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_1);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("paren");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_paren_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::box(3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_Lean_Parser_Level_paren;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_5);
lean::inc(x_3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_3);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_Level_paren;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
if (lean::obj_tag(x_4) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
lean::inc(x_3);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_3);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_Level_paren;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_4, 0);
lean::inc(x_27);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_5);
lean::inc(x_3);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_Level_paren;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
}
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Level_paren_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_14; obj* x_15; obj* x_28; 
x_28 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
lean::dec(x_28);
x_29 = l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2;
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = lean::box(3);
x_14 = x_31;
x_15 = x_32;
goto block_27;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_14 = x_34;
x_15 = x_33;
goto block_27;
}
}
block_13:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_5);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_4, 0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_3);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_3);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
}
block_27:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_14);
x_18 = lean::box(0);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_14, 1);
lean::inc(x_22);
lean::dec(x_14);
x_2 = x_17;
x_3 = x_21;
x_4 = x_22;
goto block_13;
}
}
else
{
lean::dec(x_15);
if (lean::obj_tag(x_14) == 0)
{
obj* x_23; 
lean::dec(x_14);
x_23 = l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
lean::dec(x_14);
x_26 = lean::box(0);
x_2 = x_26;
x_3 = x_24;
x_4 = x_25;
goto block_13;
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_paren_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_paren_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_paren_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_1);
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_Lean_Parser_token(x_5, x_6, x_7);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_9, 1);
x_13 = lean::cnstr_get(x_9, 0);
lean::dec(x_13);
x_14 = !lean::is_exclusive(x_10);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_10, 0);
x_16 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_39; obj* x_40; uint8 x_41; 
x_39 = lean::cnstr_get(x_15, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_41 = lean::string_dec_eq(x_1, x_40);
lean::dec(x_1);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::free_heap_obj(x_10);
lean::free_heap_obj(x_9);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_6);
x_43 = lean::box(0);
x_44 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_40, x_3, x_42, x_43, x_5, x_16, x_12);
lean::dec(x_5);
lean::dec(x_42);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_44);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = lean::cnstr_get(x_44, 0);
lean::dec(x_47);
x_48 = !lean::is_exclusive(x_45);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_49 = lean::cnstr_get(x_45, 2);
x_50 = lean::cnstr_get(x_45, 0);
lean::dec(x_50);
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_45, 2, x_51);
lean::cnstr_set(x_45, 0, x_15);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_45);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_53);
x_55 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_54, x_8);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
lean::cnstr_set(x_44, 0, x_56);
return x_44;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_57 = lean::cnstr_get(x_45, 1);
x_58 = lean::cnstr_get(x_45, 2);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_45);
x_59 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_15);
lean::cnstr_set(x_60, 1, x_57);
lean::cnstr_set(x_60, 2, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_62);
x_64 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_63, x_8);
x_65 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_64);
lean::cnstr_set(x_44, 0, x_65);
return x_44;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_66 = lean::cnstr_get(x_44, 1);
lean::inc(x_66);
lean::dec(x_44);
x_67 = lean::cnstr_get(x_45, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_45, 2);
lean::inc(x_68);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 lean::cnstr_release(x_45, 2);
 x_69 = x_45;
} else {
 lean::dec_ref(x_45);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_15);
lean::cnstr_set(x_71, 1, x_67);
lean::cnstr_set(x_71, 2, x_70);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_73);
x_75 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_74, x_8);
x_76 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_66);
return x_77;
}
}
else
{
uint8 x_78; 
lean::dec(x_15);
x_78 = !lean::is_exclusive(x_44);
if (x_78 == 0)
{
obj* x_79; uint8 x_80; 
x_79 = lean::cnstr_get(x_44, 0);
lean::dec(x_79);
x_80 = !lean::is_exclusive(x_45);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_45);
x_82 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_81);
x_84 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_83, x_8);
x_85 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_84);
lean::cnstr_set(x_44, 0, x_85);
return x_44;
}
else
{
obj* x_86; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_86 = lean::cnstr_get(x_45, 0);
x_87 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
lean::inc(x_86);
lean::dec(x_45);
x_88 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set_scalar(x_88, sizeof(void*)*1, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_88);
x_90 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_89);
x_92 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_91, x_8);
x_93 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_92);
lean::cnstr_set(x_44, 0, x_93);
return x_44;
}
}
else
{
obj* x_94; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_44, 1);
lean::inc(x_94);
lean::dec(x_44);
x_95 = lean::cnstr_get(x_45, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_97 = x_45;
} else {
 lean::dec_ref(x_45);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_98);
x_100 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_100, x_99);
x_102 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_101, x_8);
x_103 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_102);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_94);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_40);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_105 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_10, 2, x_105);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_10);
x_107 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_106);
x_109 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_108, x_8);
x_110 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_109);
lean::cnstr_set(x_9, 0, x_110);
return x_9;
}
}
else
{
obj* x_111; 
lean::free_heap_obj(x_10);
lean::dec(x_15);
lean::free_heap_obj(x_9);
lean::dec(x_1);
x_111 = lean::box(0);
x_18 = x_111;
goto block_38;
}
block_38:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
lean::dec(x_18);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_6);
x_20 = lean::box(0);
x_21 = l_String_splitAux___main___closed__1;
x_22 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_21, x_3, x_19, x_20, x_5, x_16, x_12);
lean::dec(x_5);
lean::dec(x_19);
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_24 = lean::cnstr_get(x_22, 0);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_24);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_25);
x_28 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_27, x_8);
x_29 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_28);
lean::cnstr_set(x_22, 0, x_29);
return x_22;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_22, 0);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_22);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_30);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_32);
x_35 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_34, x_8);
x_36 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_112 = lean::cnstr_get(x_10, 0);
x_113 = lean::cnstr_get(x_10, 1);
x_114 = lean::cnstr_get(x_10, 2);
lean::inc(x_114);
lean::inc(x_113);
lean::inc(x_112);
lean::dec(x_10);
if (lean::obj_tag(x_112) == 0)
{
obj* x_130; obj* x_131; uint8 x_132; 
x_130 = lean::cnstr_get(x_112, 0);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_130, 1);
lean::inc(x_131);
lean::dec(x_130);
x_132 = lean::string_dec_eq(x_1, x_131);
lean::dec(x_1);
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::free_heap_obj(x_9);
x_133 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_133, 0, x_6);
x_134 = lean::box(0);
x_135 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_131, x_3, x_133, x_134, x_5, x_113, x_12);
lean::dec(x_5);
lean::dec(x_133);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_137 = lean::cnstr_get(x_135, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_138 = x_135;
} else {
 lean::dec_ref(x_135);
 x_138 = lean::box(0);
}
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_136, 2);
lean::inc(x_140);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 lean::cnstr_release(x_136, 2);
 x_141 = x_136;
} else {
 lean::dec_ref(x_136);
 x_141 = lean::box(0);
}
x_142 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_141)) {
 x_143 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_143 = x_141;
}
lean::cnstr_set(x_143, 0, x_112);
lean::cnstr_set(x_143, 1, x_139);
lean::cnstr_set(x_143, 2, x_142);
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_144);
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_142, x_145);
x_147 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_146, x_8);
x_148 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_147);
if (lean::is_scalar(x_138)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_138;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_137);
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_112);
x_150 = lean::cnstr_get(x_135, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_151 = x_135;
} else {
 lean::dec_ref(x_135);
 x_151 = lean::box(0);
}
x_152 = lean::cnstr_get(x_136, 0);
lean::inc(x_152);
x_153 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_154 = x_136;
} else {
 lean::dec_ref(x_136);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
lean::cnstr_set_scalar(x_155, sizeof(void*)*1, x_153);
x_156 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_155);
x_157 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_158 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_157, x_156);
x_159 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_158, x_8);
x_160 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_159);
if (lean::is_scalar(x_151)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_151;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_150);
return x_161;
}
}
else
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_131);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_162 = l_Lean_Parser_finishCommentBlock___closed__2;
x_163 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_163, 0, x_112);
lean::cnstr_set(x_163, 1, x_113);
lean::cnstr_set(x_163, 2, x_162);
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_163);
x_165 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_166 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_165, x_164);
x_167 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_166, x_8);
x_168 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_167);
lean::cnstr_set(x_9, 0, x_168);
return x_9;
}
}
else
{
obj* x_169; 
lean::dec(x_112);
lean::free_heap_obj(x_9);
lean::dec(x_1);
x_169 = lean::box(0);
x_115 = x_169;
goto block_129;
}
block_129:
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_115);
x_116 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_116, 0, x_6);
x_117 = lean::box(0);
x_118 = l_String_splitAux___main___closed__1;
x_119 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_118, x_3, x_116, x_117, x_5, x_113, x_12);
lean::dec(x_5);
lean::dec(x_116);
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_119, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 lean::cnstr_release(x_119, 1);
 x_122 = x_119;
} else {
 lean::dec_ref(x_119);
 x_122 = lean::box(0);
}
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_120);
x_124 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_125 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_124, x_123);
x_126 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_125, x_8);
x_127 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_126);
if (lean::is_scalar(x_122)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_122;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
return x_128;
}
}
}
else
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_170 = lean::cnstr_get(x_9, 1);
lean::inc(x_170);
lean::dec(x_9);
x_171 = lean::cnstr_get(x_10, 0);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_10, 1);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_10, 2);
lean::inc(x_173);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_174 = x_10;
} else {
 lean::dec_ref(x_10);
 x_174 = lean::box(0);
}
if (lean::obj_tag(x_171) == 0)
{
obj* x_190; obj* x_191; uint8 x_192; 
x_190 = lean::cnstr_get(x_171, 0);
lean::inc(x_190);
x_191 = lean::cnstr_get(x_190, 1);
lean::inc(x_191);
lean::dec(x_190);
x_192 = lean::string_dec_eq(x_1, x_191);
lean::dec(x_1);
if (x_192 == 0)
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_174);
x_193 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_193, 0, x_6);
x_194 = lean::box(0);
x_195 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_191, x_3, x_193, x_194, x_5, x_172, x_170);
lean::dec(x_5);
lean::dec(x_193);
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
x_197 = lean::cnstr_get(x_195, 1);
lean::inc(x_197);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_release(x_195, 0);
 lean::cnstr_release(x_195, 1);
 x_198 = x_195;
} else {
 lean::dec_ref(x_195);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
x_200 = lean::cnstr_get(x_196, 2);
lean::inc(x_200);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 lean::cnstr_release(x_196, 2);
 x_201 = x_196;
} else {
 lean::dec_ref(x_196);
 x_201 = lean::box(0);
}
x_202 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_201)) {
 x_203 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_203 = x_201;
}
lean::cnstr_set(x_203, 0, x_171);
lean::cnstr_set(x_203, 1, x_199);
lean::cnstr_set(x_203, 2, x_202);
x_204 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_203);
x_205 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_204);
x_206 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_202, x_205);
x_207 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_206, x_8);
x_208 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_207);
if (lean::is_scalar(x_198)) {
 x_209 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_209 = x_198;
}
lean::cnstr_set(x_209, 0, x_208);
lean::cnstr_set(x_209, 1, x_197);
return x_209;
}
else
{
obj* x_210; obj* x_211; obj* x_212; uint8 x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_171);
x_210 = lean::cnstr_get(x_195, 1);
lean::inc(x_210);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_release(x_195, 0);
 lean::cnstr_release(x_195, 1);
 x_211 = x_195;
} else {
 lean::dec_ref(x_195);
 x_211 = lean::box(0);
}
x_212 = lean::cnstr_get(x_196, 0);
lean::inc(x_212);
x_213 = lean::cnstr_get_scalar<uint8>(x_196, sizeof(void*)*1);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 x_214 = x_196;
} else {
 lean::dec_ref(x_196);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
lean::cnstr_set_scalar(x_215, sizeof(void*)*1, x_213);
x_216 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_215);
x_217 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_218 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_217, x_216);
x_219 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_218, x_8);
x_220 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_219);
if (lean::is_scalar(x_211)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_211;
}
lean::cnstr_set(x_221, 0, x_220);
lean::cnstr_set(x_221, 1, x_210);
return x_221;
}
}
else
{
obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_191);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_222 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_174)) {
 x_223 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_223 = x_174;
}
lean::cnstr_set(x_223, 0, x_171);
lean::cnstr_set(x_223, 1, x_172);
lean::cnstr_set(x_223, 2, x_222);
x_224 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_223);
x_225 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_226 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_225, x_224);
x_227 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_226, x_8);
x_228 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_227);
x_229 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_170);
return x_229;
}
}
else
{
obj* x_230; 
lean::dec(x_174);
lean::dec(x_171);
lean::dec(x_1);
x_230 = lean::box(0);
x_175 = x_230;
goto block_189;
}
block_189:
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
lean::dec(x_175);
x_176 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_176, 0, x_6);
x_177 = lean::box(0);
x_178 = l_String_splitAux___main___closed__1;
x_179 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_178, x_3, x_176, x_177, x_5, x_172, x_170);
lean::dec(x_5);
lean::dec(x_176);
x_180 = lean::cnstr_get(x_179, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_179, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 lean::cnstr_release(x_179, 1);
 x_182 = x_179;
} else {
 lean::dec_ref(x_179);
 x_182 = lean::box(0);
}
x_183 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_180);
x_184 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_185 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_184, x_183);
x_186 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_185, x_8);
x_187 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_186);
if (lean::is_scalar(x_182)) {
 x_188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_188 = x_182;
}
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_181);
return x_188;
}
}
}
else
{
uint8 x_231; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_231 = !lean::is_exclusive(x_9);
if (x_231 == 0)
{
obj* x_232; uint8 x_233; 
x_232 = lean::cnstr_get(x_9, 0);
lean::dec(x_232);
x_233 = !lean::is_exclusive(x_10);
if (x_233 == 0)
{
obj* x_234; obj* x_235; obj* x_236; obj* x_237; 
x_234 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_235 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_234, x_10);
x_236 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_235, x_8);
x_237 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_236);
lean::cnstr_set(x_9, 0, x_237);
return x_9;
}
else
{
obj* x_238; uint8 x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
x_238 = lean::cnstr_get(x_10, 0);
x_239 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_238);
lean::dec(x_10);
x_240 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_240, 0, x_238);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_239);
x_241 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_242 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_241, x_240);
x_243 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_242, x_8);
x_244 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_243);
lean::cnstr_set(x_9, 0, x_244);
return x_9;
}
}
else
{
obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_245 = lean::cnstr_get(x_9, 1);
lean::inc(x_245);
lean::dec(x_9);
x_246 = lean::cnstr_get(x_10, 0);
lean::inc(x_246);
x_247 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_248 = x_10;
} else {
 lean::dec_ref(x_10);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_246);
lean::cnstr_set_scalar(x_249, sizeof(void*)*1, x_247);
x_250 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_251 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_250, x_249);
x_252 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_251, x_8);
x_253 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_252);
x_254 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_254, 0, x_253);
lean::cnstr_set(x_254, 1, x_245);
return x_254;
}
}
}
}
obj* _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::mk_string("(");
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(x_4);
x_6 = lean::mk_string(")");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_4);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_8);
lean::dec(x_7);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_10);
lean::dec(x_10);
lean::dec(x_3);
x_12 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
return x_12;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_2);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_maxPrec;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_Parser), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string(")");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_6);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_LevelParserM_Monad;
x_17 = l_Lean_Parser_LevelParserM_MonadExcept;
x_18 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_19 = l_Lean_Parser_LevelParserM_Alternative;
x_20 = l_Lean_Parser_Level_paren;
x_21 = l_Lean_Parser_Level_paren_HasView;
x_22 = l_Lean_Parser_Combinators_node_view___rarg(x_16, x_17, x_18, x_19, x_20, x_15, x_21);
lean::dec(x_15);
return x_22;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
x_25 = l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(x_1, x_22, x_12, x_4, x_5, x_23, x_15);
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
x_49 = l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(x_1, x_46, x_12, x_4, x_5, x_47, x_15);
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
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::box(0);
lean::inc(x_1);
x_8 = l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
obj* _init_l_Lean_Parser_Level_paren_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_maxPrec;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_Parser), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string(")");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_6);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_Level_paren_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Level_paren;
x_6 = l_Lean_Parser_Level_paren_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_leading() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("leading");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1() {
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
x_9 = l_Lean_Parser_Level_leading;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(4u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(5u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_Level_leading;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
case 1:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
x_12 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
x_15 = l_Lean_Parser_Level_leading;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
case 2:
{
obj* x_17; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
lean::dec(x_17);
x_18 = l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1;
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
x_22 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_2);
x_25 = l_Lean_Parser_Level_leading;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
return x_26;
}
}
case 3:
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
lean::dec(x_1);
x_28 = l_Lean_Parser_Level_paren_HasView;
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
x_30 = lean::apply_1(x_29, x_27);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_2);
x_32 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_2);
x_35 = l_Lean_Parser_Level_leading;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
case 4:
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
lean::dec(x_1);
x_38 = l_Lean_Parser_number_HasView;
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
x_40 = lean::apply_1(x_39, x_37);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_2);
x_42 = l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2;
x_43 = l_Lean_Parser_Syntax_mkNode(x_42, x_41);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_2);
x_45 = l_Lean_Parser_Level_leading;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
return x_46;
}
default: 
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get(x_1, 0);
lean::inc(x_47);
lean::dec(x_1);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_2);
x_50 = l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_2);
x_53 = l_Lean_Parser_Level_leading;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
return x_54;
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_8 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("leading");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_leading_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
x_7 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
x_10 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
x_14 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
x_18 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
x_25 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
x_26 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
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
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
lean::free_heap_obj(x_13);
x_35 = lean::mk_nat_obj(3u);
x_36 = lean::nat_dec_eq(x_22, x_35);
if (x_36 == 0)
{
obj* x_37; uint8 x_38; 
x_37 = lean::mk_nat_obj(4u);
x_38 = lean::nat_dec_eq(x_22, x_37);
lean::dec(x_22);
if (x_38 == 0)
{
if (lean::obj_tag(x_28) == 1)
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_40 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_41; 
lean::dec(x_28);
x_41 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2;
return x_41;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = l_Lean_Parser_number_HasView;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::apply_1(x_43, x_28);
x_45 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_22);
x_46 = l_Lean_Parser_Level_paren_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_28);
x_49 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_50; obj* x_51; 
x_50 = lean::cnstr_get(x_28, 0);
lean::inc(x_50);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_50);
x_51 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_51, 0, x_13);
return x_51;
}
else
{
obj* x_52; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_52 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3;
return x_52;
}
}
}
else
{
obj* x_53; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_28);
return x_53;
}
}
else
{
obj* x_54; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_28);
return x_54;
}
}
else
{
obj* x_55; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_55 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_55;
}
}
}
}
}
}
else
{
obj* x_56; obj* x_57; 
x_56 = lean::cnstr_get(x_13, 0);
lean::inc(x_56);
lean::dec(x_13);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
switch (lean::obj_tag(x_57)) {
case 0:
{
obj* x_58; 
lean::dec(x_57);
lean::dec(x_56);
x_58 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_58;
}
case 1:
{
obj* x_59; 
lean::dec(x_57);
lean::dec(x_56);
x_59 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_59;
}
default: 
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; uint8 x_64; 
x_60 = lean::cnstr_get(x_56, 1);
lean::inc(x_60);
lean::dec(x_56);
x_61 = lean::cnstr_get(x_57, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
lean::dec(x_57);
x_63 = lean::box(0);
x_64 = lean_name_dec_eq(x_61, x_63);
lean::dec(x_61);
if (x_64 == 0)
{
obj* x_65; 
lean::dec(x_62);
lean::dec(x_60);
x_65 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_65;
}
else
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_66; 
lean::dec(x_62);
lean::dec(x_60);
x_66 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_66;
}
else
{
obj* x_67; 
x_67 = lean::cnstr_get(x_60, 1);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; uint8 x_70; 
lean::dec(x_67);
x_68 = lean::cnstr_get(x_60, 0);
lean::inc(x_68);
lean::dec(x_60);
x_69 = lean::mk_nat_obj(0u);
x_70 = lean::nat_dec_eq(x_62, x_69);
if (x_70 == 0)
{
obj* x_71; uint8 x_72; 
x_71 = lean::mk_nat_obj(1u);
x_72 = lean::nat_dec_eq(x_62, x_71);
if (x_72 == 0)
{
obj* x_73; uint8 x_74; 
x_73 = lean::mk_nat_obj(2u);
x_74 = lean::nat_dec_eq(x_62, x_73);
if (x_74 == 0)
{
obj* x_75; uint8 x_76; 
x_75 = lean::mk_nat_obj(3u);
x_76 = lean::nat_dec_eq(x_62, x_75);
if (x_76 == 0)
{
obj* x_77; uint8 x_78; 
x_77 = lean::mk_nat_obj(4u);
x_78 = lean::nat_dec_eq(x_62, x_77);
lean::dec(x_62);
if (x_78 == 0)
{
if (lean::obj_tag(x_68) == 1)
{
obj* x_79; obj* x_80; 
x_79 = lean::cnstr_get(x_68, 0);
lean::inc(x_79);
lean::dec(x_68);
x_80 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
else
{
obj* x_81; 
lean::dec(x_68);
x_81 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2;
return x_81;
}
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_82 = l_Lean_Parser_number_HasView;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_84 = lean::apply_1(x_83, x_68);
x_85 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_62);
x_86 = l_Lean_Parser_Level_paren_HasView;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::apply_1(x_87, x_68);
x_89 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
else
{
lean::dec(x_62);
if (lean::obj_tag(x_68) == 0)
{
obj* x_90; obj* x_91; obj* x_92; 
x_90 = lean::cnstr_get(x_68, 0);
lean::inc(x_90);
lean::dec(x_68);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
else
{
obj* x_93; 
lean::dec(x_68);
x_93 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3;
return x_93;
}
}
}
else
{
obj* x_94; 
lean::dec(x_62);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_68);
return x_94;
}
}
else
{
obj* x_95; 
lean::dec(x_62);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_68);
return x_95;
}
}
else
{
obj* x_96; 
lean::dec(x_67);
lean::dec(x_62);
lean::dec(x_60);
x_96 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_96;
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
obj* x_97; 
lean::dec(x_11);
lean::dec(x_6);
x_97 = l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4;
return x_97;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_leading_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
lean::inc(x_3);
x_6 = l_Lean_Parser_token(x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_9 = x_6;
} else {
 lean::dec_ref(x_6);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_13 = x_7;
} else {
 lean::dec_ref(x_7);
 x_13 = lean::box(0);
}
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_90; obj* x_91; obj* x_92; 
x_90 = lean::cnstr_get(x_10, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
lean::dec(x_90);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_14 = x_92;
goto block_89;
}
case 1:
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_93 = lean::cnstr_get(x_10, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_93, 1);
lean::inc(x_94);
lean::dec(x_93);
x_95 = l_Lean_Parser_Substring_toString(x_94);
lean::dec(x_94);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
x_14 = x_96;
goto block_89;
}
default: 
{
obj* x_97; 
x_97 = lean::box(0);
x_14 = x_97;
goto block_89;
}
}
block_89:
{
uint8 x_15; 
if (lean::obj_tag(x_14) == 0)
{
uint8 x_84; 
lean::dec(x_14);
x_84 = 1;
x_15 = x_84;
goto block_83;
}
else
{
obj* x_85; uint8 x_86; 
x_85 = lean::cnstr_get(x_14, 0);
lean::inc(x_85);
lean::dec(x_14);
x_86 = lean::string_dec_eq(x_85, x_1);
lean::dec(x_85);
if (x_86 == 0)
{
uint8 x_87; 
x_87 = 1;
x_15 = x_87;
goto block_83;
}
else
{
uint8 x_88; 
x_88 = 0;
x_15 = x_88;
goto block_83;
}
}
block_83:
{
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_16 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_16);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_17);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_18);
x_21 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_20);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_13);
lean::dec(x_9);
x_23 = l_String_quote(x_1);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_4);
x_26 = lean::box(0);
x_27 = l_String_splitAux___main___closed__1;
x_28 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_27, x_24, x_25, x_26, x_3, x_11, x_8);
lean::dec(x_3);
lean::dec(x_25);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_28);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::cnstr_get(x_28, 0);
lean::dec(x_31);
x_32 = !lean::is_exclusive(x_29);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_29, 2);
x_34 = lean::cnstr_get(x_29, 0);
lean::dec(x_34);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_29, 2, x_35);
lean::cnstr_set(x_29, 0, x_10);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_29);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_36);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_37);
x_39 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_38);
lean::cnstr_set(x_28, 0, x_39);
return x_28;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_29, 1);
x_41 = lean::cnstr_get(x_29, 2);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_29);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_10);
lean::cnstr_set(x_43, 1, x_40);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_45);
x_47 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_46);
lean::cnstr_set(x_28, 0, x_47);
return x_28;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_28, 1);
lean::inc(x_48);
lean::dec(x_28);
x_49 = lean::cnstr_get(x_29, 1);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_29, 2);
lean::inc(x_50);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 lean::cnstr_release(x_29, 2);
 x_51 = x_29;
} else {
 lean::dec_ref(x_29);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_10);
lean::cnstr_set(x_53, 1, x_49);
lean::cnstr_set(x_53, 2, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_55);
x_57 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_48);
return x_58;
}
}
else
{
uint8 x_59; 
lean::dec(x_10);
x_59 = !lean::is_exclusive(x_28);
if (x_59 == 0)
{
obj* x_60; uint8 x_61; 
x_60 = lean::cnstr_get(x_28, 0);
lean::dec(x_60);
x_61 = !lean::is_exclusive(x_29);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_29);
x_63 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_62);
x_65 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_64);
lean::cnstr_set(x_28, 0, x_65);
return x_28;
}
else
{
obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_66 = lean::cnstr_get(x_29, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
lean::inc(x_66);
lean::dec(x_29);
x_68 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_67);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_68);
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_69);
x_72 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_71);
lean::cnstr_set(x_28, 0, x_72);
return x_28;
}
}
else
{
obj* x_73; obj* x_74; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_28, 1);
lean::inc(x_73);
lean::dec(x_28);
x_74 = lean::cnstr_get(x_29, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_76 = x_29;
} else {
 lean::dec_ref(x_29);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_75);
x_78 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_77);
x_79 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_78);
x_81 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_73);
return x_82;
}
}
}
}
}
}
else
{
uint8 x_98; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_98 = !lean::is_exclusive(x_6);
if (x_98 == 0)
{
obj* x_99; uint8 x_100; 
x_99 = lean::cnstr_get(x_6, 0);
lean::dec(x_99);
x_100 = !lean::is_exclusive(x_7);
if (x_100 == 0)
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_7);
x_103 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_102);
lean::cnstr_set(x_6, 0, x_103);
return x_6;
}
else
{
obj* x_104; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_7, 0);
x_105 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_104);
lean::dec(x_7);
x_106 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_105);
x_107 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_106);
x_109 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_108);
lean::cnstr_set(x_6, 0, x_109);
return x_6;
}
}
else
{
obj* x_110; obj* x_111; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_110 = lean::cnstr_get(x_6, 1);
lean::inc(x_110);
lean::dec(x_6);
x_111 = lean::cnstr_get(x_7, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_113 = x_7;
} else {
 lean::dec_ref(x_7);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
lean::cnstr_set_scalar(x_114, sizeof(void*)*1, x_112);
x_115 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_114);
x_117 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_116);
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_110);
return x_118;
}
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("identifier");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::obj_tag(x_10) == 1)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_2);
lean::dec(x_1);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_5, 2, x_35);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_36);
x_38 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_39 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_37, x_38);
x_40 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_39);
lean::cnstr_set(x_4, 0, x_40);
return x_4;
}
else
{
obj* x_41; 
lean::free_heap_obj(x_5);
lean::dec(x_10);
lean::free_heap_obj(x_4);
x_41 = lean::box(0);
x_13 = x_41;
goto block_34;
}
block_34:
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
lean::dec(x_13);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_2);
x_15 = lean::box(0);
x_16 = l_String_splitAux___main___closed__1;
x_17 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_16, x_17, x_14, x_15, x_1, x_11, x_7);
lean::dec(x_1);
lean::dec(x_14);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_20);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
x_24 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_23, x_17);
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
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_26);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_28);
x_31 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_30, x_17);
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
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_5, 0);
x_43 = lean::cnstr_get(x_5, 1);
x_44 = lean::cnstr_get(x_5, 2);
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_5);
if (lean::obj_tag(x_42) == 1)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_2);
lean::dec(x_1);
x_61 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_42);
lean::cnstr_set(x_62, 1, x_43);
lean::cnstr_set(x_62, 2, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_61, x_63);
x_65 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_66 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_64, x_65);
x_67 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_66);
lean::cnstr_set(x_4, 0, x_67);
return x_4;
}
else
{
obj* x_68; 
lean::dec(x_42);
lean::free_heap_obj(x_4);
x_68 = lean::box(0);
x_45 = x_68;
goto block_60;
}
block_60:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_45);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_2);
x_47 = lean::box(0);
x_48 = l_String_splitAux___main___closed__1;
x_49 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_50 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_48, x_49, x_46, x_47, x_1, x_43, x_7);
lean::dec(x_1);
lean::dec(x_46);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_50, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 x_53 = x_50;
} else {
 lean::dec_ref(x_50);
 x_53 = lean::box(0);
}
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_51);
x_55 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_54);
x_57 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_56, x_49);
x_58 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_57);
if (lean::is_scalar(x_53)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_53;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_4, 1);
lean::inc(x_69);
lean::dec(x_4);
x_70 = lean::cnstr_get(x_5, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_5, 1);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_5, 2);
lean::inc(x_72);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_73 = x_5;
} else {
 lean::dec_ref(x_5);
 x_73 = lean::box(0);
}
if (lean::obj_tag(x_70) == 1)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_2);
lean::dec(x_1);
x_90 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_73)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_73;
}
lean::cnstr_set(x_91, 0, x_70);
lean::cnstr_set(x_91, 1, x_71);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_91);
x_93 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_92);
x_94 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_95 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_93, x_94);
x_96 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_95);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_69);
return x_97;
}
else
{
obj* x_98; 
lean::dec(x_73);
lean::dec(x_70);
x_98 = lean::box(0);
x_74 = x_98;
goto block_89;
}
block_89:
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_74);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_2);
x_76 = lean::box(0);
x_77 = l_String_splitAux___main___closed__1;
x_78 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_79 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_77, x_78, x_75, x_76, x_1, x_71, x_69);
lean::dec(x_1);
lean::dec(x_75);
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
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_80);
x_84 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_84, x_83);
x_86 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_85, x_78);
x_87 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_86);
if (lean::is_scalar(x_82)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_82;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_81);
return x_88;
}
}
}
else
{
uint8 x_99; 
lean::dec(x_2);
lean::dec(x_1);
x_99 = !lean::is_exclusive(x_4);
if (x_99 == 0)
{
obj* x_100; uint8 x_101; 
x_100 = lean::cnstr_get(x_4, 0);
lean::dec(x_100);
x_101 = !lean::is_exclusive(x_5);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_102 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_102, x_5);
x_104 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_105 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_103, x_104);
x_106 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_105);
lean::cnstr_set(x_4, 0, x_106);
return x_4;
}
else
{
obj* x_107; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_107 = lean::cnstr_get(x_5, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_107);
lean::dec(x_5);
x_109 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_108);
x_110 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_109);
x_112 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_113 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_111, x_112);
x_114 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_113);
lean::cnstr_set(x_4, 0, x_114);
return x_4;
}
}
else
{
obj* x_115; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_115 = lean::cnstr_get(x_4, 1);
lean::inc(x_115);
lean::dec(x_4);
x_116 = lean::cnstr_get(x_5, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_118 = x_5;
} else {
 lean::dec_ref(x_5);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_120, x_119);
x_122 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_123 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_121, x_122);
x_124 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_123);
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_115);
return x_125;
}
}
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(x_8, x_9, x_7, x_7, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_1);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_2, x_14);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_16 = lean::apply_4(x_12, x_3, x_4, x_5, x_6);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_16);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_16, 1);
x_20 = lean::cnstr_get(x_16, 0);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_17);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 2);
x_24 = lean::box(0);
x_25 = lean_name_mk_numeral(x_24, x_2);
x_26 = lean::box(0);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_22);
x_27 = l_Lean_Parser_Syntax_mkNode(x_25, x_1);
x_28 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_17, 2, x_28);
lean::cnstr_set(x_17, 0, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_17);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_29);
return x_16;
}
else
{
uint8 x_30; 
x_30 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (x_30 == 0)
{
obj* x_31; obj* x_32; uint8 x_33; 
lean::free_heap_obj(x_16);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
lean::dec(x_29);
x_32 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_13, x_15, x_3, x_4, x_5, x_19);
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
x_35 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_34);
lean::cnstr_set(x_32, 0, x_35);
return x_32;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_32, 0);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_32);
x_38 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_29);
return x_16;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_40 = lean::cnstr_get(x_17, 0);
x_41 = lean::cnstr_get(x_17, 1);
x_42 = lean::cnstr_get(x_17, 2);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_17);
x_43 = lean::box(0);
x_44 = lean_name_mk_numeral(x_43, x_2);
x_45 = lean::box(0);
lean::cnstr_set(x_1, 1, x_45);
lean::cnstr_set(x_1, 0, x_40);
x_46 = l_Lean_Parser_Syntax_mkNode(x_44, x_1);
x_47 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_41);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_48);
if (lean::obj_tag(x_49) == 0)
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_49);
return x_16;
}
else
{
uint8 x_50; 
x_50 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::free_heap_obj(x_16);
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
lean::dec(x_49);
x_52 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_13, x_15, x_3, x_4, x_5, x_19);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
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
x_56 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_51, x_53);
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
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_49);
return x_16;
}
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_58 = lean::cnstr_get(x_16, 1);
lean::inc(x_58);
lean::dec(x_16);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_17, 1);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_17, 2);
lean::inc(x_61);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 lean::cnstr_release(x_17, 2);
 x_62 = x_17;
} else {
 lean::dec_ref(x_17);
 x_62 = lean::box(0);
}
x_63 = lean::box(0);
x_64 = lean_name_mk_numeral(x_63, x_2);
x_65 = lean::box(0);
lean::cnstr_set(x_1, 1, x_65);
lean::cnstr_set(x_1, 0, x_59);
x_66 = l_Lean_Parser_Syntax_mkNode(x_64, x_1);
x_67 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_60);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_61, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_58);
return x_70;
}
else
{
uint8 x_71; 
x_71 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
lean::dec(x_69);
x_73 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_13, x_15, x_3, x_4, x_5, x_58);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_73, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_76 = x_73;
} else {
 lean::dec_ref(x_73);
 x_76 = lean::box(0);
}
x_77 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_72, x_74);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_75);
return x_78;
}
else
{
obj* x_79; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_69);
lean::cnstr_set(x_79, 1, x_58);
return x_79;
}
}
}
}
else
{
uint8 x_80; 
lean::free_heap_obj(x_1);
lean::dec(x_2);
x_80 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; uint8 x_84; 
x_81 = lean::cnstr_get(x_16, 1);
lean::inc(x_81);
lean::dec(x_16);
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
lean::dec(x_17);
x_83 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_13, x_15, x_3, x_4, x_5, x_81);
x_84 = !lean::is_exclusive(x_83);
if (x_84 == 0)
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_83, 0);
x_86 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_82, x_85);
lean::cnstr_set(x_83, 0, x_86);
return x_83;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_87 = lean::cnstr_get(x_83, 0);
x_88 = lean::cnstr_get(x_83, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_83);
x_89 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_82, x_87);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8 x_91; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_91 = !lean::is_exclusive(x_16);
if (x_91 == 0)
{
obj* x_92; uint8 x_93; 
x_92 = lean::cnstr_get(x_16, 0);
lean::dec(x_92);
x_93 = !lean::is_exclusive(x_17);
if (x_93 == 0)
{
return x_16;
}
else
{
obj* x_94; obj* x_95; 
x_94 = lean::cnstr_get(x_17, 0);
lean::inc(x_94);
lean::dec(x_17);
x_95 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_80);
lean::cnstr_set(x_16, 0, x_95);
return x_16;
}
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_96 = lean::cnstr_get(x_16, 1);
lean::inc(x_96);
lean::dec(x_16);
x_97 = lean::cnstr_get(x_17, 0);
lean::inc(x_97);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_98 = x_17;
} else {
 lean::dec_ref(x_17);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_80);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
return x_100;
}
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_1, 0);
x_102 = lean::cnstr_get(x_1, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_1);
x_103 = lean::mk_nat_obj(1u);
x_104 = lean::nat_add(x_2, x_103);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_105 = lean::apply_4(x_101, x_3, x_4, x_5, x_6);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_107 = lean::cnstr_get(x_105, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_108 = x_105;
} else {
 lean::dec_ref(x_105);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_106, 1);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_106, 2);
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 lean::cnstr_release(x_106, 2);
 x_112 = x_106;
} else {
 lean::dec_ref(x_106);
 x_112 = lean::box(0);
}
x_113 = lean::box(0);
x_114 = lean_name_mk_numeral(x_113, x_2);
x_115 = lean::box(0);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_109);
lean::cnstr_set(x_116, 1, x_115);
x_117 = l_Lean_Parser_Syntax_mkNode(x_114, x_116);
x_118 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_112)) {
 x_119 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_119 = x_112;
}
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_110);
lean::cnstr_set(x_119, 2, x_118);
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_111, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_107);
return x_121;
}
else
{
uint8 x_122; 
x_122 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (x_122 == 0)
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_108);
x_123 = lean::cnstr_get(x_120, 0);
lean::inc(x_123);
lean::dec(x_120);
x_124 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_102, x_104, x_3, x_4, x_5, x_107);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_127 = x_124;
} else {
 lean::dec_ref(x_124);
 x_127 = lean::box(0);
}
x_128 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_123, x_125);
if (lean::is_scalar(x_127)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_127;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_126);
return x_129;
}
else
{
obj* x_130; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_108)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_108;
}
lean::cnstr_set(x_130, 0, x_120);
lean::cnstr_set(x_130, 1, x_107);
return x_130;
}
}
}
else
{
uint8 x_131; 
lean::dec(x_2);
x_131 = lean::cnstr_get_scalar<uint8>(x_106, sizeof(void*)*1);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_132 = lean::cnstr_get(x_105, 1);
lean::inc(x_132);
lean::dec(x_105);
x_133 = lean::cnstr_get(x_106, 0);
lean::inc(x_133);
lean::dec(x_106);
x_134 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_102, x_104, x_3, x_4, x_5, x_132);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
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
x_138 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_133, x_135);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_136);
return x_139;
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_140 = lean::cnstr_get(x_105, 1);
lean::inc(x_140);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_141 = x_105;
} else {
 lean::dec_ref(x_105);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_106, 0);
lean::inc(x_142);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_143 = x_106;
} else {
 lean::dec_ref(x_106);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_142);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_131);
if (lean::is_scalar(x_141)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_141;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_140);
return x_145;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_");
x_3 = l_Lean_Parser_maxPrec;
x_4 = l_Lean_Parser_symbol_tokens___rarg(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_1);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_6);
lean::dec(x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_1);
lean::dec(x_12);
x_14 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
return x_14;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_9;
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_1 = lean::mk_string("max");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::mk_string("imax");
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::mk_string("_");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = l_Lean_Parser_maxPrec;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed), 1, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed), 1, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_Parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
x_23 = l_Lean_Parser_LevelParserM_Monad;
x_24 = l_Lean_Parser_LevelParserM_MonadExcept;
x_25 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_26 = l_Lean_Parser_LevelParserM_Alternative;
x_27 = l_Lean_Parser_Level_leading;
x_28 = l_Lean_Parser_Level_leading_HasView;
x_29 = l_Lean_Parser_Combinators_node_view___rarg(x_23, x_24, x_25, x_26, x_27, x_22, x_28);
lean::dec(x_22);
return x_29;
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::mk_string("max");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::mk_string("imax");
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::mk_string("_");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = l_Lean_Parser_maxPrec;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed), 1, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed), 1, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_Parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
return x_22;
}
}
obj* l_Lean_Parser_Level_leading_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Level_leading;
x_6 = l_Lean_Parser_Level_leading_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_app() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("app");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_Level_app;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
lean::dec(x_5);
x_6 = l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_7);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_9 = lean::box(3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_app_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_app_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_app_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_app_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_app_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(x_1);
x_3 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_4);
lean::dec(x_3);
x_6 = l_Lean_Parser_Level_Lean_Parser_HasTokens;
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_5);
lean::dec(x_5);
x_8 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_maxPrec;
x_7 = l_Lean_Parser_Level_Parser(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_7 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_8 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_9 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_10 = l_Lean_Parser_Level_app;
x_11 = l_Lean_Parser_Level_app_HasView;
x_12 = l_Lean_Parser_Combinators_node_view___rarg(x_6, x_7, x_8, x_9, x_10, x_5, x_11);
lean::dec(x_5);
return x_12;
}
}
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_9 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_68; obj* x_69; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_14 = x_3;
} else {
 lean::dec_ref(x_3);
 x_14 = lean::box(0);
}
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
x_68 = lean::apply_5(x_12, x_4, x_5, x_6, x_7, x_8);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
x_70 = lean::cnstr_get(x_68, 1);
lean::inc(x_70);
lean::dec(x_68);
x_15 = x_69;
x_16 = x_70;
goto block_67;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_71; 
x_71 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_72; uint8 x_73; 
x_72 = lean::cnstr_get(x_68, 1);
lean::inc(x_72);
lean::dec(x_68);
x_73 = !lean::is_exclusive(x_69);
if (x_73 == 0)
{
uint8 x_74; 
x_74 = 0;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_74);
x_15 = x_69;
x_16 = x_72;
goto block_67;
}
else
{
obj* x_75; uint8 x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
lean::dec(x_69);
x_76 = 0;
x_77 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_76);
x_15 = x_77;
x_16 = x_72;
goto block_67;
}
}
else
{
obj* x_78; uint8 x_79; 
x_78 = lean::cnstr_get(x_68, 1);
lean::inc(x_78);
lean::dec(x_68);
x_79 = !lean::is_exclusive(x_69);
if (x_79 == 0)
{
uint8 x_80; 
x_80 = 1;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_80);
x_15 = x_69;
x_16 = x_78;
goto block_67;
}
else
{
obj* x_81; uint8 x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_69, 0);
lean::inc(x_81);
lean::dec(x_69);
x_82 = 1;
x_83 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_82);
x_15 = x_83;
x_16 = x_78;
goto block_67;
}
}
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_69, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_84, 3);
lean::inc(x_85);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; uint8 x_87; 
lean::dec(x_85);
x_86 = lean::cnstr_get(x_68, 1);
lean::inc(x_86);
lean::dec(x_68);
x_87 = !lean::is_exclusive(x_69);
if (x_87 == 0)
{
uint8 x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
x_89 = lean::cnstr_get(x_69, 0);
lean::dec(x_89);
x_90 = !lean::is_exclusive(x_84);
if (x_90 == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_91 = lean::cnstr_get(x_84, 3);
lean::dec(x_91);
x_92 = lean::box(3);
lean::inc(x_2);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_2);
x_94 = l_List_reverse___rarg(x_93);
lean::inc(x_1);
x_95 = l_Lean_Parser_Syntax_mkNode(x_1, x_94);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_84, 3, x_96);
if (x_88 == 0)
{
uint8 x_97; 
x_97 = 0;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_97);
x_15 = x_69;
x_16 = x_86;
goto block_67;
}
else
{
uint8 x_98; 
x_98 = 1;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_98);
x_15 = x_69;
x_16 = x_86;
goto block_67;
}
}
else
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_99 = lean::cnstr_get(x_84, 0);
x_100 = lean::cnstr_get(x_84, 1);
x_101 = lean::cnstr_get(x_84, 2);
lean::inc(x_101);
lean::inc(x_100);
lean::inc(x_99);
lean::dec(x_84);
x_102 = lean::box(3);
lean::inc(x_2);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_2);
x_104 = l_List_reverse___rarg(x_103);
lean::inc(x_1);
x_105 = l_Lean_Parser_Syntax_mkNode(x_1, x_104);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
x_107 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_107, 0, x_99);
lean::cnstr_set(x_107, 1, x_100);
lean::cnstr_set(x_107, 2, x_101);
lean::cnstr_set(x_107, 3, x_106);
if (x_88 == 0)
{
uint8 x_108; 
x_108 = 0;
lean::cnstr_set(x_69, 0, x_107);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_108);
x_15 = x_69;
x_16 = x_86;
goto block_67;
}
else
{
uint8 x_109; 
x_109 = 1;
lean::cnstr_set(x_69, 0, x_107);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_109);
x_15 = x_69;
x_16 = x_86;
goto block_67;
}
}
}
else
{
uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_110 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
lean::dec(x_69);
x_111 = lean::cnstr_get(x_84, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_84, 1);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_84, 2);
lean::inc(x_113);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 lean::cnstr_release(x_84, 2);
 lean::cnstr_release(x_84, 3);
 x_114 = x_84;
} else {
 lean::dec_ref(x_84);
 x_114 = lean::box(0);
}
x_115 = lean::box(3);
lean::inc(x_2);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_2);
x_117 = l_List_reverse___rarg(x_116);
lean::inc(x_1);
x_118 = l_Lean_Parser_Syntax_mkNode(x_1, x_117);
x_119 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_119, 0, x_118);
if (lean::is_scalar(x_114)) {
 x_120 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_120 = x_114;
}
lean::cnstr_set(x_120, 0, x_111);
lean::cnstr_set(x_120, 1, x_112);
lean::cnstr_set(x_120, 2, x_113);
lean::cnstr_set(x_120, 3, x_119);
if (x_110 == 0)
{
uint8 x_121; obj* x_122; 
x_121 = 0;
x_122 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_121);
x_15 = x_122;
x_16 = x_86;
goto block_67;
}
else
{
uint8 x_123; obj* x_124; 
x_123 = 1;
x_124 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_123);
x_15 = x_124;
x_16 = x_86;
goto block_67;
}
}
}
else
{
obj* x_125; uint8 x_126; 
x_125 = lean::cnstr_get(x_68, 1);
lean::inc(x_125);
lean::dec(x_68);
x_126 = !lean::is_exclusive(x_69);
if (x_126 == 0)
{
uint8 x_127; obj* x_128; uint8 x_129; 
x_127 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
x_128 = lean::cnstr_get(x_69, 0);
lean::dec(x_128);
x_129 = !lean::is_exclusive(x_84);
if (x_129 == 0)
{
obj* x_130; uint8 x_131; 
x_130 = lean::cnstr_get(x_84, 3);
lean::dec(x_130);
x_131 = !lean::is_exclusive(x_85);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_132 = lean::cnstr_get(x_85, 0);
lean::inc(x_2);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_2);
x_134 = l_List_reverse___rarg(x_133);
lean::inc(x_1);
x_135 = l_Lean_Parser_Syntax_mkNode(x_1, x_134);
lean::cnstr_set(x_85, 0, x_135);
if (x_127 == 0)
{
uint8 x_136; 
x_136 = 0;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_136);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
else
{
uint8 x_137; 
x_137 = 1;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_137);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
}
else
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_138 = lean::cnstr_get(x_85, 0);
lean::inc(x_138);
lean::dec(x_85);
lean::inc(x_2);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_2);
x_140 = l_List_reverse___rarg(x_139);
lean::inc(x_1);
x_141 = l_Lean_Parser_Syntax_mkNode(x_1, x_140);
x_142 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_84, 3, x_142);
if (x_127 == 0)
{
uint8 x_143; 
x_143 = 0;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_143);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
else
{
uint8 x_144; 
x_144 = 1;
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_144);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_145 = lean::cnstr_get(x_84, 0);
x_146 = lean::cnstr_get(x_84, 1);
x_147 = lean::cnstr_get(x_84, 2);
lean::inc(x_147);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_84);
x_148 = lean::cnstr_get(x_85, 0);
lean::inc(x_148);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_149 = x_85;
} else {
 lean::dec_ref(x_85);
 x_149 = lean::box(0);
}
lean::inc(x_2);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_148);
lean::cnstr_set(x_150, 1, x_2);
x_151 = l_List_reverse___rarg(x_150);
lean::inc(x_1);
x_152 = l_Lean_Parser_Syntax_mkNode(x_1, x_151);
if (lean::is_scalar(x_149)) {
 x_153 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_153 = x_149;
}
lean::cnstr_set(x_153, 0, x_152);
x_154 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_154, 0, x_145);
lean::cnstr_set(x_154, 1, x_146);
lean::cnstr_set(x_154, 2, x_147);
lean::cnstr_set(x_154, 3, x_153);
if (x_127 == 0)
{
uint8 x_155; 
x_155 = 0;
lean::cnstr_set(x_69, 0, x_154);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_155);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
else
{
uint8 x_156; 
x_156 = 1;
lean::cnstr_set(x_69, 0, x_154);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_156);
x_15 = x_69;
x_16 = x_125;
goto block_67;
}
}
}
else
{
uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_157 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
lean::dec(x_69);
x_158 = lean::cnstr_get(x_84, 0);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_84, 1);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_84, 2);
lean::inc(x_160);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 lean::cnstr_release(x_84, 2);
 lean::cnstr_release(x_84, 3);
 x_161 = x_84;
} else {
 lean::dec_ref(x_84);
 x_161 = lean::box(0);
}
x_162 = lean::cnstr_get(x_85, 0);
lean::inc(x_162);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_163 = x_85;
} else {
 lean::dec_ref(x_85);
 x_163 = lean::box(0);
}
lean::inc(x_2);
x_164 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_164, 0, x_162);
lean::cnstr_set(x_164, 1, x_2);
x_165 = l_List_reverse___rarg(x_164);
lean::inc(x_1);
x_166 = l_Lean_Parser_Syntax_mkNode(x_1, x_165);
if (lean::is_scalar(x_163)) {
 x_167 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_167 = x_163;
}
lean::cnstr_set(x_167, 0, x_166);
if (lean::is_scalar(x_161)) {
 x_168 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_168 = x_161;
}
lean::cnstr_set(x_168, 0, x_158);
lean::cnstr_set(x_168, 1, x_159);
lean::cnstr_set(x_168, 2, x_160);
lean::cnstr_set(x_168, 3, x_167);
if (x_157 == 0)
{
uint8 x_169; obj* x_170; 
x_169 = 0;
x_170 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_170, 0, x_168);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_169);
x_15 = x_170;
x_16 = x_125;
goto block_67;
}
else
{
uint8 x_171; obj* x_172; 
x_171 = 1;
x_172 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set_scalar(x_172, sizeof(void*)*1, x_171);
x_15 = x_172;
x_16 = x_125;
goto block_67;
}
}
}
}
}
block_67:
{
if (lean::obj_tag(x_15) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_15, 0);
x_19 = lean::cnstr_get(x_15, 2);
if (lean::is_scalar(x_14)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_14;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_15, 2, x_21);
lean::cnstr_set(x_15, 0, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_15);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_22, 2);
lean::inc(x_25);
lean::dec(x_22);
x_26 = l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(x_1, x_23, x_13, x_4, x_5, x_6, x_24, x_16);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_28);
lean::cnstr_set(x_26, 0, x_29);
return x_26;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_26);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8 x_34; 
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_34 = !lean::is_exclusive(x_22);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_16);
return x_35;
}
else
{
obj* x_36; uint8 x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_22, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
lean::inc(x_36);
lean::dec(x_22);
x_38 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_16);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_40 = lean::cnstr_get(x_15, 0);
x_41 = lean::cnstr_get(x_15, 1);
x_42 = lean::cnstr_get(x_15, 2);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_15);
if (lean::is_scalar(x_14)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_14;
}
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_2);
x_44 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_41);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_46, 2);
lean::inc(x_49);
lean::dec(x_46);
x_50 = l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(x_1, x_47, x_13, x_4, x_5, x_6, x_48, x_16);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_50, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 x_53 = x_50;
} else {
 lean::dec_ref(x_50);
 x_53 = lean::box(0);
}
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_51);
if (lean::is_scalar(x_53)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_53;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_52);
return x_55;
}
else
{
obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_46, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_58 = x_46;
} else {
 lean::dec_ref(x_46);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_16);
return x_60;
}
}
}
else
{
uint8 x_61; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_61 = !lean::is_exclusive(x_15);
if (x_61 == 0)
{
obj* x_62; 
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_15);
lean::cnstr_set(x_62, 1, x_16);
return x_62;
}
else
{
obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_63 = lean::cnstr_get(x_15, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
lean::inc(x_63);
lean::dec(x_15);
x_65 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_16);
return x_66;
}
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::box(0);
lean::inc(x_1);
x_9 = l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_9, 0);
lean::dec(x_12);
x_13 = !lean::is_exclusive(x_10);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 2);
x_16 = l_List_reverse___rarg(x_14);
x_17 = l_Lean_Parser_Syntax_mkNode(x_1, x_16);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_10, 2, x_18);
lean::cnstr_set(x_10, 0, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_10);
lean::cnstr_set(x_9, 0, x_19);
return x_9;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_10, 0);
x_21 = lean::cnstr_get(x_10, 1);
x_22 = lean::cnstr_get(x_10, 2);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_10);
x_23 = l_List_reverse___rarg(x_20);
x_24 = l_Lean_Parser_Syntax_mkNode(x_1, x_23);
x_25 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_21);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_26);
lean::cnstr_set(x_9, 0, x_27);
return x_9;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_28 = lean::cnstr_get(x_9, 1);
lean::inc(x_28);
lean::dec(x_9);
x_29 = lean::cnstr_get(x_10, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_10, 1);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_10, 2);
lean::inc(x_31);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_32 = x_10;
} else {
 lean::dec_ref(x_10);
 x_32 = lean::box(0);
}
x_33 = l_List_reverse___rarg(x_29);
x_34 = l_Lean_Parser_Syntax_mkNode(x_1, x_33);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_32)) {
 x_36 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_36 = x_32;
}
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_30);
lean::cnstr_set(x_36, 2, x_35);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_28);
return x_38;
}
}
else
{
uint8 x_39; 
lean::dec(x_1);
x_39 = !lean::is_exclusive(x_9);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = lean::cnstr_get(x_9, 0);
lean::dec(x_40);
x_41 = !lean::is_exclusive(x_10);
if (x_41 == 0)
{
return x_9;
}
else
{
obj* x_42; uint8 x_43; obj* x_44; 
x_42 = lean::cnstr_get(x_10, 0);
x_43 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_42);
lean::dec(x_10);
x_44 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_43);
lean::cnstr_set(x_9, 0, x_44);
return x_9;
}
}
else
{
obj* x_45; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_9, 1);
lean::inc(x_45);
lean::dec(x_9);
x_46 = lean::cnstr_get(x_10, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_48 = x_10;
} else {
 lean::dec_ref(x_10);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_47);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_45);
return x_50;
}
}
}
}
obj* _init_l_Lean_Parser_Level_app_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_Parser_Level_app_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Level_app;
x_7 = l_Lean_Parser_Level_app_Parser___closed__1;
x_8 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_addLit() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("addLit");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_addLit_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_number_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_4);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
if (lean::obj_tag(x_3) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_3);
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_Level_addLit;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_9);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_2);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_Level_addLit;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_number_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Level_addLit_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_28; 
x_28 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
lean::dec(x_28);
x_29 = l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2;
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = lean::box(3);
x_2 = x_31;
x_3 = x_32;
goto block_27;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_2 = x_34;
x_3 = x_33;
goto block_27;
}
}
block_27:
{
obj* x_4; obj* x_5; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_4 = x_2;
x_5 = x_24;
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
x_4 = x_26;
x_5 = x_25;
goto block_23;
}
block_23:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_4);
x_8 = l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_Lean_Parser_number_HasView;
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::apply_1(x_12, x_10);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_5);
x_15 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set(x_17, 2, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_19 = l_Lean_Parser_number_HasView;
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_21 = lean::apply_1(x_20, x_18);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_3);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_addLit_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_9, 0, x_1);
lean::inc(x_7);
lean::inc(x_6);
x_10 = l_Lean_Parser_token(x_6, x_7, x_8);
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
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
x_17 = lean::cnstr_get(x_11, 1);
x_18 = lean::cnstr_get(x_11, 2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_40; obj* x_41; uint8 x_42; 
x_40 = lean::cnstr_get(x_16, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_42 = lean::string_dec_eq(x_1, x_41);
lean::dec(x_1);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::free_heap_obj(x_11);
lean::free_heap_obj(x_10);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_7);
x_44 = lean::box(0);
x_45 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_41, x_3, x_43, x_44, x_6, x_17, x_13);
lean::dec(x_6);
lean::dec(x_43);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_45);
if (x_47 == 0)
{
obj* x_48; uint8 x_49; 
x_48 = lean::cnstr_get(x_45, 0);
lean::dec(x_48);
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = lean::cnstr_get(x_46, 2);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_46, 2, x_52);
lean::cnstr_set(x_46, 0, x_16);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_46);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_54);
x_56 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_55, x_9);
x_57 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_56);
lean::cnstr_set(x_45, 0, x_57);
return x_45;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_58 = lean::cnstr_get(x_46, 1);
x_59 = lean::cnstr_get(x_46, 2);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_46);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_16);
lean::cnstr_set(x_61, 1, x_58);
lean::cnstr_set(x_61, 2, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_63);
x_65 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_64, x_9);
x_66 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_65);
lean::cnstr_set(x_45, 0, x_66);
return x_45;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_67 = lean::cnstr_get(x_45, 1);
lean::inc(x_67);
lean::dec(x_45);
x_68 = lean::cnstr_get(x_46, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_46, 2);
lean::inc(x_69);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 lean::cnstr_release(x_46, 2);
 x_70 = x_46;
} else {
 lean::dec_ref(x_46);
 x_70 = lean::box(0);
}
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_16);
lean::cnstr_set(x_72, 1, x_68);
lean::cnstr_set(x_72, 2, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_73);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_74);
x_76 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_75, x_9);
x_77 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_67);
return x_78;
}
}
else
{
uint8 x_79; 
lean::dec(x_16);
x_79 = !lean::is_exclusive(x_45);
if (x_79 == 0)
{
obj* x_80; uint8 x_81; 
x_80 = lean::cnstr_get(x_45, 0);
lean::dec(x_80);
x_81 = !lean::is_exclusive(x_46);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_46);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_82);
x_85 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_84, x_9);
x_86 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_85);
lean::cnstr_set(x_45, 0, x_86);
return x_45;
}
else
{
obj* x_87; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_87 = lean::cnstr_get(x_46, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
lean::inc(x_87);
lean::dec(x_46);
x_89 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_88);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_89);
x_91 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_90);
x_93 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_92, x_9);
x_94 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_93);
lean::cnstr_set(x_45, 0, x_94);
return x_45;
}
}
else
{
obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_45, 1);
lean::inc(x_95);
lean::dec(x_45);
x_96 = lean::cnstr_get(x_46, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_98 = x_46;
} else {
 lean::dec_ref(x_46);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_99);
x_101 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_100);
x_103 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_102, x_9);
x_104 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_103);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_95);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_41);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
x_106 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_11, 2, x_106);
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_11);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_108, x_107);
x_110 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_109, x_9);
x_111 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_110);
lean::cnstr_set(x_10, 0, x_111);
return x_10;
}
}
else
{
obj* x_112; 
lean::free_heap_obj(x_11);
lean::dec(x_16);
lean::free_heap_obj(x_10);
lean::dec(x_1);
x_112 = lean::box(0);
x_19 = x_112;
goto block_39;
}
block_39:
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
lean::dec(x_19);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_7);
x_21 = lean::box(0);
x_22 = l_String_splitAux___main___closed__1;
x_23 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_22, x_3, x_20, x_21, x_6, x_17, x_13);
lean::dec(x_6);
lean::dec(x_20);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_23, 0);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_25);
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_26);
x_29 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_28, x_9);
x_30 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_29);
lean::cnstr_set(x_23, 0, x_30);
return x_23;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_23, 0);
x_32 = lean::cnstr_get(x_23, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_23);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_31);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_33);
x_36 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_35, x_9);
x_37 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_113 = lean::cnstr_get(x_11, 0);
x_114 = lean::cnstr_get(x_11, 1);
x_115 = lean::cnstr_get(x_11, 2);
lean::inc(x_115);
lean::inc(x_114);
lean::inc(x_113);
lean::dec(x_11);
if (lean::obj_tag(x_113) == 0)
{
obj* x_131; obj* x_132; uint8 x_133; 
x_131 = lean::cnstr_get(x_113, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_131, 1);
lean::inc(x_132);
lean::dec(x_131);
x_133 = lean::string_dec_eq(x_1, x_132);
lean::dec(x_1);
if (x_133 == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::free_heap_obj(x_10);
x_134 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_134, 0, x_7);
x_135 = lean::box(0);
x_136 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_132, x_3, x_134, x_135, x_6, x_114, x_13);
lean::dec(x_6);
lean::dec(x_134);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_138 = lean::cnstr_get(x_136, 1);
lean::inc(x_138);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_139 = x_136;
} else {
 lean::dec_ref(x_136);
 x_139 = lean::box(0);
}
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_137, 2);
lean::inc(x_141);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 lean::cnstr_release(x_137, 2);
 x_142 = x_137;
} else {
 lean::dec_ref(x_137);
 x_142 = lean::box(0);
}
x_143 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_142)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_142;
}
lean::cnstr_set(x_144, 0, x_113);
lean::cnstr_set(x_144, 1, x_140);
lean::cnstr_set(x_144, 2, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_144);
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_145);
x_147 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_143, x_146);
x_148 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_147, x_9);
x_149 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_148);
if (lean::is_scalar(x_139)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_139;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_138);
return x_150;
}
else
{
obj* x_151; obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_113);
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
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_156);
x_158 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_158, x_157);
x_160 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_159, x_9);
x_161 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_160);
if (lean::is_scalar(x_152)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_152;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_151);
return x_162;
}
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_132);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
x_163 = l_Lean_Parser_finishCommentBlock___closed__2;
x_164 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_164, 0, x_113);
lean::cnstr_set(x_164, 1, x_114);
lean::cnstr_set(x_164, 2, x_163);
x_165 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_164);
x_166 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_167 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_166, x_165);
x_168 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_167, x_9);
x_169 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_168);
lean::cnstr_set(x_10, 0, x_169);
return x_10;
}
}
else
{
obj* x_170; 
lean::dec(x_113);
lean::free_heap_obj(x_10);
lean::dec(x_1);
x_170 = lean::box(0);
x_116 = x_170;
goto block_130;
}
block_130:
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_116);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_7);
x_118 = lean::box(0);
x_119 = l_String_splitAux___main___closed__1;
x_120 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_119, x_3, x_117, x_118, x_6, x_114, x_13);
lean::dec(x_6);
lean::dec(x_117);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_120, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_123 = x_120;
} else {
 lean::dec_ref(x_120);
 x_123 = lean::box(0);
}
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_121);
x_125 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_125, x_124);
x_127 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_126, x_9);
x_128 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_127);
if (lean::is_scalar(x_123)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_123;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_122);
return x_129;
}
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_171 = lean::cnstr_get(x_10, 1);
lean::inc(x_171);
lean::dec(x_10);
x_172 = lean::cnstr_get(x_11, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_11, 1);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_11, 2);
lean::inc(x_174);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_175 = x_11;
} else {
 lean::dec_ref(x_11);
 x_175 = lean::box(0);
}
if (lean::obj_tag(x_172) == 0)
{
obj* x_191; obj* x_192; uint8 x_193; 
x_191 = lean::cnstr_get(x_172, 0);
lean::inc(x_191);
x_192 = lean::cnstr_get(x_191, 1);
lean::inc(x_192);
lean::dec(x_191);
x_193 = lean::string_dec_eq(x_1, x_192);
lean::dec(x_1);
if (x_193 == 0)
{
obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
lean::dec(x_175);
x_194 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_194, 0, x_7);
x_195 = lean::box(0);
x_196 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_192, x_3, x_194, x_195, x_6, x_173, x_171);
lean::dec(x_6);
lean::dec(x_194);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_198 = lean::cnstr_get(x_196, 1);
lean::inc(x_198);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_199 = x_196;
} else {
 lean::dec_ref(x_196);
 x_199 = lean::box(0);
}
x_200 = lean::cnstr_get(x_197, 1);
lean::inc(x_200);
x_201 = lean::cnstr_get(x_197, 2);
lean::inc(x_201);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 lean::cnstr_release(x_197, 2);
 x_202 = x_197;
} else {
 lean::dec_ref(x_197);
 x_202 = lean::box(0);
}
x_203 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_202)) {
 x_204 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_204 = x_202;
}
lean::cnstr_set(x_204, 0, x_172);
lean::cnstr_set(x_204, 1, x_200);
lean::cnstr_set(x_204, 2, x_203);
x_205 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_201, x_204);
x_206 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_205);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_203, x_206);
x_208 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_207, x_9);
x_209 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_208);
if (lean::is_scalar(x_199)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_199;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_198);
return x_210;
}
else
{
obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_172);
x_211 = lean::cnstr_get(x_196, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_212 = x_196;
} else {
 lean::dec_ref(x_196);
 x_212 = lean::box(0);
}
x_213 = lean::cnstr_get(x_197, 0);
lean::inc(x_213);
x_214 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*1);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 x_215 = x_197;
} else {
 lean::dec_ref(x_197);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
lean::cnstr_set_scalar(x_216, sizeof(void*)*1, x_214);
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_216);
x_218 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_219 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_218, x_217);
x_220 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_219, x_9);
x_221 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_220);
if (lean::is_scalar(x_212)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_212;
}
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_211);
return x_222;
}
}
else
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; 
lean::dec(x_192);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
x_223 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_175)) {
 x_224 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_224 = x_175;
}
lean::cnstr_set(x_224, 0, x_172);
lean::cnstr_set(x_224, 1, x_173);
lean::cnstr_set(x_224, 2, x_223);
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_224);
x_226 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_227 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_226, x_225);
x_228 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_227, x_9);
x_229 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_228);
x_230 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_171);
return x_230;
}
}
else
{
obj* x_231; 
lean::dec(x_175);
lean::dec(x_172);
lean::dec(x_1);
x_231 = lean::box(0);
x_176 = x_231;
goto block_190;
}
block_190:
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
lean::dec(x_176);
x_177 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_177, 0, x_7);
x_178 = lean::box(0);
x_179 = l_String_splitAux___main___closed__1;
x_180 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_179, x_3, x_177, x_178, x_6, x_173, x_171);
lean::dec(x_6);
lean::dec(x_177);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_180, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_183 = x_180;
} else {
 lean::dec_ref(x_180);
 x_183 = lean::box(0);
}
x_184 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_181);
x_185 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_186 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_185, x_184);
x_187 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_186, x_9);
x_188 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_187);
if (lean::is_scalar(x_183)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_183;
}
lean::cnstr_set(x_189, 0, x_188);
lean::cnstr_set(x_189, 1, x_182);
return x_189;
}
}
}
else
{
uint8 x_232; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_232 = !lean::is_exclusive(x_10);
if (x_232 == 0)
{
obj* x_233; uint8 x_234; 
x_233 = lean::cnstr_get(x_10, 0);
lean::dec(x_233);
x_234 = !lean::is_exclusive(x_11);
if (x_234 == 0)
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
x_235 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_236 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_235, x_11);
x_237 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_236, x_9);
x_238 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_237);
lean::cnstr_set(x_10, 0, x_238);
return x_10;
}
else
{
obj* x_239; uint8 x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_239 = lean::cnstr_get(x_11, 0);
x_240 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_239);
lean::dec(x_11);
x_241 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_241, 0, x_239);
lean::cnstr_set_scalar(x_241, sizeof(void*)*1, x_240);
x_242 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_243 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_242, x_241);
x_244 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_243, x_9);
x_245 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_244);
lean::cnstr_set(x_10, 0, x_245);
return x_10;
}
}
else
{
obj* x_246; obj* x_247; uint8 x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_246 = lean::cnstr_get(x_10, 1);
lean::inc(x_246);
lean::dec(x_10);
x_247 = lean::cnstr_get(x_11, 0);
lean::inc(x_247);
x_248 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_249 = x_11;
} else {
 lean::dec_ref(x_11);
 x_249 = lean::box(0);
}
if (lean::is_scalar(x_249)) {
 x_250 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_250 = x_249;
}
lean::cnstr_set(x_250, 0, x_247);
lean::cnstr_set_scalar(x_250, sizeof(void*)*1, x_248);
x_251 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_252 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_251, x_250);
x_253 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_252, x_9);
x_254 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_253);
x_255 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_246);
return x_255;
}
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___rarg), 3, 0);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("+");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_4);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_5);
lean::dec(x_5);
lean::dec(x_3);
x_7 = l_Lean_Parser_Level_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_6);
lean::dec(x_6);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_9;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_9;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_1 = lean::mk_string("+");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_13 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_14 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_15 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_16 = l_Lean_Parser_Level_addLit;
x_17 = l_Lean_Parser_Level_addLit_HasView;
x_18 = l_Lean_Parser_Combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
lean::dec(x_11);
return x_18;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("+");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
obj* l_Lean_Parser_Level_addLit_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Level_addLit;
x_7 = l_Lean_Parser_Level_addLit_Parser___closed__1;
x_8 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_trailing() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("trailing");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_trailing_HasView_x27___elambda__1(obj* x_1) {
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
x_4 = l_Lean_Parser_Level_app_HasView;
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
x_11 = l_Lean_Parser_Level_trailing;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Lean_Parser_Level_addLit_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_Level_trailing;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Level_app_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Level");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("trailing");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Level_trailing_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
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
x_7 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
x_10 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
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
x_14 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_17; 
lean::dec(x_16);
lean::dec(x_15);
x_17 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_17;
}
case 1:
{
obj* x_18; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_18;
}
default: 
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_20, x_22);
lean::dec(x_20);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_21);
lean::dec(x_19);
x_24 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; 
lean::dec(x_21);
lean::dec(x_19);
x_25 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
lean::dec(x_26);
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::nat_dec_eq(x_21, x_28);
lean::dec(x_21);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = l_Lean_Parser_Level_addLit_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::apply_1(x_31, x_27);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = l_Lean_Parser_Level_app_HasView;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_27);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
else
{
obj* x_38; 
lean::dec(x_26);
lean::dec(x_21);
lean::dec(x_19);
x_38 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_38;
}
}
}
}
}
}
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_6);
x_39 = l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1;
return x_39;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_trailing_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_4);
x_11 = 0;
x_12 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
lean::dec(x_8);
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
lean::cnstr_set(x_15, 2, x_2);
lean::cnstr_set(x_15, 3, x_4);
x_16 = 0;
x_17 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_9, x_10, x_8, x_8, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_11;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_2, x_15);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_17 = lean::apply_5(x_13, x_3, x_4, x_5, x_6, x_7);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_17);
if (x_19 == 0)
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = lean::cnstr_get(x_17, 1);
x_21 = lean::cnstr_get(x_17, 0);
lean::dec(x_21);
x_22 = !lean::is_exclusive(x_18);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = lean::cnstr_get(x_18, 2);
x_25 = lean::box(0);
x_26 = lean_name_mk_numeral(x_25, x_2);
x_27 = lean::box(0);
lean::cnstr_set(x_1, 1, x_27);
lean::cnstr_set(x_1, 0, x_23);
x_28 = l_Lean_Parser_Syntax_mkNode(x_26, x_1);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_18, 2, x_29);
lean::cnstr_set(x_18, 0, x_28);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_18);
if (lean::obj_tag(x_30) == 0)
{
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_17, 0, x_30);
return x_17;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_33; uint8 x_34; 
lean::free_heap_obj(x_17);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::dec(x_30);
x_33 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_14, x_16, x_3, x_4, x_5, x_6, x_20);
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_33, 0);
x_36 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_32, x_35);
lean::cnstr_set(x_33, 0, x_36);
return x_33;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_33);
x_39 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_32, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_17, 0, x_30);
return x_17;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_41 = lean::cnstr_get(x_18, 0);
x_42 = lean::cnstr_get(x_18, 1);
x_43 = lean::cnstr_get(x_18, 2);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_18);
x_44 = lean::box(0);
x_45 = lean_name_mk_numeral(x_44, x_2);
x_46 = lean::box(0);
lean::cnstr_set(x_1, 1, x_46);
lean::cnstr_set(x_1, 0, x_41);
x_47 = l_Lean_Parser_Syntax_mkNode(x_45, x_1);
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_42);
lean::cnstr_set(x_49, 2, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_49);
if (lean::obj_tag(x_50) == 0)
{
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_17, 0, x_50);
return x_17;
}
else
{
uint8 x_51; 
x_51 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::free_heap_obj(x_17);
x_52 = lean::cnstr_get(x_50, 0);
lean::inc(x_52);
lean::dec(x_50);
x_53 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_14, x_16, x_3, x_4, x_5, x_6, x_20);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_56 = x_53;
} else {
 lean::dec_ref(x_53);
 x_56 = lean::box(0);
}
x_57 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_52, x_54);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_55);
return x_58;
}
else
{
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_17, 0, x_50);
return x_17;
}
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_59 = lean::cnstr_get(x_17, 1);
lean::inc(x_59);
lean::dec(x_17);
x_60 = lean::cnstr_get(x_18, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_18, 1);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_18, 2);
lean::inc(x_62);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 x_63 = x_18;
} else {
 lean::dec_ref(x_18);
 x_63 = lean::box(0);
}
x_64 = lean::box(0);
x_65 = lean_name_mk_numeral(x_64, x_2);
x_66 = lean::box(0);
lean::cnstr_set(x_1, 1, x_66);
lean::cnstr_set(x_1, 0, x_60);
x_67 = l_Lean_Parser_Syntax_mkNode(x_65, x_1);
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_63)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_63;
}
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_61);
lean::cnstr_set(x_69, 2, x_68);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; 
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_59);
return x_71;
}
else
{
uint8 x_72; 
x_72 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_74 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_14, x_16, x_3, x_4, x_5, x_6, x_59);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_74, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 lean::cnstr_release(x_74, 1);
 x_77 = x_74;
} else {
 lean::dec_ref(x_74);
 x_77 = lean::box(0);
}
x_78 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_73, x_75);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
return x_79;
}
else
{
obj* x_80; 
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_70);
lean::cnstr_set(x_80, 1, x_59);
return x_80;
}
}
}
}
else
{
uint8 x_81; 
lean::free_heap_obj(x_1);
lean::dec(x_2);
x_81 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; uint8 x_85; 
x_82 = lean::cnstr_get(x_17, 1);
lean::inc(x_82);
lean::dec(x_17);
x_83 = lean::cnstr_get(x_18, 0);
lean::inc(x_83);
lean::dec(x_18);
x_84 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_14, x_16, x_3, x_4, x_5, x_6, x_82);
x_85 = !lean::is_exclusive(x_84);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_84, 0);
x_87 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_83, x_86);
lean::cnstr_set(x_84, 0, x_87);
return x_84;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get(x_84, 0);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_84);
x_90 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_83, x_88);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8 x_92; 
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_92 = !lean::is_exclusive(x_17);
if (x_92 == 0)
{
obj* x_93; uint8 x_94; 
x_93 = lean::cnstr_get(x_17, 0);
lean::dec(x_93);
x_94 = !lean::is_exclusive(x_18);
if (x_94 == 0)
{
return x_17;
}
else
{
obj* x_95; obj* x_96; 
x_95 = lean::cnstr_get(x_18, 0);
lean::inc(x_95);
lean::dec(x_18);
x_96 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_81);
lean::cnstr_set(x_17, 0, x_96);
return x_17;
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_97 = lean::cnstr_get(x_17, 1);
lean::inc(x_97);
lean::dec(x_17);
x_98 = lean::cnstr_get(x_18, 0);
lean::inc(x_98);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_99 = x_18;
} else {
 lean::dec_ref(x_18);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_81);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
return x_101;
}
}
}
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_102 = lean::cnstr_get(x_1, 0);
x_103 = lean::cnstr_get(x_1, 1);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_1);
x_104 = lean::mk_nat_obj(1u);
x_105 = lean::nat_add(x_2, x_104);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_106 = lean::apply_5(x_102, x_3, x_4, x_5, x_6, x_7);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_108 = lean::cnstr_get(x_106, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_109 = x_106;
} else {
 lean::dec_ref(x_106);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_107, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_107, 1);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_107, 2);
lean::inc(x_112);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_release(x_107, 0);
 lean::cnstr_release(x_107, 1);
 lean::cnstr_release(x_107, 2);
 x_113 = x_107;
} else {
 lean::dec_ref(x_107);
 x_113 = lean::box(0);
}
x_114 = lean::box(0);
x_115 = lean_name_mk_numeral(x_114, x_2);
x_116 = lean::box(0);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_110);
lean::cnstr_set(x_117, 1, x_116);
x_118 = l_Lean_Parser_Syntax_mkNode(x_115, x_117);
x_119 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_113)) {
 x_120 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_120 = x_113;
}
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_111);
lean::cnstr_set(x_120, 2, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_120);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; 
lean::dec(x_105);
lean::dec(x_103);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_109)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_109;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_108);
return x_122;
}
else
{
uint8 x_123; 
x_123 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
if (x_123 == 0)
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_109);
x_124 = lean::cnstr_get(x_121, 0);
lean::inc(x_124);
lean::dec(x_121);
x_125 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_103, x_105, x_3, x_4, x_5, x_6, x_108);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_128 = x_125;
} else {
 lean::dec_ref(x_125);
 x_128 = lean::box(0);
}
x_129 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_124, x_126);
if (lean::is_scalar(x_128)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_128;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_127);
return x_130;
}
else
{
obj* x_131; 
lean::dec(x_105);
lean::dec(x_103);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_109)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_109;
}
lean::cnstr_set(x_131, 0, x_121);
lean::cnstr_set(x_131, 1, x_108);
return x_131;
}
}
}
else
{
uint8 x_132; 
lean::dec(x_2);
x_132 = lean::cnstr_get_scalar<uint8>(x_107, sizeof(void*)*1);
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_133 = lean::cnstr_get(x_106, 1);
lean::inc(x_133);
lean::dec(x_106);
x_134 = lean::cnstr_get(x_107, 0);
lean::inc(x_134);
lean::dec(x_107);
x_135 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_103, x_105, x_3, x_4, x_5, x_6, x_133);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_135, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_138 = x_135;
} else {
 lean::dec_ref(x_135);
 x_138 = lean::box(0);
}
x_139 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_134, x_136);
if (lean::is_scalar(x_138)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_138;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_105);
lean::dec(x_103);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_141 = lean::cnstr_get(x_106, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_142 = x_106;
} else {
 lean::dec_ref(x_106);
 x_142 = lean::box(0);
}
x_143 = lean::cnstr_get(x_107, 0);
lean::inc(x_143);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_release(x_107, 0);
 x_144 = x_107;
} else {
 lean::dec_ref(x_107);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set_scalar(x_145, sizeof(void*)*1, x_132);
if (lean::is_scalar(x_142)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_142;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_141);
return x_146;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_1);
x_4 = l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_3);
lean::dec(x_3);
x_6 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_1);
lean::dec(x_6);
x_8 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_10;
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_Parser), 5, 0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_10 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_11 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_13 = l_Lean_Parser_Level_trailing;
x_14 = l_Lean_Parser_Level_trailing_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_Parser), 5, 0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
return x_8;
}
}
obj* l_Lean_Parser_Level_trailing_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Level_trailing;
x_7 = l_Lean_Parser_Level_trailing_Parser___closed__1;
x_8 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens;
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1;
return x_2;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTRefl___boxed), 2, 1);
lean::closure_set(x_1, 0, lean::box(0));
return x_1;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_Parser), 4, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_Parser), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = l_Lean_Parser_BasicParserM_Monad;
x_3 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1;
x_4 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_5 = l_Lean_Parser_BasicParserM_MonadReader;
x_6 = l_Lean_Parser_BasicParserM_MonadExcept;
x_7 = l_Lean_Parser_BasicParserM_Alternative;
x_8 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2;
x_9 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3;
x_10 = l_Lean_Parser_prattParser_View___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1);
return x_10;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_peekToken___closed__1;
lean::inc(x_2);
x_6 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(x_5, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
lean::dec(x_8);
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_7);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_7, 2);
x_13 = lean::cnstr_get(x_7, 0);
lean::dec(x_13);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_15);
lean::cnstr_set(x_7, 0, x_14);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_7);
lean::cnstr_set(x_6, 0, x_16);
return x_6;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = lean::cnstr_get(x_7, 1);
x_18 = lean::cnstr_get(x_7, 2);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_7);
x_19 = lean::mk_nat_obj(0u);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_21);
lean::cnstr_set(x_6, 0, x_22);
return x_6;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
lean::dec(x_6);
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_7, 2);
lean::inc(x_25);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_26 = x_7;
} else {
 lean::dec_ref(x_7);
 x_26 = lean::box(0);
}
x_27 = lean::mk_nat_obj(0u);
x_28 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_26)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_26;
}
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_24);
lean::cnstr_set(x_29, 2, x_28);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
return x_31;
}
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_8, 0);
lean::inc(x_32);
lean::dec(x_8);
switch (lean::obj_tag(x_32)) {
case 0:
{
obj* x_33; obj* x_34; uint8 x_35; 
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
lean::dec(x_32);
x_34 = lean::cnstr_get(x_6, 1);
lean::inc(x_34);
lean::dec(x_6);
x_35 = !lean::is_exclusive(x_7);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_36 = lean::cnstr_get(x_7, 1);
x_37 = lean::cnstr_get(x_7, 2);
x_38 = lean::cnstr_get(x_7, 0);
lean::dec(x_38);
x_39 = lean::cnstr_get(x_33, 1);
lean::inc(x_39);
lean::dec(x_33);
x_40 = lean::cnstr_get(x_2, 1);
lean::inc(x_40);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_Trie_oldMatchPrefix___rarg(x_40, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
lean::dec(x_43);
lean::free_heap_obj(x_7);
x_44 = lean::box(0);
x_45 = l_Lean_Parser_currLbp___rarg___lambda__1___closed__1;
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_45, x_46, x_44, x_44, x_1, x_2, x_36, x_34);
lean::dec(x_2);
x_48 = !lean::is_exclusive(x_47);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_49 = lean::cnstr_get(x_47, 0);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_49);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_52);
lean::cnstr_set(x_47, 0, x_53);
return x_47;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_54 = lean::cnstr_get(x_47, 0);
x_55 = lean::cnstr_get(x_47, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_47);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_54);
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
return x_60;
}
}
else
{
obj* x_61; uint8 x_62; 
lean::dec(x_2);
x_61 = lean::cnstr_get(x_43, 0);
lean::inc(x_61);
lean::dec(x_43);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_61, 1);
x_64 = lean::cnstr_get(x_61, 0);
lean::dec(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
lean::dec(x_63);
x_66 = l_Lean_Parser_matchToken___closed__1;
lean::cnstr_set(x_7, 2, x_66);
lean::cnstr_set(x_7, 0, x_65);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_7);
lean::cnstr_set(x_61, 1, x_34);
lean::cnstr_set(x_61, 0, x_67);
return x_61;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
lean::dec(x_68);
x_70 = l_Lean_Parser_matchToken___closed__1;
lean::cnstr_set(x_7, 2, x_70);
lean::cnstr_set(x_7, 0, x_69);
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_7);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_34);
return x_72;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_73 = lean::cnstr_get(x_7, 1);
x_74 = lean::cnstr_get(x_7, 2);
lean::inc(x_74);
lean::inc(x_73);
lean::dec(x_7);
x_75 = lean::cnstr_get(x_33, 1);
lean::inc(x_75);
lean::dec(x_33);
x_76 = lean::cnstr_get(x_2, 1);
lean::inc(x_76);
x_77 = lean::mk_nat_obj(0u);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_Lean_Parser_Trie_oldMatchPrefix___rarg(x_76, x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_79);
x_80 = lean::box(0);
x_81 = l_Lean_Parser_currLbp___rarg___lambda__1___closed__1;
x_82 = l_mjoin___rarg___closed__1;
x_83 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_81, x_82, x_80, x_80, x_1, x_2, x_73, x_34);
lean::dec(x_2);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_83, 1);
lean::inc(x_85);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_86 = x_83;
} else {
 lean::dec_ref(x_83);
 x_86 = lean::box(0);
}
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_84);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_88);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_89);
if (lean::is_scalar(x_86)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_86;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_85);
return x_91;
}
else
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_2);
x_92 = lean::cnstr_get(x_79, 0);
lean::inc(x_92);
lean::dec(x_79);
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_94 = x_92;
} else {
 lean::dec_ref(x_92);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
lean::dec(x_93);
x_96 = l_Lean_Parser_matchToken___closed__1;
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_73);
lean::cnstr_set(x_97, 2, x_96);
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_97);
if (lean::is_scalar(x_94)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_94;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_34);
return x_99;
}
}
}
case 1:
{
uint8 x_100; 
lean::dec(x_32);
lean::dec(x_2);
x_100 = !lean::is_exclusive(x_6);
if (x_100 == 0)
{
obj* x_101; uint8 x_102; 
x_101 = lean::cnstr_get(x_6, 0);
lean::dec(x_101);
x_102 = !lean::is_exclusive(x_7);
if (x_102 == 0)
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_103 = lean::cnstr_get(x_7, 2);
x_104 = lean::cnstr_get(x_7, 0);
lean::dec(x_104);
x_105 = l_Lean_Parser_maxPrec;
x_106 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_106);
lean::cnstr_set(x_7, 0, x_105);
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_7);
lean::cnstr_set(x_6, 0, x_107);
return x_6;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_108 = lean::cnstr_get(x_7, 1);
x_109 = lean::cnstr_get(x_7, 2);
lean::inc(x_109);
lean::inc(x_108);
lean::dec(x_7);
x_110 = l_Lean_Parser_maxPrec;
x_111 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_112 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_108);
lean::cnstr_set(x_112, 2, x_111);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_109, x_112);
lean::cnstr_set(x_6, 0, x_113);
return x_6;
}
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_114 = lean::cnstr_get(x_6, 1);
lean::inc(x_114);
lean::dec(x_6);
x_115 = lean::cnstr_get(x_7, 1);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_7, 2);
lean::inc(x_116);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_117 = x_7;
} else {
 lean::dec_ref(x_7);
 x_117 = lean::box(0);
}
x_118 = l_Lean_Parser_maxPrec;
x_119 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_117)) {
 x_120 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_120 = x_117;
}
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_115);
lean::cnstr_set(x_120, 2, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_120);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_114);
return x_122;
}
}
case 2:
{
obj* x_123; uint8 x_124; 
x_123 = lean::cnstr_get(x_32, 0);
lean::inc(x_123);
lean::dec(x_32);
x_124 = !lean::is_exclusive(x_6);
if (x_124 == 0)
{
obj* x_125; obj* x_126; uint8 x_127; 
x_125 = lean::cnstr_get(x_6, 1);
x_126 = lean::cnstr_get(x_6, 0);
lean::dec(x_126);
x_127 = !lean::is_exclusive(x_7);
if (x_127 == 0)
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; uint8 x_133; 
x_128 = lean::cnstr_get(x_7, 1);
x_129 = lean::cnstr_get(x_7, 2);
x_130 = lean::cnstr_get(x_7, 0);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
x_132 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
x_133 = lean_name_dec_eq(x_131, x_132);
if (x_133 == 0)
{
obj* x_134; uint8 x_135; 
x_134 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
x_135 = lean_name_dec_eq(x_131, x_134);
lean::dec(x_131);
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; uint8 x_140; 
lean::free_heap_obj(x_7);
lean::free_heap_obj(x_6);
x_136 = lean::box(0);
x_137 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_138 = l_mjoin___rarg___closed__1;
x_139 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_137, x_138, x_136, x_136, x_1, x_2, x_128, x_125);
lean::dec(x_2);
x_140 = !lean::is_exclusive(x_139);
if (x_140 == 0)
{
obj* x_141; obj* x_142; 
x_141 = lean::cnstr_get(x_139, 0);
x_142 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_141);
lean::cnstr_set(x_139, 0, x_142);
return x_139;
}
else
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_143 = lean::cnstr_get(x_139, 0);
x_144 = lean::cnstr_get(x_139, 1);
lean::inc(x_144);
lean::inc(x_143);
lean::dec(x_139);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_143);
x_146 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_144);
return x_146;
}
}
else
{
obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_2);
x_147 = l_Lean_Parser_maxPrec;
x_148 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_148);
lean::cnstr_set(x_7, 0, x_147);
x_149 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_7);
lean::cnstr_set(x_6, 0, x_149);
return x_6;
}
}
else
{
obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_131);
lean::dec(x_2);
x_150 = l_Lean_Parser_maxPrec;
x_151 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_151);
lean::cnstr_set(x_7, 0, x_150);
x_152 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_7);
lean::cnstr_set(x_6, 0, x_152);
return x_6;
}
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; uint8 x_157; 
x_153 = lean::cnstr_get(x_7, 1);
x_154 = lean::cnstr_get(x_7, 2);
lean::inc(x_154);
lean::inc(x_153);
lean::dec(x_7);
x_155 = lean::cnstr_get(x_123, 0);
lean::inc(x_155);
lean::dec(x_123);
x_156 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
x_157 = lean_name_dec_eq(x_155, x_156);
if (x_157 == 0)
{
obj* x_158; uint8 x_159; 
x_158 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
x_159 = lean_name_dec_eq(x_155, x_158);
lean::dec(x_155);
if (x_159 == 0)
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::free_heap_obj(x_6);
x_160 = lean::box(0);
x_161 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_162 = l_mjoin___rarg___closed__1;
x_163 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_161, x_162, x_160, x_160, x_1, x_2, x_153, x_125);
lean::dec(x_2);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 x_166 = x_163;
} else {
 lean::dec_ref(x_163);
 x_166 = lean::box(0);
}
x_167 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_154, x_164);
if (lean::is_scalar(x_166)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_166;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
return x_168;
}
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_2);
x_169 = l_Lean_Parser_maxPrec;
x_170 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_171 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set(x_171, 1, x_153);
lean::cnstr_set(x_171, 2, x_170);
x_172 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_154, x_171);
lean::cnstr_set(x_6, 0, x_172);
return x_6;
}
}
else
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_155);
lean::dec(x_2);
x_173 = l_Lean_Parser_maxPrec;
x_174 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_175 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set(x_175, 1, x_153);
lean::cnstr_set(x_175, 2, x_174);
x_176 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_154, x_175);
lean::cnstr_set(x_6, 0, x_176);
return x_6;
}
}
}
else
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; uint8 x_183; 
x_177 = lean::cnstr_get(x_6, 1);
lean::inc(x_177);
lean::dec(x_6);
x_178 = lean::cnstr_get(x_7, 1);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_7, 2);
lean::inc(x_179);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_180 = x_7;
} else {
 lean::dec_ref(x_7);
 x_180 = lean::box(0);
}
x_181 = lean::cnstr_get(x_123, 0);
lean::inc(x_181);
lean::dec(x_123);
x_182 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
x_183 = lean_name_dec_eq(x_181, x_182);
if (x_183 == 0)
{
obj* x_184; uint8 x_185; 
x_184 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
x_185 = lean_name_dec_eq(x_181, x_184);
lean::dec(x_181);
if (x_185 == 0)
{
obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_180);
x_186 = lean::box(0);
x_187 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_188 = l_mjoin___rarg___closed__1;
x_189 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_187, x_188, x_186, x_186, x_1, x_2, x_178, x_177);
lean::dec(x_2);
x_190 = lean::cnstr_get(x_189, 0);
lean::inc(x_190);
x_191 = lean::cnstr_get(x_189, 1);
lean::inc(x_191);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 x_192 = x_189;
} else {
 lean::dec_ref(x_189);
 x_192 = lean::box(0);
}
x_193 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_190);
if (lean::is_scalar(x_192)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_192;
}
lean::cnstr_set(x_194, 0, x_193);
lean::cnstr_set(x_194, 1, x_191);
return x_194;
}
else
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_2);
x_195 = l_Lean_Parser_maxPrec;
x_196 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_180)) {
 x_197 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_197 = x_180;
}
lean::cnstr_set(x_197, 0, x_195);
lean::cnstr_set(x_197, 1, x_178);
lean::cnstr_set(x_197, 2, x_196);
x_198 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_197);
x_199 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_199, 0, x_198);
lean::cnstr_set(x_199, 1, x_177);
return x_199;
}
}
else
{
obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
lean::dec(x_181);
lean::dec(x_2);
x_200 = l_Lean_Parser_maxPrec;
x_201 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_180)) {
 x_202 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_202 = x_180;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_178);
lean::cnstr_set(x_202, 2, x_201);
x_203 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_202);
x_204 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_177);
return x_204;
}
}
}
default: 
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; uint8 x_212; 
lean::dec(x_32);
x_205 = lean::cnstr_get(x_6, 1);
lean::inc(x_205);
lean::dec(x_6);
x_206 = lean::cnstr_get(x_7, 1);
lean::inc(x_206);
x_207 = lean::cnstr_get(x_7, 2);
lean::inc(x_207);
lean::dec(x_7);
x_208 = lean::box(0);
x_209 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_210 = l_mjoin___rarg___closed__1;
x_211 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_209, x_210, x_208, x_208, x_1, x_2, x_206, x_205);
lean::dec(x_2);
x_212 = !lean::is_exclusive(x_211);
if (x_212 == 0)
{
obj* x_213; obj* x_214; 
x_213 = lean::cnstr_get(x_211, 0);
x_214 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_207, x_213);
lean::cnstr_set(x_211, 0, x_214);
return x_211;
}
else
{
obj* x_215; obj* x_216; obj* x_217; obj* x_218; 
x_215 = lean::cnstr_get(x_211, 0);
x_216 = lean::cnstr_get(x_211, 1);
lean::inc(x_216);
lean::inc(x_215);
lean::dec(x_211);
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_207, x_215);
x_218 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_218, 0, x_217);
lean::cnstr_set(x_218, 1, x_216);
return x_218;
}
}
}
}
}
else
{
uint8 x_219; 
lean::dec(x_2);
x_219 = !lean::is_exclusive(x_6);
if (x_219 == 0)
{
obj* x_220; uint8 x_221; 
x_220 = lean::cnstr_get(x_6, 0);
lean::dec(x_220);
x_221 = !lean::is_exclusive(x_7);
if (x_221 == 0)
{
return x_6;
}
else
{
obj* x_222; uint8 x_223; obj* x_224; 
x_222 = lean::cnstr_get(x_7, 0);
x_223 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_222);
lean::dec(x_7);
x_224 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_224, 0, x_222);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_223);
lean::cnstr_set(x_6, 0, x_224);
return x_6;
}
}
else
{
obj* x_225; obj* x_226; uint8 x_227; obj* x_228; obj* x_229; obj* x_230; 
x_225 = lean::cnstr_get(x_6, 1);
lean::inc(x_225);
lean::dec(x_6);
x_226 = lean::cnstr_get(x_7, 0);
lean::inc(x_226);
x_227 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_228 = x_7;
} else {
 lean::dec_ref(x_7);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_226);
lean::cnstr_set_scalar(x_229, sizeof(void*)*1, x_227);
x_230 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_225);
return x_230;
}
}
}
}
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_3, x_11);
lean::inc(x_6);
x_13 = l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(x_5, x_6, x_7, x_8);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; obj* x_17; uint8 x_18; 
x_16 = lean::cnstr_get(x_13, 1);
x_17 = lean::cnstr_get(x_13, 0);
lean::dec(x_17);
x_18 = !lean::is_exclusive(x_14);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_19 = lean::cnstr_get(x_14, 0);
x_20 = lean::cnstr_get(x_14, 1);
x_21 = lean::cnstr_get(x_14, 2);
x_22 = lean::nat_dec_lt(x_2, x_19);
lean::dec(x_19);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_14, 2, x_23);
lean::cnstr_set(x_14, 0, x_4);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_14);
lean::cnstr_set(x_13, 0, x_24);
return x_13;
}
else
{
obj* x_25; obj* x_26; 
lean::free_heap_obj(x_14);
lean::free_heap_obj(x_13);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_5);
x_25 = lean::apply_5(x_1, x_4, x_5, x_6, x_20, x_16);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_26, 2);
lean::inc(x_30);
lean::dec(x_26);
x_31 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_1, x_2, x_12, x_28, x_5, x_6, x_29, x_27);
lean::dec(x_12);
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_31, 0);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_33);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_34);
lean::cnstr_set(x_31, 0, x_35);
return x_31;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_31, 0);
x_37 = lean::cnstr_get(x_31, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_31);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_36);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8 x_41; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_41 = !lean::is_exclusive(x_25);
if (x_41 == 0)
{
obj* x_42; uint8 x_43; 
x_42 = lean::cnstr_get(x_25, 0);
lean::dec(x_42);
x_43 = !lean::is_exclusive(x_26);
if (x_43 == 0)
{
obj* x_44; 
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_26);
lean::cnstr_set(x_25, 0, x_44);
return x_25;
}
else
{
obj* x_45; uint8 x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_26, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
lean::inc(x_45);
lean::dec(x_26);
x_47 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_46);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_47);
lean::cnstr_set(x_25, 0, x_48);
return x_25;
}
}
else
{
obj* x_49; obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_49 = lean::cnstr_get(x_25, 1);
lean::inc(x_49);
lean::dec(x_25);
x_50 = lean::cnstr_get(x_26, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_52 = x_26;
} else {
 lean::dec_ref(x_26);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_51);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_49);
return x_55;
}
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; uint8 x_59; 
x_56 = lean::cnstr_get(x_14, 0);
x_57 = lean::cnstr_get(x_14, 1);
x_58 = lean::cnstr_get(x_14, 2);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_14);
x_59 = lean::nat_dec_lt(x_2, x_56);
lean::dec(x_56);
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_4);
lean::cnstr_set(x_61, 1, x_57);
lean::cnstr_set(x_61, 2, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_61);
lean::cnstr_set(x_13, 0, x_62);
return x_13;
}
else
{
obj* x_63; obj* x_64; 
lean::free_heap_obj(x_13);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_5);
x_63 = lean::apply_5(x_1, x_4, x_5, x_6, x_57, x_16);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
lean::dec(x_63);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_64, 2);
lean::inc(x_68);
lean::dec(x_64);
x_69 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_1, x_2, x_12, x_66, x_5, x_6, x_67, x_65);
lean::dec(x_12);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_72 = x_69;
} else {
 lean::dec_ref(x_69);
 x_72 = lean::box(0);
}
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_70);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_73);
if (lean::is_scalar(x_72)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_72;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_71);
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; uint8 x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_76 = lean::cnstr_get(x_63, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_77 = x_63;
} else {
 lean::dec_ref(x_63);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_64, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get_scalar<uint8>(x_64, sizeof(void*)*1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_80 = x_64;
} else {
 lean::dec_ref(x_64);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_79);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_81);
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
return x_83;
}
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; uint8 x_89; 
x_84 = lean::cnstr_get(x_13, 1);
lean::inc(x_84);
lean::dec(x_13);
x_85 = lean::cnstr_get(x_14, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_14, 1);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_14, 2);
lean::inc(x_87);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_88 = x_14;
} else {
 lean::dec_ref(x_14);
 x_88 = lean::box(0);
}
x_89 = lean::nat_dec_lt(x_2, x_85);
lean::dec(x_85);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_90 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_88)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_88;
}
lean::cnstr_set(x_91, 0, x_4);
lean::cnstr_set(x_91, 1, x_86);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_84);
return x_93;
}
else
{
obj* x_94; obj* x_95; 
lean::dec(x_88);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_5);
x_94 = lean::apply_5(x_1, x_4, x_5, x_6, x_86, x_84);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_94, 1);
lean::inc(x_96);
lean::dec(x_94);
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_95, 2);
lean::inc(x_99);
lean::dec(x_95);
x_100 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_1, x_2, x_12, x_97, x_5, x_6, x_98, x_96);
lean::dec(x_12);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_103 = x_100;
} else {
 lean::dec_ref(x_100);
 x_103 = lean::box(0);
}
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_101);
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_104);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_102);
return x_106;
}
else
{
obj* x_107; obj* x_108; obj* x_109; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_107 = lean::cnstr_get(x_94, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_108 = x_94;
} else {
 lean::dec_ref(x_94);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_95, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_111 = x_95;
} else {
 lean::dec_ref(x_95);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_110);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_112);
if (lean::is_scalar(x_108)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_108;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_107);
return x_114;
}
}
}
}
else
{
uint8 x_115; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_115 = !lean::is_exclusive(x_13);
if (x_115 == 0)
{
obj* x_116; uint8 x_117; 
x_116 = lean::cnstr_get(x_13, 0);
lean::dec(x_116);
x_117 = !lean::is_exclusive(x_14);
if (x_117 == 0)
{
return x_13;
}
else
{
obj* x_118; uint8 x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_14, 0);
x_119 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::inc(x_118);
lean::dec(x_14);
x_120 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set_scalar(x_120, sizeof(void*)*1, x_119);
lean::cnstr_set(x_13, 0, x_120);
return x_13;
}
}
else
{
obj* x_121; obj* x_122; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; 
x_121 = lean::cnstr_get(x_13, 1);
lean::inc(x_121);
lean::dec(x_13);
x_122 = lean::cnstr_get(x_14, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_124 = x_14;
} else {
 lean::dec_ref(x_14);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_121);
return x_126;
}
}
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_4);
lean::dec(x_1);
x_127 = lean::box(0);
x_128 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_129 = l_mjoin___rarg___closed__1;
x_130 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_128, x_129, x_127, x_127, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
return x_130;
}
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_5);
lean::inc(x_3);
x_8 = lean::apply_4(x_1, x_3, x_5, x_6, x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_9, 2);
lean::inc(x_13);
lean::dec(x_9);
x_14 = l_String_OldIterator_remaining___main(x_12);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_14, x_15);
lean::dec(x_14);
x_17 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_2, x_4, x_16, x_11, x_3, x_5, x_12, x_10);
lean::dec(x_16);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = l_Lean_Parser_finishCommentBlock___closed__2;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_19);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_21);
lean::cnstr_set(x_17, 0, x_22);
return x_17;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_17, 0);
x_24 = lean::cnstr_get(x_17, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_17);
x_25 = l_Lean_Parser_finishCommentBlock___closed__2;
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_23);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8 x_29; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_29 = !lean::is_exclusive(x_8);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::cnstr_get(x_8, 0);
lean::dec(x_30);
x_31 = !lean::is_exclusive(x_9);
if (x_31 == 0)
{
return x_8;
}
else
{
obj* x_32; uint8 x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_9, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_32);
lean::dec(x_9);
x_34 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_33);
lean::cnstr_set(x_8, 0, x_34);
return x_8;
}
}
else
{
obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_8, 1);
lean::inc(x_35);
lean::dec(x_8);
x_36 = lean::cnstr_get(x_9, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_38 = x_9;
} else {
 lean::dec_ref(x_9);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_35);
return x_40;
}
}
}
}
obj* _init_l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__1___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed), 7, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_7);
x_10 = lean::apply_4(x_3, x_9, x_4, x_5, x_6);
return x_10;
}
}
obj* l_Lean_Parser_levelParser_run(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2;
x_6 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3;
x_7 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_9;
}
}
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
return x_8;
}
}
obj* _init_l_Lean_Parser_levelParserCoe() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser_run), 4, 0);
return x_1;
}
}
obj* initialize_init_lean_parser_pratt(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_level(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_pratt(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_LevelParserM_Monad = _init_l_Lean_Parser_LevelParserM_Monad();
lean::mark_persistent(l_Lean_Parser_LevelParserM_Monad);
l_Lean_Parser_LevelParserM_Alternative = _init_l_Lean_Parser_LevelParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_LevelParserM_Alternative);
l_Lean_Parser_LevelParserM_MonadReader = _init_l_Lean_Parser_LevelParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_LevelParserM_MonadReader);
l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec);
l_Lean_Parser_LevelParserM_MonadExcept = _init_l_Lean_Parser_LevelParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_LevelParserM_MonadExcept);
l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec = _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec();
lean::mark_persistent(l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec);
l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser = _init_l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser();
lean::mark_persistent(l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser);
l_Lean_Parser_TrailingLevelParserM_Monad = _init_l_Lean_Parser_TrailingLevelParserM_Monad();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_Monad);
l_Lean_Parser_TrailingLevelParserM_Alternative = _init_l_Lean_Parser_TrailingLevelParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_Alternative);
l_Lean_Parser_TrailingLevelParserM_MonadReader = _init_l_Lean_Parser_TrailingLevelParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_MonadReader);
l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec);
l_Lean_Parser_TrailingLevelParserM_MonadExcept = _init_l_Lean_Parser_TrailingLevelParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_MonadExcept);
l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec = _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec);
l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser = _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser();
lean::mark_persistent(l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser);
l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1 = _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1);
l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1 = _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1);
l_Lean_Parser_Level_Parser___closed__1 = _init_l_Lean_Parser_Level_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_Parser___closed__1);
l_Lean_Parser_Level_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_Lean_Parser_HasTokens);
l_Lean_Parser_Level_Lean_Parser_HasView = _init_l_Lean_Parser_Level_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_Lean_Parser_HasView);
l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
lean::mark_persistent(l_Lean_Parser_Level_paren);
l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Level_paren_HasView_x27 = _init_l_Lean_Parser_Level_paren_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x27);
l_Lean_Parser_Level_paren_HasView = _init_l_Lean_Parser_Level_paren_HasView();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView);
l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens);
l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView);
l_Lean_Parser_Level_paren_Parser___closed__1 = _init_l_Lean_Parser_Level_paren_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_paren_Parser___closed__1);
l_Lean_Parser_Level_leading = _init_l_Lean_Parser_Level_leading();
lean::mark_persistent(l_Lean_Parser_Level_leading);
l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3 = _init_l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3);
l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_Level_leading_HasView_x27 = _init_l_Lean_Parser_Level_leading_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x27);
l_Lean_Parser_Level_leading_HasView = _init_l_Lean_Parser_Level_leading_HasView();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView);
l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1 = _init_l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1);
l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens);
l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView);
l_Lean_Parser_Level_leading_Parser___closed__1 = _init_l_Lean_Parser_Level_leading_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_leading_Parser___closed__1);
l_Lean_Parser_Level_app = _init_l_Lean_Parser_Level_app();
lean::mark_persistent(l_Lean_Parser_Level_app);
l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_app_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_Level_app_HasView_x27 = _init_l_Lean_Parser_Level_app_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Level_app_HasView_x27);
l_Lean_Parser_Level_app_HasView = _init_l_Lean_Parser_Level_app_HasView();
lean::mark_persistent(l_Lean_Parser_Level_app_HasView);
l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens);
l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView);
l_Lean_Parser_Level_app_Parser___closed__1 = _init_l_Lean_Parser_Level_app_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_app_Parser___closed__1);
l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
lean::mark_persistent(l_Lean_Parser_Level_addLit);
l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Level_addLit_HasView_x27 = _init_l_Lean_Parser_Level_addLit_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x27);
l_Lean_Parser_Level_addLit_HasView = _init_l_Lean_Parser_Level_addLit_HasView();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView);
l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens);
l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView);
l_Lean_Parser_Level_addLit_Parser___closed__1 = _init_l_Lean_Parser_Level_addLit_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit_Parser___closed__1);
l_Lean_Parser_Level_trailing = _init_l_Lean_Parser_Level_trailing();
lean::mark_persistent(l_Lean_Parser_Level_trailing);
l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Level_trailing_HasView_x27 = _init_l_Lean_Parser_Level_trailing_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x27);
l_Lean_Parser_Level_trailing_HasView = _init_l_Lean_Parser_Level_trailing_HasView();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView);
l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens);
l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView);
l_Lean_Parser_Level_trailing_Parser___closed__1 = _init_l_Lean_Parser_Level_trailing_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser___closed__1);
l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1 = _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1();
lean::mark_persistent(l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___closed__1);
l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1 = _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1();
lean::mark_persistent(l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1);
l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2 = _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2();
lean::mark_persistent(l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2);
l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3 = _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3();
lean::mark_persistent(l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3);
l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1 = _init_l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1();
lean::mark_persistent(l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1);
l_Lean_Parser_levelParserCoe = _init_l_Lean_Parser_levelParserCoe();
lean::mark_persistent(l_Lean_Parser_levelParserCoe);
return w;
}
