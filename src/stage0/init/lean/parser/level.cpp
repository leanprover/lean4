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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*);
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l_Lean_Parser_trailingLevelParserCoe(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix___rarg(obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Level_paren;
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_Lean_Parser_MonadRec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*);
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_HasView_x_27;
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l_Lean_Parser_LevelParserM_MonadExcept;
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Alternative;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1;
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
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
obj* l_Lean_Parser_Level_addLit;
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
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
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__2(obj*);
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_Level_trailing_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___boxed(obj*);
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
obj* l_Lean_Parser_Level_app_HasView_x_27;
obj* l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser;
obj* l_Lean_Parser_Level_getLeading(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_Level_trailing_Parser___closed__1;
obj* l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView;
obj* l_hasMonadLiftTRefl___boxed(obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
obj* l_Lean_Parser_Level_paren_HasView_x_27;
extern obj* l_Lean_Parser_matchToken___closed__1;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_LevelParserM_Alternative;
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__2(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Level_paren_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x_27;
extern obj* l_Lean_Parser_peekToken___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(obj*);
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___boxed(obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_addLit_Parser___closed__1;
obj* l_Lean_Parser_Level_app_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_Level_trailing;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Level_leading;
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_Combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3;
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
obj* l_Lean_Parser_Level_Lean_Parser_HasView;
obj* l_Lean_Parser_TrailingLevelParserM_MonadReader;
obj* l_ReaderT_MonadExcept___rarg(obj*);
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x_27;
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_app_Parser___closed__1;
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_Level_app_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___boxed(obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_Level_getLeading___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
obj* l_Lean_Parser_levelParser_run(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Parser_Level_app_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2(obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1;
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_addLit_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_Level_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2;
obj* l_hasMonadLiftTTrans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_paren_HasView;
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_TrailingLevelParserM_Monad;
extern obj* l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1;
obj* _init_l_Lean_Parser_LevelParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_BasicParserM_Monad;
x_1 = l_ReaderT_Monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_BasicParserM_Monad;
x_1 = l_Lean_Parser_BasicParserM_Alternative;
x_2 = l_ReaderT_Alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_LevelParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_BasicParserM_MonadReader;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_BasicParserM_Monad;
x_1 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_2 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_LevelParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_BasicParserM_MonadExcept;
x_1 = l_ReaderT_MonadExcept___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Parser_BasicParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTRefl___boxed), 2, 1);
lean::closure_set(x_2, 0, lean::box(0));
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = l_ReaderT_Monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = l_Lean_Parser_LevelParserM_Alternative;
x_2 = l_ReaderT_Alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, lean::box(0));
lean::closure_set(x_2, 3, x_0);
lean::closure_set(x_2, 4, x_0);
x_3 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_4 = l_Lean_Parser_monadParsecTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_LevelParserM_MonadExcept;
x_1 = l_ReaderT_MonadExcept___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadRec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
lean::closure_set(x_3, 2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Parser_TrailingLevelParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Parser_LevelParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_Lean_Parser_LevelParserM_Lean_Parser_monadBasicParser;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_trailingLevelParserCoe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_trailingLevelParserCoe___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_trailingLevelParserCoe(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("universe Level");
return x_0;
}
}
obj* l_Lean_Parser_Level_Parser_Lean_Parser_HasView(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___spec__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadRec;
x_4 = l_Lean_Parser_Combinators_recurse_view___rarg(x_0, x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_7 = l_Lean_Parser_LevelParserM_Alternative;
x_8 = l_Lean_Parser_Level_Parser_Lean_Parser_HasView___closed__1;
x_9 = l_Lean_Parser_Combinators_label_view___rarg(x_6, x_7, x_2, x_8, x_4);
lean::dec(x_2);
return x_9;
}
}
obj* _init_l_Lean_Parser_Level_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("universe Level");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_Level_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
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
x_11 = l_Lean_Parser_Level_Parser___closed__1;
x_12 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_6, x_11);
if (lean::is_scalar(x_10)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_10;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
return x_13;
}
}
obj* l_Lean_Parser_Level_getLeading(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_Level_getLeading___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Level_getLeading(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Level_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Parser_Level_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("paren");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2;
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
lbl_4:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_2);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_3, 0);
lean::inc(x_24);
lean::dec(x_3);
switch (lean::obj_tag(x_24)) {
case 0:
{
obj* x_27; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_30);
return x_31;
}
case 3:
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
default:
{
obj* x_35; obj* x_36; 
lean::dec(x_24);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_2);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
}
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_6, 0);
lean::inc(x_37);
lean::dec(x_6);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
if (lean::obj_tag(x_5) == 0)
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::box(0);
x_42 = lean::box(3);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set(x_43, 2, x_41);
return x_43;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_5, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_5, 1);
lean::inc(x_46);
lean::dec(x_5);
x_1 = x_40;
x_2 = x_44;
x_3 = x_46;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_49; 
x_49 = l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; obj* x_52; obj* x_55; 
x_50 = lean::cnstr_get(x_5, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_5, 1);
lean::inc(x_52);
lean::dec(x_5);
x_55 = lean::box(0);
x_1 = x_55;
x_2 = x_50;
x_3 = x_52;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_57; 
x_57 = l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1;
return x_57;
}
else
{
obj* x_58; obj* x_60; obj* x_63; 
x_58 = lean::cnstr_get(x_5, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_5, 1);
lean::inc(x_60);
lean::dec(x_5);
x_63 = lean::box(0);
x_1 = x_63;
x_2 = x_58;
x_3 = x_60;
goto lbl_4;
}
}
}
}
}
}
obj* l_Lean_Parser_Level_paren_HasView_x_27___lambda__2(obj* x_0) {
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_Level_paren;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_8);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(3);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_Level_paren;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
else
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
lean::dec(x_1);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_5) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_Level_paren;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_5, 0);
lean::inc(x_34);
lean::dec(x_5);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_8);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_3);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_28);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_Parser_Level_paren;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_paren_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_paren_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_Lean_Parser_token(x_4, x_5, x_6);
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_10, 0);
x_19 = lean::cnstr_get(x_10, 1);
x_21 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_23 = x_10;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_10);
 x_23 = lean::box(0);
}
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_26; obj* x_28; uint8 x_31; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
lean::dec(x_26);
x_31 = lean::string_dec_eq(x_0, x_28);
lean::dec(x_0);
if (x_31 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_23);
lean::dec(x_14);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_5);
x_36 = lean::box(0);
x_37 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_28, x_2, x_35, x_36, x_4, x_19, x_12);
lean::dec(x_4);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_41 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_43 = x_37;
} else {
 lean::inc(x_41);
 lean::dec(x_37);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_39, 1);
x_46 = lean::cnstr_get(x_39, 2);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_48 = x_39;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_39);
 x_48 = lean::box(0);
}
x_49 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_17);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_52);
x_54 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_53, x_16);
x_55 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_54);
if (lean::is_scalar(x_43)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_43;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_41);
return x_56;
}
else
{
obj* x_58; obj* x_60; obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_17);
x_58 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_60 = x_37;
} else {
 lean::inc(x_58);
 lean::dec(x_37);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_39, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 x_64 = x_39;
} else {
 lean::inc(x_61);
 lean::dec(x_39);
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
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_66);
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_67);
x_70 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_69, x_16);
x_71 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_70);
if (lean::is_scalar(x_60)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_60;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_58);
return x_72;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_28);
x_77 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_23)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_23;
}
lean::cnstr_set(x_78, 0, x_17);
lean::cnstr_set(x_78, 1, x_19);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_78);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_79);
x_82 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_81, x_16);
x_83 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_82);
if (lean::is_scalar(x_14)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_14;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_12);
return x_84;
}
}
case 3:
{
obj* x_88; 
lean::dec(x_23);
lean::dec(x_14);
lean::dec(x_0);
x_88 = lean::box(0);
x_24 = x_88;
goto lbl_25;
}
default:
{
obj* x_93; 
lean::dec(x_23);
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_17);
x_93 = lean::box(0);
x_24 = x_93;
goto lbl_25;
}
}
lbl_25:
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_24);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_5);
x_96 = lean::box(0);
x_97 = l_String_splitAux___main___closed__1;
x_98 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_97, x_2, x_95, x_96, x_4, x_19, x_12);
lean::dec(x_4);
x_100 = lean::cnstr_get(x_98, 0);
x_102 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 x_104 = x_98;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_98);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_100);
x_106 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_106, x_105);
x_108 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_107, x_16);
x_109 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_108);
if (lean::is_scalar(x_104)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_104;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_102);
return x_110;
}
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::cnstr_get(x_10, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_118 = x_10;
} else {
 lean::inc(x_115);
 lean::dec(x_10);
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
x_123 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_122, x_16);
x_124 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_123);
if (lean::is_scalar(x_14)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_14;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_12);
return x_125;
}
}
}
obj* _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_17; 
x_0 = lean::mk_string("(");
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string(")");
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_5);
lean::dec(x_4);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_8);
lean::dec(x_6);
x_11 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_9);
lean::dec(x_9);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_12);
lean::dec(x_12);
lean::dec(x_2);
x_17 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
return x_17;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_3);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = l_Lean_Parser_maxPrec;
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_Parser), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string(")");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_LevelParserM_Monad;
x_20 = l_Lean_Parser_LevelParserM_MonadExcept;
x_21 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_22 = l_Lean_Parser_LevelParserM_Alternative;
x_23 = l_Lean_Parser_Level_paren;
x_24 = l_Lean_Parser_Level_paren_HasView;
x_25 = l_Lean_Parser_Combinators_node_view___rarg(x_19, x_20, x_21, x_22, x_23, x_18, x_24);
lean::dec(x_18);
return x_25;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
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
obj* x_48; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_50 = x_24;
} else {
 lean::inc(x_48);
 lean::dec(x_24);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 3);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_53; obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
x_53 = lean::cnstr_get(x_23, 1);
lean::inc(x_53);
lean::dec(x_23);
x_56 = lean::cnstr_get(x_48, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_48, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_48, 2);
lean::inc(x_60);
lean::dec(x_48);
x_63 = lean::box(3);
lean::inc(x_1);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_1);
x_66 = l_List_reverse___rarg(x_65);
lean::inc(x_0);
x_68 = l_Lean_Parser_Syntax_mkNode(x_0, x_66);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_70, 0, x_56);
lean::cnstr_set(x_70, 1, x_58);
lean::cnstr_set(x_70, 2, x_60);
lean::cnstr_set(x_70, 3, x_69);
if (x_29 == 0)
{
uint8 x_71; obj* x_72; obj* x_73; 
x_71 = 0;
if (lean::is_scalar(x_50)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_50;
}
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_71);
x_73 = x_72;
x_18 = x_73;
x_19 = x_53;
goto lbl_20;
}
else
{
uint8 x_74; obj* x_75; obj* x_76; 
x_74 = 1;
if (lean::is_scalar(x_50)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_50;
}
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_74);
x_76 = x_75;
x_18 = x_76;
x_19 = x_53;
goto lbl_20;
}
}
else
{
obj* x_77; obj* x_80; obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
x_77 = lean::cnstr_get(x_23, 1);
lean::inc(x_77);
lean::dec(x_23);
x_80 = lean::cnstr_get(x_48, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_48, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_48, 2);
lean::inc(x_84);
lean::dec(x_48);
x_87 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_89 = x_51;
} else {
 lean::inc(x_87);
 lean::dec(x_51);
 x_89 = lean::box(0);
}
lean::inc(x_1);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set(x_91, 1, x_1);
x_92 = l_List_reverse___rarg(x_91);
lean::inc(x_0);
x_94 = l_Lean_Parser_Syntax_mkNode(x_0, x_92);
if (lean::is_scalar(x_89)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_89;
}
lean::cnstr_set(x_95, 0, x_94);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_80);
lean::cnstr_set(x_96, 1, x_82);
lean::cnstr_set(x_96, 2, x_84);
lean::cnstr_set(x_96, 3, x_95);
if (x_29 == 0)
{
uint8 x_97; obj* x_98; obj* x_99; 
x_97 = 0;
if (lean::is_scalar(x_50)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_50;
}
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_97);
x_99 = x_98;
x_18 = x_99;
x_19 = x_77;
goto lbl_20;
}
else
{
uint8 x_100; obj* x_101; obj* x_102; 
x_100 = 1;
if (lean::is_scalar(x_50)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_50;
}
lean::cnstr_set(x_101, 0, x_96);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_100);
x_102 = x_101;
x_18 = x_102;
x_19 = x_77;
goto lbl_20;
}
}
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_18, 0);
x_105 = lean::cnstr_get(x_18, 1);
x_107 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 x_109 = x_18;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_18);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_17;
}
lean::cnstr_set(x_110, 0, x_103);
lean::cnstr_set(x_110, 1, x_1);
x_111 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_105);
lean::cnstr_set(x_112, 2, x_111);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_116; obj* x_118; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_113, 2);
lean::inc(x_118);
lean::dec(x_113);
x_121 = l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(x_0, x_114, x_15, x_3, x_4, x_116, x_19);
x_122 = lean::cnstr_get(x_121, 0);
x_124 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 x_126 = x_121;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_118, x_122);
if (lean::is_scalar(x_126)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_126;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_124);
return x_128;
}
else
{
obj* x_133; uint8 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_133 = lean::cnstr_get(x_113, 0);
x_135 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
if (lean::is_exclusive(x_113)) {
 x_136 = x_113;
} else {
 lean::inc(x_133);
 lean::dec(x_113);
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
x_139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_19);
return x_139;
}
}
else
{
obj* x_146; uint8 x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_146 = lean::cnstr_get(x_18, 0);
x_148 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_149 = x_18;
} else {
 lean::inc(x_146);
 lean::dec(x_18);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_146);
lean::cnstr_set_scalar(x_150, sizeof(void*)*1, x_148);
x_151 = x_150;
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_19);
return x_152;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_List_mfoldl___main___at_Lean_Parser_Level_paren_Parser___spec__2(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* _init_l_Lean_Parser_Level_paren_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = l_Lean_Parser_maxPrec;
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_Parser), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string(")");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l_Lean_Parser_Level_paren_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Level_paren;
x_5 = l_Lean_Parser_Level_paren_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_leading() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1() {
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
x_8 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
x_11 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
x_23 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
x_31 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
x_50 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
obj* x_66; uint8 x_67; 
lean::dec(x_26);
x_66 = lean::mk_nat_obj(3ul);
x_67 = lean::nat_dec_eq(x_41, x_66);
if (x_67 == 0)
{
obj* x_68; uint8 x_69; 
x_68 = lean::mk_nat_obj(4ul);
x_69 = lean::nat_dec_eq(x_41, x_68);
lean::dec(x_41);
if (x_69 == 0)
{
switch (lean::obj_tag(x_56)) {
case 1:
{
obj* x_71; obj* x_74; 
x_71 = lean::cnstr_get(x_56, 0);
lean::inc(x_71);
lean::dec(x_56);
x_74 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_74, 0, x_71);
return x_74;
}
case 3:
{
obj* x_75; 
x_75 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2;
return x_75;
}
default:
{
obj* x_77; 
lean::dec(x_56);
x_77 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2;
return x_77;
}
}
}
else
{
obj* x_78; obj* x_79; obj* x_82; obj* x_83; 
x_78 = l_Lean_Parser_number_HasView;
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
lean::dec(x_78);
x_82 = lean::apply_1(x_79, x_56);
x_83 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
}
else
{
obj* x_85; obj* x_86; obj* x_89; obj* x_90; 
lean::dec(x_41);
x_85 = l_Lean_Parser_Level_paren_HasView;
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
lean::dec(x_85);
x_89 = lean::apply_1(x_86, x_56);
x_90 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_92; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_56, 0);
lean::inc(x_92);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_26;
}
lean::cnstr_set(x_95, 0, x_92);
x_96 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
case 3:
{
obj* x_98; 
lean::dec(x_26);
x_98 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3;
return x_98;
}
default:
{
obj* x_101; 
lean::dec(x_56);
lean::dec(x_26);
x_101 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3;
return x_101;
}
}
}
}
else
{
obj* x_104; 
lean::dec(x_26);
lean::dec(x_41);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_56);
return x_104;
}
}
else
{
obj* x_107; 
lean::dec(x_26);
lean::dec(x_41);
x_107 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_107, 0, x_56);
return x_107;
}
}
else
{
obj* x_112; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_112 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
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
x_115 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4;
return x_115;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Level_leading;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(4ul);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(5ul);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
x_6 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_Level_leading;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
case 1:
{
obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_1);
x_18 = l_Lean_Parser_Level_leading;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
case 2:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_1);
x_32 = l_Lean_Parser_Level_leading;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
}
case 3:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = l_Lean_Parser_Level_paren_HasView;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_41 = lean::apply_1(x_38, x_34);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_1);
x_43 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
x_44 = l_Lean_Parser_Syntax_mkNode(x_43, x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_1);
x_46 = l_Lean_Parser_Level_leading;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
case 4:
{
obj* x_48; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
lean::dec(x_0);
x_51 = l_Lean_Parser_number_HasView;
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
lean::dec(x_51);
x_55 = lean::apply_1(x_52, x_48);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_1);
x_57 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2;
x_58 = l_Lean_Parser_Syntax_mkNode(x_57, x_56);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_1);
x_60 = l_Lean_Parser_Level_leading;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
return x_61;
}
default:
{
obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_0, 0);
lean::inc(x_62);
lean::dec(x_0);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3;
x_68 = l_Lean_Parser_Syntax_mkNode(x_67, x_66);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_1);
x_70 = l_Lean_Parser_Level_leading;
x_71 = l_Lean_Parser_Syntax_mkNode(x_70, x_69);
return x_71;
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_leading_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_leading_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = l_Lean_Parser_token(x_2, x_3, x_4);
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
obj* x_22; obj* x_24; obj* x_27; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_20 = x_27;
goto lbl_21;
}
case 1:
{
obj* x_28; obj* x_30; obj* x_33; obj* x_35; 
x_28 = lean::cnstr_get(x_13, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_33 = l_Lean_Parser_Substring_toString(x_30);
lean::dec(x_30);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_33);
x_20 = x_35;
goto lbl_21;
}
default:
{
obj* x_36; 
x_36 = lean::box(0);
x_20 = x_36;
goto lbl_21;
}
}
lbl_21:
{
uint8 x_37; 
if (lean::obj_tag(x_20) == 0)
{
uint8 x_39; 
x_39 = 1;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; uint8 x_43; 
x_40 = lean::cnstr_get(x_20, 0);
lean::inc(x_40);
lean::dec(x_20);
x_43 = lean::string_dec_eq(x_40, x_0);
lean::dec(x_40);
if (x_43 == 0)
{
uint8 x_45; 
x_45 = 1;
x_37 = x_45;
goto lbl_38;
}
else
{
uint8 x_46; 
x_46 = 0;
x_37 = x_46;
goto lbl_38;
}
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_50 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_19)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_19;
}
lean::cnstr_set(x_51, 0, x_13);
lean::cnstr_set(x_51, 1, x_15);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_51);
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_52);
x_55 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_54);
if (lean::is_scalar(x_12)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_12;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_10);
return x_56;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_12);
lean::dec(x_19);
x_59 = l_String_quote(x_0);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_3);
x_62 = lean::box(0);
x_63 = l_String_splitAux___main___closed__1;
x_64 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_63, x_60, x_61, x_62, x_2, x_15, x_10);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_68 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_70 = x_64;
} else {
 lean::inc(x_68);
 lean::dec(x_64);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_66, 1);
x_73 = lean::cnstr_get(x_66, 2);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_75 = x_66;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_66);
 x_75 = lean::box(0);
}
x_76 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_13);
lean::cnstr_set(x_77, 1, x_71);
lean::cnstr_set(x_77, 2, x_76);
x_78 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_78);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_79);
x_81 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_80);
if (lean::is_scalar(x_70)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_70;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_68);
return x_82;
}
else
{
obj* x_84; obj* x_86; obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_13);
x_84 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_86 = x_64;
} else {
 lean::inc(x_84);
 lean::dec(x_64);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_66, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_90 = x_66;
} else {
 lean::inc(x_87);
 lean::dec(x_66);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
x_93 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_92);
x_94 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_95 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_94, x_93);
x_96 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_95);
if (lean::is_scalar(x_86)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_86;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_84);
return x_97;
}
}
}
}
}
else
{
obj* x_101; obj* x_103; obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_101 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_103 = x_7;
} else {
 lean::inc(x_101);
 lean::dec(x_7);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_8, 0);
x_106 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_107 = x_8;
} else {
 lean::inc(x_104);
 lean::dec(x_8);
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
x_110 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_109);
x_112 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_111);
if (lean::is_scalar(x_103)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_103;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_101);
return x_113;
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_Lean_Parser_token(x_0, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
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
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_17 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = l_Lean_Parser_number;
x_19 = l_Lean_Parser_Syntax_isOfKind___main(x_18, x_11);
if (x_19 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_String_splitAux___main___closed__1;
x_26 = l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
lean::dec(x_0);
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
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_29);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_34);
x_37 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_36);
if (lean::is_scalar(x_33)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_33;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_0);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_17;
}
lean::cnstr_set(x_42, 0, x_11);
lean::cnstr_set(x_42, 1, x_13);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_43);
x_45 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_44);
if (lean::is_scalar(x_10)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_10;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_8);
return x_46;
}
}
else
{
obj* x_49; obj* x_51; obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_1);
lean::dec(x_0);
x_49 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_51 = x_5;
} else {
 lean::inc(x_49);
 lean::dec(x_5);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_6, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_55 = x_6;
} else {
 lean::inc(x_52);
 lean::dec(x_6);
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
x_58 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_57);
x_60 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_59);
if (lean::is_scalar(x_51)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_51;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_49);
return x_61;
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_Lean_Parser_token(x_0, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
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
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_17 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
switch (lean::obj_tag(x_11)) {
case 1:
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_0);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_17;
}
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_24);
x_26 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_27 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_25, x_26);
x_28 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_27);
if (lean::is_scalar(x_10)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_10;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_8);
return x_29;
}
case 3:
{
obj* x_32; 
lean::dec(x_17);
lean::dec(x_10);
x_32 = lean::box(0);
x_18 = x_32;
goto lbl_19;
}
default:
{
obj* x_36; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_36 = lean::box(0);
x_18 = x_36;
goto lbl_19;
}
}
lbl_19:
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_18);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_1);
x_39 = lean::box(0);
x_40 = l_String_splitAux___main___closed__1;
x_41 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_42 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_40, x_41, x_38, x_39, x_0, x_13, x_8);
lean::dec(x_0);
x_44 = lean::cnstr_get(x_42, 0);
x_46 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_48 = x_42;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_42);
 x_48 = lean::box(0);
}
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_44);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_49);
x_52 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_51, x_41);
x_53 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_52);
if (lean::is_scalar(x_48)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_48;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_46);
return x_54;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_0);
x_57 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_59 = x_5;
} else {
 lean::inc(x_57);
 lean::dec(x_5);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_6, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_63 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
x_66 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_65);
x_68 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg___closed__1;
x_69 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_67, x_68);
x_70 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_69);
if (lean::is_scalar(x_59)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_59;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_57);
return x_71;
}
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_6);
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
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_14; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_6);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_0);
lean::cnstr_set(x_17, 2, x_1);
lean::cnstr_set(x_17, 3, x_3);
x_18 = 0;
x_19 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_18);
x_20 = x_19;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_0, 0);
x_15 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_21 = lean::apply_4(x_13, x_2, x_3, x_4, x_5);
x_22 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 lean::cnstr_set(x_21, 1, lean::box(0));
 x_26 = x_21;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_21);
 x_26 = lean::box(0);
}
x_27 = lean::mk_nat_obj(1ul);
x_28 = lean::nat_add(x_1, x_27);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_29 = lean::cnstr_get(x_22, 0);
x_31 = lean::cnstr_get(x_22, 1);
x_33 = lean::cnstr_get(x_22, 2);
if (lean::is_exclusive(x_22)) {
 x_35 = x_22;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_22);
 x_35 = lean::box(0);
}
x_36 = lean::box(0);
x_37 = lean_name_mk_numeral(x_36, x_1);
x_38 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_17;
}
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_Syntax_mkNode(x_37, x_39);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_31);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_49; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_15);
if (lean::is_scalar(x_26)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_26;
}
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_24);
return x_49;
}
else
{
uint8 x_50; 
x_50 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_26);
x_52 = lean::cnstr_get(x_43, 0);
lean::inc(x_52);
lean::dec(x_43);
x_55 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_15, x_28, x_2, x_3, x_4, x_24);
x_56 = lean::cnstr_get(x_55, 0);
x_58 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_60 = x_55;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_55);
 x_60 = lean::box(0);
}
x_61 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_52, x_56);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_58);
return x_62;
}
else
{
obj* x_68; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_15);
if (lean::is_scalar(x_26)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_26;
}
lean::cnstr_set(x_68, 0, x_43);
lean::cnstr_set(x_68, 1, x_24);
return x_68;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_1);
lean::dec(x_17);
x_71 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_26);
x_73 = lean::cnstr_get(x_22, 0);
lean::inc(x_73);
lean::dec(x_22);
x_76 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4(x_15, x_28, x_2, x_3, x_4, x_24);
x_77 = lean::cnstr_get(x_76, 0);
x_79 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 x_81 = x_76;
} else {
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
x_82 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_73, x_77);
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_79);
return x_83;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_15);
x_89 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_91 = x_22;
} else {
 lean::inc(x_89);
 lean::dec(x_22);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_71);
x_93 = x_92;
if (lean::is_scalar(x_26)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_26;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_24);
return x_94;
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_0);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_5);
lean::dec(x_5);
x_8 = l_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens;
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_6);
lean::dec(x_6);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_9);
lean::dec(x_9);
lean::dec(x_3);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_11);
lean::dec(x_11);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_14);
lean::dec(x_14);
x_18 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
x_20 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_0);
lean::dec(x_18);
x_22 = l_Lean_Parser_tokens___rarg(x_20);
lean::dec(x_20);
return x_22;
}
}
obj* l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = l_Lean_Parser_maxPrec;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed), 1, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed), 1, 0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_Parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_nat_obj(0ul);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_11);
x_24 = l_Lean_Parser_LevelParserM_Monad;
x_25 = l_Lean_Parser_LevelParserM_MonadExcept;
x_26 = l_Lean_Parser_LevelParserM_Lean_Parser_MonadParsec;
x_27 = l_Lean_Parser_LevelParserM_Alternative;
x_28 = l_Lean_Parser_Level_leading;
x_29 = l_Lean_Parser_Level_leading_HasView;
x_30 = l_Lean_Parser_Combinators_node_view___rarg(x_24, x_25, x_26, x_27, x_28, x_23, x_29);
lean::dec(x_23);
return x_30;
}
}
obj* _init_l_Lean_Parser_Level_leading_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = l_Lean_Parser_maxPrec;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_paren_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__3___boxed), 1, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__2___boxed), 1, 0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_paren_Parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_nat_obj(0ul);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_11);
return x_23;
}
}
obj* l_Lean_Parser_Level_leading_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Level_leading;
x_5 = l_Lean_Parser_Level_leading_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_paren_Parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_app() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("app");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* l_Lean_Parser_Level_app_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1;
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_23; 
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
lean::dec(x_10);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
}
}
}
}
obj* l_Lean_Parser_Level_app_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_Level_app;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_Level_app_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_app_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_app_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_0 = l_Lean_Parser_Level_Parser_Lean_Parser_HasTokens___closed__1;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = lean::box(0);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_Level_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_3);
lean::dec(x_3);
x_8 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
return x_8;
}
}
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_maxPrec;
x_6 = l_Lean_Parser_Level_Parser(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_6 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_7 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_8 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_9 = l_Lean_Parser_Level_app;
x_10 = l_Lean_Parser_Level_app_HasView;
x_11 = l_Lean_Parser_Combinators_node_view___rarg(x_5, x_6, x_7, x_8, x_9, x_4, x_10);
lean::dec(x_4);
return x_11;
}
}
obj* l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* x_51; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_53 = x_27;
} else {
 lean::inc(x_51);
 lean::dec(x_27);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
x_56 = lean::cnstr_get(x_26, 1);
lean::inc(x_56);
lean::dec(x_26);
x_59 = lean::cnstr_get(x_51, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_51, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_51, 2);
lean::inc(x_63);
lean::dec(x_51);
x_66 = lean::box(3);
lean::inc(x_1);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_1);
x_69 = l_List_reverse___rarg(x_68);
lean::inc(x_0);
x_71 = l_Lean_Parser_Syntax_mkNode(x_0, x_69);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_73, 0, x_59);
lean::cnstr_set(x_73, 1, x_61);
lean::cnstr_set(x_73, 2, x_63);
lean::cnstr_set(x_73, 3, x_72);
if (x_32 == 0)
{
uint8 x_74; obj* x_75; obj* x_76; 
x_74 = 0;
if (lean::is_scalar(x_53)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_53;
}
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_74);
x_76 = x_75;
x_20 = x_76;
x_21 = x_56;
goto lbl_22;
}
else
{
uint8 x_77; obj* x_78; obj* x_79; 
x_77 = 1;
if (lean::is_scalar(x_53)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_53;
}
lean::cnstr_set(x_78, 0, x_73);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_77);
x_79 = x_78;
x_20 = x_79;
x_21 = x_56;
goto lbl_22;
}
}
else
{
obj* x_80; obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
x_80 = lean::cnstr_get(x_26, 1);
lean::inc(x_80);
lean::dec(x_26);
x_83 = lean::cnstr_get(x_51, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_51, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_51, 2);
lean::inc(x_87);
lean::dec(x_51);
x_90 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_92 = x_54;
} else {
 lean::inc(x_90);
 lean::dec(x_54);
 x_92 = lean::box(0);
}
lean::inc(x_1);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set(x_94, 1, x_1);
x_95 = l_List_reverse___rarg(x_94);
lean::inc(x_0);
x_97 = l_Lean_Parser_Syntax_mkNode(x_0, x_95);
if (lean::is_scalar(x_92)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_92;
}
lean::cnstr_set(x_98, 0, x_97);
x_99 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_99, 0, x_83);
lean::cnstr_set(x_99, 1, x_85);
lean::cnstr_set(x_99, 2, x_87);
lean::cnstr_set(x_99, 3, x_98);
if (x_32 == 0)
{
uint8 x_100; obj* x_101; obj* x_102; 
x_100 = 0;
if (lean::is_scalar(x_53)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_53;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_100);
x_102 = x_101;
x_20 = x_102;
x_21 = x_80;
goto lbl_22;
}
else
{
uint8 x_103; obj* x_104; obj* x_105; 
x_103 = 1;
if (lean::is_scalar(x_53)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_53;
}
lean::cnstr_set(x_104, 0, x_99);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_103);
x_105 = x_104;
x_20 = x_105;
x_21 = x_80;
goto lbl_22;
}
}
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_106 = lean::cnstr_get(x_20, 0);
x_108 = lean::cnstr_get(x_20, 1);
x_110 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_112 = x_20;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::inc(x_110);
 lean::dec(x_20);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_19;
}
lean::cnstr_set(x_113, 0, x_106);
lean::cnstr_set(x_113, 1, x_1);
x_114 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_112)) {
 x_115 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_115 = x_112;
}
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_108);
lean::cnstr_set(x_115, 2, x_114);
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_119; obj* x_121; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_131; 
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_116, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_116, 2);
lean::inc(x_121);
lean::dec(x_116);
x_124 = l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(x_0, x_117, x_17, x_3, x_4, x_5, x_119, x_21);
x_125 = lean::cnstr_get(x_124, 0);
x_127 = lean::cnstr_get(x_124, 1);
if (lean::is_exclusive(x_124)) {
 x_129 = x_124;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_124);
 x_129 = lean::box(0);
}
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_121, x_125);
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_127);
return x_131;
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_137 = lean::cnstr_get(x_116, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_116, sizeof(void*)*1);
if (lean::is_exclusive(x_116)) {
 x_140 = x_116;
} else {
 lean::inc(x_137);
 lean::dec(x_116);
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
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_21);
return x_143;
}
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_151 = lean::cnstr_get(x_20, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_154 = x_20;
} else {
 lean::inc(x_151);
 lean::dec(x_20);
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
x_157 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_21);
return x_157;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::box(0);
lean::inc(x_0);
x_9 = l_List_mfoldl___main___at_Lean_Parser_Level_app_Parser___spec__2(x_0, x_7, x_1, x_2, x_3, x_4, x_5, x_6);
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
obj* _init_l_Lean_Parser_Level_app_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_Level_app_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Level_app;
x_6 = l_Lean_Parser_Level_app_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_addLit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("addLit");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1() {
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
obj* _init_l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1;
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2;
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
obj* x_18; obj* x_19; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; 
x_21 = lean::box(3);
x_18 = x_1;
x_19 = x_21;
goto lbl_20;
}
else
{
obj* x_22; obj* x_24; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
lean::dec(x_1);
x_18 = x_24;
x_19 = x_22;
goto lbl_20;
}
lbl_20:
{
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
if (lean::obj_tag(x_18) == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1;
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_2);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_18, 0);
lean::inc(x_33);
lean::dec(x_18);
x_36 = l_Lean_Parser_number_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_33);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_30);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
case 3:
{
obj* x_42; 
x_42 = lean::box(0);
if (lean::obj_tag(x_18) == 0)
{
obj* x_43; obj* x_44; 
x_43 = l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_2);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_52; obj* x_53; 
x_45 = lean::cnstr_get(x_18, 0);
lean::inc(x_45);
lean::dec(x_18);
x_48 = l_Lean_Parser_number_HasView;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
lean::dec(x_48);
x_52 = lean::apply_1(x_49, x_45);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_2);
lean::cnstr_set(x_53, 1, x_42);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
}
default:
{
obj* x_55; 
lean::dec(x_19);
x_55 = lean::box(0);
if (lean::obj_tag(x_18) == 0)
{
obj* x_56; obj* x_57; 
x_56 = l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1;
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_2);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_56);
return x_57;
}
else
{
obj* x_58; obj* x_61; obj* x_62; obj* x_65; obj* x_66; 
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_Lean_Parser_number_HasView;
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
lean::dec(x_61);
x_65 = lean::apply_1(x_62, x_58);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_2);
lean::cnstr_set(x_66, 1, x_55);
lean::cnstr_set(x_66, 2, x_65);
return x_66;
}
}
}
}
}
}
}
obj* l_Lean_Parser_Level_addLit_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_number_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_5);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_Level_addLit;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
lean::dec(x_3);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_14);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_Level_addLit;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_addLit_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; 
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_Lean_Parser_token(x_5, x_6, x_7);
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
obj* x_36; obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_15);
lean::dec(x_24);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_6);
x_37 = lean::box(0);
x_38 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_29, x_2, x_36, x_37, x_5, x_20, x_13);
lean::dec(x_5);
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_42 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
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
lean::cnstr_set(x_51, 0, x_18);
lean::cnstr_set(x_51, 1, x_45);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_53);
x_55 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_54, x_17);
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
lean::dec(x_18);
x_59 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_61 = x_38;
} else {
 lean::inc(x_59);
 lean::dec(x_38);
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
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_67);
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_68);
x_71 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_70, x_17);
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
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_29);
x_78 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_24)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_24;
}
lean::cnstr_set(x_79, 0, x_18);
lean::cnstr_set(x_79, 1, x_20);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_79);
x_81 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_80);
x_83 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_82, x_17);
x_84 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_83);
if (lean::is_scalar(x_15)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_15;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_13);
return x_85;
}
}
case 3:
{
obj* x_89; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
x_89 = lean::box(0);
x_25 = x_89;
goto lbl_26;
}
default:
{
obj* x_94; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
lean::dec(x_18);
x_94 = lean::box(0);
x_25 = x_94;
goto lbl_26;
}
}
lbl_26:
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_25);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_6);
x_97 = lean::box(0);
x_98 = l_String_splitAux___main___closed__1;
x_99 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_98, x_2, x_96, x_97, x_5, x_20, x_13);
lean::dec(x_5);
x_101 = lean::cnstr_get(x_99, 0);
x_103 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_105 = x_99;
} else {
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_99);
 x_105 = lean::box(0);
}
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_101);
x_107 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_106);
x_109 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_108, x_17);
x_110 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_109);
if (lean::is_scalar(x_105)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_105;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_103);
return x_111;
}
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_116 = lean::cnstr_get(x_11, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_119 = x_11;
} else {
 lean::inc(x_116);
 lean::dec(x_11);
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
x_122 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_122, x_121);
x_124 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_123, x_17);
x_125 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_124);
if (lean::is_scalar(x_15)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_15;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_13);
return x_126;
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_Lean_Parser_token(x_0, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
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
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_17 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = l_Lean_Parser_number;
x_19 = l_Lean_Parser_Syntax_isOfKind___main(x_18, x_11);
if (x_19 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_String_splitAux___main___closed__1;
x_26 = l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
lean::dec(x_0);
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
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_29);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_34);
x_37 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_36);
if (lean::is_scalar(x_33)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_33;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_0);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_17;
}
lean::cnstr_set(x_42, 0, x_11);
lean::cnstr_set(x_42, 1, x_13);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_43);
x_45 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_44);
if (lean::is_scalar(x_10)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_10;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_8);
return x_46;
}
}
else
{
obj* x_49; obj* x_51; obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_1);
lean::dec(x_0);
x_49 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_51 = x_5;
} else {
 lean::inc(x_49);
 lean::dec(x_5);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_6, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_55 = x_6;
} else {
 lean::inc(x_52);
 lean::dec(x_6);
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
x_58 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_57);
x_60 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_59);
if (lean::is_scalar(x_51)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_51;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_49);
return x_61;
}
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_12; 
x_0 = lean::mk_string("+");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_4);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
x_9 = l_Lean_Parser_Level_Lean_Parser_HasTokens;
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_6);
lean::dec(x_6);
x_12 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
return x_12;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_4);
return x_8;
}
}
obj* l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::mk_string("+");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 2, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_14 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_15 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_16 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_17 = l_Lean_Parser_Level_addLit;
x_18 = l_Lean_Parser_Level_addLit_HasView;
x_19 = l_Lean_Parser_Combinators_node_view___rarg(x_13, x_14, x_15, x_16, x_17, x_12, x_18);
lean::dec(x_12);
return x_19;
}
}
obj* _init_l_Lean_Parser_Level_addLit_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::mk_string("+");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___at_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens___spec__2___boxed), 2, 0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_getLeading___boxed), 5, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
obj* l_Lean_Parser_Level_addLit_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Level_addLit;
x_6 = l_Lean_Parser_Level_addLit_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_Level_trailing() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_Level_app_HasView;
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
obj* _init_l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_23 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_30 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_47 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_58 = l_Lean_Parser_Level_addLit_HasView;
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
x_64 = l_Lean_Parser_Level_app_HasView;
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
x_73 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
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
x_76 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1;
return x_76;
}
}
}
}
}
}
obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__2(obj* x_0) {
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
x_5 = l_Lean_Parser_Level_app_HasView;
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
x_14 = l_Lean_Parser_Level_trailing;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_Level_addLit_HasView;
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
x_28 = l_Lean_Parser_Level_trailing;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Level_trailing_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Level_trailing_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_7);
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
lean::cnstr_set(x_13, 1, x_8);
return x_13;
}
else
{
obj* x_15; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_0);
lean::cnstr_set(x_18, 2, x_1);
lean::cnstr_set(x_18, 3, x_3);
x_19 = 0;
x_20 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_19);
x_21 = x_20;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 9, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_11;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_15 = lean::cnstr_get(x_0, 0);
x_17 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_19 = x_0;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_0);
 x_19 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_24 = lean::apply_5(x_15, x_2, x_3, x_4, x_5, x_6);
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 lean::cnstr_set(x_24, 1, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::mk_nat_obj(1ul);
x_31 = lean::nat_add(x_1, x_30);
if (lean::obj_tag(x_25) == 0)
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_32 = lean::cnstr_get(x_25, 0);
x_34 = lean::cnstr_get(x_25, 1);
x_36 = lean::cnstr_get(x_25, 2);
if (lean::is_exclusive(x_25)) {
 x_38 = x_25;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_25);
 x_38 = lean::box(0);
}
x_39 = lean::box(0);
x_40 = lean_name_mk_numeral(x_39, x_1);
x_41 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_19;
}
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_Syntax_mkNode(x_40, x_42);
x_44 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_34);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_53; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_17);
if (lean::is_scalar(x_29)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_29;
}
lean::cnstr_set(x_53, 0, x_46);
lean::cnstr_set(x_53, 1, x_27);
return x_53;
}
else
{
uint8 x_54; 
x_54 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (x_54 == 0)
{
obj* x_56; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_29);
x_56 = lean::cnstr_get(x_46, 0);
lean::inc(x_56);
lean::dec(x_46);
x_59 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_17, x_31, x_2, x_3, x_4, x_5, x_27);
x_60 = lean::cnstr_get(x_59, 0);
x_62 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 x_64 = x_59;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
x_65 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_56, x_60);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_62);
return x_66;
}
else
{
obj* x_73; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_17);
if (lean::is_scalar(x_29)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_29;
}
lean::cnstr_set(x_73, 0, x_46);
lean::cnstr_set(x_73, 1, x_27);
return x_73;
}
}
}
else
{
uint8 x_76; 
lean::dec(x_19);
lean::dec(x_1);
x_76 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (x_76 == 0)
{
obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_29);
x_78 = lean::cnstr_get(x_25, 0);
lean::inc(x_78);
lean::dec(x_25);
x_81 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1(x_17, x_31, x_2, x_3, x_4, x_5, x_27);
x_82 = lean::cnstr_get(x_81, 0);
x_84 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 x_86 = x_81;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_81);
 x_86 = lean::box(0);
}
x_87 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_78, x_82);
if (lean::is_scalar(x_86)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_86;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_84);
return x_88;
}
else
{
obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_17);
x_95 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_97 = x_25;
} else {
 lean::inc(x_95);
 lean::dec(x_25);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_76);
x_99 = x_98;
if (lean::is_scalar(x_29)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_29;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_27);
return x_100;
}
}
}
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_Level_addLit_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_0);
x_3 = l_Lean_Parser_Level_app_Parser_Lean_Parser_HasTokens;
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_TrailingLevelParserM_Monad;
x_9 = l_Lean_Parser_TrailingLevelParserM_MonadExcept;
x_10 = l_Lean_Parser_TrailingLevelParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_TrailingLevelParserM_Alternative;
x_12 = l_Lean_Parser_Level_trailing;
x_13 = l_Lean_Parser_Level_trailing_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Parser_Level_trailing_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_addLit_Parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_app_Parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens___spec__1), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
}
}
obj* l_Lean_Parser_Level_trailing_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_Level_trailing;
x_6 = l_Lean_Parser_Level_trailing_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_Level_app_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Level_leading_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens;
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_levelParser_run_Lean_Parser_HasTokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTRefl___boxed), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
return x_0;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_leading_Parser), 4, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Level_trailing_Parser), 5, 0);
return x_0;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__1;
x_3 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_4 = l_Lean_Parser_BasicParserM_MonadReader;
x_5 = l_Lean_Parser_BasicParserM_MonadExcept;
x_6 = l_Lean_Parser_BasicParserM_Alternative;
x_7 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2;
x_8 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3;
x_9 = l_Lean_Parser_prattParser_View___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_0);
return x_9;
}
}
obj* l_Lean_Parser_levelParser_run_Lean_Parser_HasView___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_6);
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
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_14; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_6);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_0);
lean::cnstr_set(x_17, 2, x_1);
lean::cnstr_set(x_17, 3, x_3);
x_18 = 0;
x_19 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_18);
x_20 = x_19;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = l_Lean_Parser_peekToken___closed__1;
lean::inc(x_1);
x_6 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(x_4, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_7, 1);
x_18 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_20 = x_7;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_7);
 x_20 = lean::box(0);
}
x_21 = lean::mk_nat_obj(0ul);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_20;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_16);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_23);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_13);
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_9, 0);
lean::inc(x_26);
lean::dec(x_9);
switch (lean::obj_tag(x_26)) {
case 0:
{
obj* x_29; obj* x_32; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_7, 1);
x_37 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_39 = x_7;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_7);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_29, 1);
lean::inc(x_40);
lean::dec(x_29);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
x_45 = lean::mk_nat_obj(0ul);
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_40);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 2, x_45);
x_47 = l_Lean_Parser_Trie_oldMatchPrefix___rarg(x_43, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_39);
x_49 = lean::box(0);
x_50 = l_Lean_Parser_currLbp___rarg___lambda__1___closed__1;
x_51 = l_mjoin___rarg___closed__1;
x_52 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_50, x_51, x_49, x_49, x_0, x_1, x_35, x_32);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_52, 0);
x_56 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_58 = x_52;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_52);
 x_58 = lean::box(0);
}
x_59 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_54);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_61);
if (lean::is_scalar(x_58)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_58;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; obj* x_68; obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_1);
x_65 = lean::cnstr_get(x_47, 0);
lean::inc(x_65);
lean::dec(x_47);
x_68 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 x_70 = x_65;
} else {
 lean::inc(x_68);
 lean::dec(x_65);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
x_74 = l_Lean_Parser_matchToken___closed__1;
if (lean::is_scalar(x_39)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_39;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set(x_75, 1, x_35);
lean::cnstr_set(x_75, 2, x_74);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_75);
if (lean::is_scalar(x_70)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_70;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_32);
return x_77;
}
}
case 1:
{
obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_1);
lean::dec(x_26);
x_80 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_82 = x_6;
} else {
 lean::inc(x_80);
 lean::dec(x_6);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_7, 1);
x_85 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_87 = x_7;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_7);
 x_87 = lean::box(0);
}
x_88 = l_Lean_Parser_maxPrec;
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
if (lean::is_scalar(x_82)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_82;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_80);
return x_92;
}
case 2:
{
obj* x_93; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_107; uint8 x_108; 
x_93 = lean::cnstr_get(x_26, 0);
lean::inc(x_93);
lean::dec(x_26);
x_96 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_98 = x_6;
} else {
 lean::inc(x_96);
 lean::dec(x_6);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_7, 1);
x_101 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_103 = x_7;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_7);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_93, 0);
lean::inc(x_104);
lean::dec(x_93);
x_107 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
x_108 = lean_name_dec_eq(x_104, x_107);
if (x_108 == 0)
{
obj* x_109; uint8 x_110; 
x_109 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
x_110 = lean_name_dec_eq(x_104, x_109);
lean::dec(x_104);
if (x_110 == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_103);
lean::dec(x_98);
x_114 = lean::box(0);
x_115 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_116 = l_mjoin___rarg___closed__1;
x_117 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_115, x_116, x_114, x_114, x_0, x_1, x_99, x_96);
lean::dec(x_1);
x_119 = lean::cnstr_get(x_117, 0);
x_121 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 x_123 = x_117;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_117);
 x_123 = lean::box(0);
}
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_119);
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_121);
return x_125;
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_1);
x_127 = l_Lean_Parser_maxPrec;
x_128 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_103)) {
 x_129 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_129 = x_103;
}
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_99);
lean::cnstr_set(x_129, 2, x_128);
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_129);
if (lean::is_scalar(x_98)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_98;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_96);
return x_131;
}
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_1);
lean::dec(x_104);
x_134 = l_Lean_Parser_maxPrec;
x_135 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_103)) {
 x_136 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_136 = x_103;
}
lean::cnstr_set(x_136, 0, x_134);
lean::cnstr_set(x_136, 1, x_99);
lean::cnstr_set(x_136, 2, x_135);
x_137 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_136);
if (lean::is_scalar(x_98)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_98;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_96);
return x_138;
}
}
default:
{
obj* x_139; obj* x_142; obj* x_144; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_157; obj* x_158; 
x_139 = lean::cnstr_get(x_6, 1);
lean::inc(x_139);
lean::dec(x_6);
x_142 = lean::cnstr_get(x_7, 1);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_7, 2);
lean::inc(x_144);
lean::dec(x_7);
x_147 = lean::box(0);
x_148 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__2;
x_149 = l_mjoin___rarg___closed__1;
x_150 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_148, x_149, x_147, x_147, x_0, x_1, x_142, x_139);
lean::dec(x_1);
x_152 = lean::cnstr_get(x_150, 0);
x_154 = lean::cnstr_get(x_150, 1);
if (lean::is_exclusive(x_150)) {
 x_156 = x_150;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::dec(x_150);
 x_156 = lean::box(0);
}
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_144, x_152);
if (lean::is_scalar(x_156)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_156;
}
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_154);
return x_158;
}
}
}
}
else
{
obj* x_160; obj* x_162; obj* x_163; uint8 x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_1);
x_160 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_162 = x_6;
} else {
 lean::inc(x_160);
 lean::dec(x_6);
 x_162 = lean::box(0);
}
x_163 = lean::cnstr_get(x_7, 0);
x_165 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_166 = x_7;
} else {
 lean::inc(x_163);
 lean::dec(x_7);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_163);
lean::cnstr_set_scalar(x_167, sizeof(void*)*1, x_165);
x_168 = x_167;
if (lean::is_scalar(x_162)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_162;
}
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_160);
return x_169;
}
}
}
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0ul);
x_9 = lean::nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_5);
x_11 = l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(x_4, x_5, x_6, x_7);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; uint8 x_24; 
x_14 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_set(x_11, 1, lean::box(0));
 x_16 = x_11;
} else {
 lean::inc(x_14);
 lean::dec(x_11);
 x_16 = lean::box(0);
}
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
x_24 = lean::nat_dec_lt(x_1, x_17);
lean::dec(x_17);
if (x_24 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_23)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_23;
}
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_19);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_30);
if (lean::is_scalar(x_16)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_16;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_14);
return x_32;
}
else
{
obj* x_35; obj* x_36; obj* x_40; obj* x_41; 
lean::dec(x_16);
lean::dec(x_23);
x_35 = lean::mk_nat_obj(1ul);
x_36 = lean::nat_sub(x_2, x_35);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_0);
x_40 = lean::apply_5(x_0, x_3, x_4, x_5, x_19, x_14);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_41, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_41, 2);
lean::inc(x_50);
lean::dec(x_41);
x_53 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_0, x_1, x_36, x_46, x_4, x_5, x_48, x_43);
lean::dec(x_36);
x_55 = lean::cnstr_get(x_53, 0);
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_59 = x_53;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_55);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_60);
if (lean::is_scalar(x_59)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_59;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_57);
return x_62;
}
else
{
obj* x_67; obj* x_69; obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_36);
x_67 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_69 = x_40;
} else {
 lean::inc(x_67);
 lean::dec(x_40);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_41, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_73 = x_41;
} else {
 lean::inc(x_70);
 lean::dec(x_41);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_75);
if (lean::is_scalar(x_69)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_69;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_67);
return x_77;
}
}
}
else
{
obj* x_82; obj* x_84; obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_82 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_84 = x_11;
} else {
 lean::inc(x_82);
 lean::dec(x_11);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_12, 0);
x_87 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_88 = x_12;
} else {
 lean::inc(x_85);
 lean::dec(x_12);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
if (lean::is_scalar(x_84)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_84;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_82);
return x_91;
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_3);
lean::dec(x_0);
x_94 = lean::box(0);
x_95 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_96 = l_mjoin___rarg___closed__1;
x_97 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_95, x_96, x_94, x_94, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
return x_97;
}
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; 
lean::inc(x_4);
lean::inc(x_2);
x_9 = lean::apply_4(x_0, x_2, x_4, x_5, x_6);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
lean::dec(x_10);
x_22 = l_String_OldIterator_remaining___main(x_17);
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_add(x_22, x_23);
lean::dec(x_22);
x_26 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_1, x_3, x_24, x_15, x_2, x_4, x_17, x_12);
lean::dec(x_24);
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
x_33 = l_Lean_Parser_finishCommentBlock___closed__2;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_28);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_34);
if (lean::is_scalar(x_32)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_32;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_30);
return x_36;
}
else
{
obj* x_40; obj* x_42; obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_40 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_42 = x_9;
} else {
 lean::inc(x_40);
 lean::dec(x_9);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_10, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_46 = x_10;
} else {
 lean::inc(x_43);
 lean::dec(x_10);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
if (lean::is_scalar(x_42)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_42;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_40);
return x_49;
}
}
}
obj* _init_l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed), 7, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___closed__1;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_6);
x_9 = lean::apply_4(x_2, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* l_Lean_Parser_levelParser_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__2;
x_5 = l_Lean_Parser_levelParser_run_Lean_Parser_HasView___closed__3;
x_6 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_levelParser_run___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_currLbp___at_Lean_Parser_levelParser_run___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_pratt_1__trailingLoop___main___at_Lean_Parser_levelParser_run___spec__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_prattParser___at_Lean_Parser_levelParser_run___spec__1___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* _init_l_Lean_Parser_levelParserCoe() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_levelParser_run), 4, 0);
return x_0;
}
}
obj* initialize_init_lean_parser_pratt(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_level(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_pratt(w);
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
 l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Level_paren_HasView_x_27 = _init_l_Lean_Parser_Level_paren_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Level_paren_HasView_x_27);
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
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3 = _init_l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27___lambda__2___closed__3);
 l_Lean_Parser_Level_leading_HasView_x_27 = _init_l_Lean_Parser_Level_leading_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Level_leading_HasView_x_27);
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
 l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_app_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Level_app_HasView_x_27 = _init_l_Lean_Parser_Level_app_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Level_app_HasView_x_27);
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
 l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Level_addLit_HasView_x_27 = _init_l_Lean_Parser_Level_addLit_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Level_addLit_HasView_x_27);
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
 l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Level_trailing_HasView_x_27 = _init_l_Lean_Parser_Level_trailing_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView_x_27);
 l_Lean_Parser_Level_trailing_HasView = _init_l_Lean_Parser_Level_trailing_HasView();
lean::mark_persistent(l_Lean_Parser_Level_trailing_HasView);
 l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser_Lean_Parser_HasView);
 l_Lean_Parser_Level_trailing_Parser___closed__1 = _init_l_Lean_Parser_Level_trailing_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Level_trailing_Parser___closed__1);
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
