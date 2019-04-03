// Lean compiler output
// Module: init.lean.parser.basic
// Imports: init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.rec init.lean.parser.trie init.lean.parser.identifier init.data.rbmap.default init.lean.message
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
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___boxed(obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_Parser_tryView___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_trailingTermParserCoe___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_run___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___boxed(obj*, obj*);
obj* l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadRec;
obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadRec;
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___boxed(obj*);
extern obj* l_Lean_MessageLog_empty;
obj* l_Lean_Parser_CommandParserM_Monad___closed__1;
obj* l_Lean_Parser_TokenMap_ofList___boxed(obj*);
obj* l_Lean_Parser_TokenMap_ofList___main(obj*);
obj* l_Lean_Parser_logMessage(obj*, obj*, obj*);
obj* l_Id_map___boxed(obj*, obj*);
obj* l_Lean_Parser_CommandParserM_MonadReader(obj*);
obj* l_Lean_Parser_messageOfParsecMessage(obj*);
obj* l_Lean_Parser_MonadRec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(obj*);
obj* l_Lean_Parser_logMessage___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_ofList___rarg(obj*);
obj* l_Lean_Parser_ParserT_Alternative___rarg(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec(obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_HasTokens_Inhabited(obj*, obj*);
obj* l_Lean_Parser_BasicParserM_Monad;
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(obj*, obj*, obj*);
obj* l_StateT_Monad___rarg(obj*);
obj* l_Lean_Parser_run___rarg___closed__1;
obj* l_Lean_Parser_TokenMap_ofList(obj*);
obj* l_Lean_Parser_ParserT_Alternative(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1(obj*);
obj* l_Lean_Parser_tokenMapCons_tokens___rarg___boxed(obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3;
obj* l_Lean_Parser_CommandParserM_basicParser(obj*);
obj* l_Lean_Parser_tokenMapNil_tokens(obj*);
obj* l_Lean_Parser_run___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___boxed(obj*);
obj* l_Lean_Parser_ParserT_MonadExcept___rarg(obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_ReaderT_MonadReaderAdapter___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_HasTokens_Inhabited___boxed(obj*, obj*);
obj* l_Lean_Parser_TermParserM_Alternative;
obj* l_id___rarg___boxed(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2;
obj* l_Lean_Parser_CommandParserM_Alternative___boxed(obj*);
obj* l_Lean_Parser_ParserT_MonadExcept___boxed(obj*, obj*);
obj* l_Lean_Parser_mkTokenTrie(obj*);
obj* l_Lean_Parser_parserCoreT_Monad(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1(obj*, obj*);
obj* l_Lean_Parser_tokenMapCons_tokens___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parserCoreT_Alternative___rarg(obj*);
obj* l_Lean_Parser_tokenMapCons_tokens(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(obj*);
obj* l_Lean_Parser_logMessage___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2(obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___boxed(obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_logMessage___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Parser_parserCoreT_MonadExcept___rarg(obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Parser_commandParserConfigCoeParserConfig___boxed(obj*);
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_BasicParserM_MonadReader;
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_TokenMap_insert___boxed(obj*);
obj* l_Lean_Parser_getCache___boxed(obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_MonadExcept___closed__1;
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_TrailingTermParserM_Alternative;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_parserCoreT_MonadExcept(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg(obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___boxed(obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec(obj*);
obj* l_Lean_Parser_CommandParserM_MonadReaderAdapter___boxed(obj*, obj*);
obj* l_Lean_Parser_commandParserConfigCoeParserConfig(obj*);
obj* l_Lean_Parser_TermParserM_MonadReader;
obj* l_Id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parserCoreT_MonadExcept___boxed(obj*);
obj* l_Lean_Parser_putCache___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parserConfigCoe___boxed(obj*);
obj* l_Lean_Parser_CommandParserM_basicParser___boxed(obj*);
obj* l_Lean_Parser_ParserT_MonadReader___boxed(obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_ParserT_MonadReader(obj*, obj*);
obj* l_Lean_Parser_run___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Parser_CommandParserM_basicParser___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_trailingTermParserCoe(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_text___rarg(obj*);
obj* l_Lean_Parser_TokenMap_insert(obj*);
obj* l_Lean_Parser_ParserT_MonadExcept(obj*, obj*);
obj* l_Lean_Parser_tryView(obj*);
obj* l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_parserConfigCoe(obj*);
obj* l_Id_pure___boxed(obj*);
obj* l_Lean_Parser_List_cons_tokens___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_tokenMapNil_tokens___boxed(obj*);
obj* l_Lean_Parser_putCache(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_ParserT_Monad___rarg(obj*);
obj* l_Lean_Parser_List_nil_tokens(obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg(obj*);
obj* l_Lean_Parser_getCache___rarg(obj*, obj*);
obj* l_Lean_Parser_TrailingTermParserM_MonadReader;
obj* l_ReaderT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_run___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_CommandParserM_MonadReader___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_HasView_default___boxed(obj*);
obj* l_Lean_Parser_TermParserM_Monad;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1;
obj* l_Lean_Parser_CommandParserM_Monad___boxed(obj*);
obj* l_Id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Id_bind___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Trie_empty___closed__1;
obj* l_Lean_Parser_tokens(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec(obj*);
obj* l_Lean_Parser_tokenMapCons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(obj*);
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___boxed(obj*);
obj* l_Lean_Parser_messageOfParsecMessage___rarg(obj*, obj*);
obj* l_Lean_Parser_CommandParserM_MonadReaderAdapter(obj*, obj*);
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser;
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_parserCoreT_Monad___rarg(obj*);
obj* l_Lean_Parser_CommandParserM_MonadReader___closed__1;
obj* l_Lean_Parser_HasView_default___rarg(obj*);
obj* l_Lean_Parser_getCache(obj*);
obj* l_Lean_Parser_CommandParserM_Alternative(obj*);
obj* l_Lean_Parser_run(obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Alternative___closed__1;
obj* l_Lean_Parser_TrailingTermParserM_Monad;
obj* l_Lean_Parser_ParserT_Monad___boxed(obj*, obj*);
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___boxed(obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Monad(obj*);
obj* l_Lean_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_CommandParserM_basicParser___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_HasView_default___rarg___boxed(obj*);
obj* l_Lean_Parser_TermParserM_MonadExcept;
obj* l_Lean_Parser_ParserT_Alternative___boxed(obj*, obj*);
obj* l_Lean_Parser_TokenMap_ofList___main___boxed(obj*);
obj* l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1;
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5(obj*);
obj* l_Lean_Parser_CommandParserM_MonadExcept___boxed(obj*);
obj* l_Lean_Parser_HasView_default(obj*);
obj* l_Lean_Parser_parserCoreT_Alternative___boxed(obj*);
obj* l_Lean_Parser_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_ParserT_MonadReader___rarg(obj*);
obj* l_Lean_Parser_TrailingTermParserM_MonadExcept;
obj* l_Lean_Parser_BasicParserM_MonadExcept;
obj* l_hasMonadLiftTTrans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_logMessage___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TrailingTermParserM_Lean_Parser_monadBasicParser;
obj* l_Lean_Parser_tryView___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParserT_Monad(obj*, obj*);
obj* l_Lean_Parser_messageOfParsecMessage___boxed(obj*);
obj* l_Lean_Parser_mkTokenTrie___closed__1;
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___boxed(obj*);
obj* l_Lean_Parser_TokenMap_ofList___main___rarg(obj*);
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___rarg(obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_MonadExcept(obj*);
obj* l_Lean_Parser_List_nil_tokens___boxed(obj*);
obj* l_Lean_Parser_tryView___boxed(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1;
obj* l_Lean_Parser_parserCoreT_Monad___boxed(obj*);
obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parserCoreT_Alternative(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* _init_l_Lean_Parser_maxPrec() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1024ul);
return x_0;
}
}
obj* l_Lean_Parser_parserConfigCoe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Parser_parserConfigCoe___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_parserConfigCoe(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Monad___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_StateT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParsecT_Monad___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_Lean_Parser_parserCoreT_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parserCoreT_Monad___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_parserCoreT_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Alternative___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_StateT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParsecT_Alternative___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_Lean_Parser_parserCoreT_Alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parserCoreT_Alternative___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_parserCoreT_Alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_StateT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_Lean_Parser_MonadParsec___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_MonadExcept___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_StateT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParsecT_MonadExcept___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_Lean_Parser_parserCoreT_MonadExcept(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parserCoreT_MonadExcept___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_parserCoreT_MonadExcept___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_parserCoreT_MonadExcept(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParserT_Monad___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_parserCoreT_Monad___rarg(x_0);
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserT_Monad___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Monad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserT_Monad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Alternative___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = l_Lean_Parser_parserCoreT_Monad___rarg(x_0);
x_3 = l_Lean_Parser_parserCoreT_Alternative___rarg(x_0);
x_4 = l_ReaderT_Alternative___rarg(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_ParserT_Alternative(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserT_Alternative___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Alternative___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserT_Alternative(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadReader___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_parserCoreT_Monad___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadReader(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserT_MonadReader___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadReader___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserT_MonadReader(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_2 = l_Lean_Parser_parserCoreT_Monad___rarg(x_0);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_2);
lean::closure_set(x_6, 4, x_2);
x_7 = l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___rarg(x_0);
x_8 = l_Lean_Parser_monadParsecTrans___rarg(x_4, x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserT_Lean_Parser_MonadParsec(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadExcept___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_parserCoreT_MonadExcept___rarg(x_0);
x_2 = l_ReaderT_MonadExcept___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadExcept(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParserT_MonadExcept___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParserT_MonadExcept___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParserT_MonadExcept(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_BasicParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_BasicParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_Alternative___rarg(x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_BasicParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_MonadReader___rarg(x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_BasicParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_MonadExcept___rarg(x_9);
return x_10;
}
}
obj* l_Lean_Parser_getCache___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_getCache(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_getCache___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_getCache___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_getCache(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_putCache(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
}
}
obj* l_Lean_Parser_putCache___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_putCache(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_tokens___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_Parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tokens___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_HasTokens_Inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_HasTokens_Inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_HasTokens_Inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_List_nil_tokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_Parser_List_nil_tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_List_nil_tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_List_cons_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_tokens___rarg(x_0);
x_3 = l_Lean_Parser_tokens___rarg(x_1);
x_4 = l_List_append___rarg(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_List_cons_tokens(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_List_cons_tokens___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_List_cons_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_List_cons_tokens___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_List_cons_tokens(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_tryView___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_Syntax_isOfKind___main(x_0, x_2);
if (x_3 == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::apply_1(x_7, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_tryView(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tryView___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_tryView___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_tryView___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_tryView___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tryView(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_HasView_default___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_mjoin___rarg___closed__1;
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_HasView_default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_HasView_default___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_HasView_default___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_HasView_default___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_HasView_default___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_HasView_default(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_messageOfParsecMessage___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_12 = l_Lean_FileMap_toPosition(x_4, x_9);
x_13 = lean::box(0);
x_14 = l_Lean_Parser_Parsec_Message_text___rarg(x_1);
x_15 = 2;
x_16 = l_String_splitAux___main___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_12);
lean::cnstr_set(x_17, 2, x_13);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set(x_17, 4, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_15);
x_18 = x_17;
return x_18;
}
}
obj* l_Lean_Parser_messageOfParsecMessage(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_messageOfParsecMessage___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_messageOfParsecMessage___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_messageOfParsecMessage(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_6)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_6;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_4);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_32; obj* x_33; 
x_19 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_21 = x_1;
} else {
 lean::inc(x_19);
 lean::dec(x_1);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::is_scalar(x_21)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_21;
}
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_19);
x_33 = lean::apply_2(x_29, lean::box(0), x_32);
return x_33;
}
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::apply_2(x_3, x_8, x_6);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___boxed), 7, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_run___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_run___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_release(x_3, 1);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 3);
lean::inc(x_16);
x_18 = lean::apply_1(x_1, x_2);
x_19 = l_Lean_Parser_messageOfParsecMessage___rarg(x_18, x_13);
x_20 = l_Lean_MessageLog_empty;
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
if (lean::obj_tag(x_16) == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_Lean_Parser_run___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_6)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_6;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
x_24 = lean::apply_2(x_10, lean::box(0), x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
lean::dec(x_16);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_6)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_6;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_21);
x_30 = lean::apply_2(x_10, lean::box(0), x_29);
return x_30;
}
}
else
{
obj* x_34; obj* x_37; obj* x_40; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_4, 0);
lean::inc(x_34);
lean::dec(x_4);
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_43 = lean::cnstr_get(x_34, 0);
x_45 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 x_47 = x_34;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_34);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_48, 0, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
x_50 = lean::apply_2(x_40, lean::box(0), x_49);
return x_50;
}
}
}
obj* _init_l_Lean_Parser_run___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_Lean_Parser_run___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = l_Lean_MessageLog_empty;
lean::inc(x_2);
x_9 = lean::apply_2(x_4, x_7, x_2);
x_10 = l_String_splitAux___main___closed__1;
x_11 = l_Lean_Parser_run___rarg___closed__1;
lean::inc(x_0);
x_13 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg(x_0, lean::box(0), lean::box(0), x_9, x_3, x_10, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_run___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_2);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_Lean_Parser_run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_run___rarg), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_run___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_run___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_run(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_logMessage___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::apply_1(x_0, x_1);
x_5 = l_Lean_Parser_messageOfParsecMessage___rarg(x_4, x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_logMessage___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_logMessage___rarg___lambda__1), 4, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_3);
lean::closure_set(x_7, 2, x_2);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
}
obj* l_Lean_Parser_logMessage___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_logMessage___rarg___lambda__2), 4, 3);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_logMessage(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_logMessage___rarg), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_logMessage___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_logMessage(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid token '");
return x_0;
}
}
obj* _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', has been defined with precedences ");
return x_0;
}
}
obj* _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" and ");
return x_0;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_12 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_8, x_0, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
x_13 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_8, x_3, x_0, x_10);
lean::dec(x_8);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
else
{
obj* x_16; obj* x_19; uint8 x_21; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::nat_dec_eq(x_19, x_10);
if (x_21 == 0)
{
obj* x_22; uint8 x_25; 
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::dec(x_16);
x_25 = lean::nat_dec_eq(x_22, x_10);
if (x_25 == 0)
{
uint8 x_27; 
lean::dec(x_3);
x_27 = lean::nat_dec_eq(x_19, x_22);
if (x_27 == 0)
{
obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_5);
lean::dec(x_0);
x_30 = l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1;
x_31 = lean::string_append(x_30, x_8);
lean::dec(x_8);
x_33 = l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2;
x_34 = lean::string_append(x_31, x_33);
x_35 = l_Nat_repr(x_19);
x_36 = lean::string_append(x_34, x_35);
lean::dec(x_35);
x_38 = l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3;
x_39 = lean::string_append(x_36, x_38);
x_40 = l_Nat_repr(x_22);
x_41 = lean::string_append(x_39, x_40);
lean::dec(x_40);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_41);
return x_43;
}
else
{
lean::dec(x_8);
lean::dec(x_22);
lean::dec(x_19);
x_1 = x_5;
goto _start;
}
}
else
{
obj* x_50; 
lean::dec(x_22);
lean::dec(x_19);
x_50 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_8, x_3, x_0, x_10);
lean::dec(x_8);
x_0 = x_50;
x_1 = x_5;
goto _start;
}
}
else
{
obj* x_54; uint8 x_57; 
lean::dec(x_19);
x_54 = lean::cnstr_get(x_16, 1);
lean::inc(x_54);
lean::dec(x_16);
x_57 = lean::nat_dec_eq(x_54, x_10);
lean::dec(x_54);
if (x_57 == 0)
{
lean::dec(x_8);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_62; 
x_62 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_8, x_3, x_0, x_10);
lean::dec(x_8);
x_0 = x_62;
x_1 = x_5;
goto _start;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_mkTokenTrie___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("/-");
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_0);
x_4 = lean::mk_string("--");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_0);
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
obj* l_Lean_Parser_mkTokenTrie(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_mkTokenTrie___closed__1;
x_2 = l_List_append___rarg(x_1, x_0);
x_3 = l_Lean_Parser_Trie_empty___closed__1;
x_4 = l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
}
}
obj* _init_l_Lean_Parser_CommandParserM_Monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
x_11 = l_ReaderT_Monad___rarg(x_10);
x_12 = l_ReaderT_Monad___rarg(x_11);
return x_12;
}
}
obj* l_Lean_Parser_CommandParserM_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Monad___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_Alternative___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_ReaderT_Monad___rarg(x_11);
x_14 = l_Lean_Parser_parserCoreT_Alternative___rarg(x_9);
x_15 = l_ReaderT_Alternative___rarg(x_11, x_14);
x_16 = l_ReaderT_Alternative___rarg(x_13, x_15);
return x_16;
}
}
obj* l_Lean_Parser_CommandParserM_Alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Alternative___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_Alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_MonadReader___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
x_11 = l_ReaderT_Monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
return x_12;
}
}
obj* l_Lean_Parser_CommandParserM_MonadReader(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_MonadReader___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_MonadReader___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_MonadReader(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_ReaderT_Monad___rarg(x_11);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, x_13);
lean::inc(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_17, 0, lean::box(0));
lean::closure_set(x_17, 1, lean::box(0));
lean::closure_set(x_17, 2, lean::box(0));
lean::closure_set(x_17, 3, x_13);
lean::closure_set(x_17, 4, x_13);
x_18 = l_Lean_Parser_parserCoreT_Lean_Parser_MonadParsec___rarg(x_9);
x_19 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_11, lean::box(0), x_18);
x_20 = l_Lean_Parser_monadParsecTrans___rarg(x_15, x_17, x_19);
return x_20;
}
}
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_MonadExcept___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_parserCoreT_MonadExcept___rarg(x_9);
x_11 = l_ReaderT_MonadExcept___rarg(x_10);
x_12 = l_ReaderT_MonadExcept___rarg(x_11);
return x_12;
}
}
obj* l_Lean_Parser_CommandParserM_MonadExcept(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_MonadExcept___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_MonadExcept___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
x_11 = l_ReaderT_Monad___rarg(x_10);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_13, 0, lean::box(0));
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadRec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
lean::closure_set(x_15, 2, x_11);
return x_15;
}
}
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_parserCoreT_Monad___rarg(x_9);
x_11 = l_ReaderT_Monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_MonadReaderAdapter___boxed), 5, 4);
lean::closure_set(x_12, 0, lean::box(0));
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_11);
return x_12;
}
}
obj* l_Lean_Parser_CommandParserM_MonadReaderAdapter(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1;
return x_2;
}
}
obj* l_Lean_Parser_CommandParserM_MonadReaderAdapter___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_CommandParserM_MonadReaderAdapter(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_CommandParserM_basicParser___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::apply_1(x_0, x_3);
x_8 = lean::apply_3(x_2, x_7, x_5, x_6);
return x_8;
}
}
obj* l_Lean_Parser_CommandParserM_basicParser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_CommandParserM_basicParser___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_CommandParserM_basicParser___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_CommandParserM_basicParser___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_CommandParserM_basicParser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_CommandParserM_basicParser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TermParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_CommandParserM_Monad___closed__1;
x_1 = l_ReaderT_Monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TermParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_CommandParserM_Monad___closed__1;
x_1 = l_Lean_Parser_CommandParserM_Alternative___closed__1;
x_2 = l_ReaderT_Alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TermParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_CommandParserM_MonadReader___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_CommandParserM_Monad___closed__1;
x_1 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1;
x_2 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TermParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_CommandParserM_MonadExcept___closed__1;
x_1 = l_ReaderT_MonadExcept___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TermParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Lean_Parser_CommandParserM_Monad___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_CommandParserM_basicParser___rarg___boxed), 7, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg___boxed), 4, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = l_ReaderT_Monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = l_Lean_Parser_TermParserM_Alternative;
x_2 = l_ReaderT_Alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Lean_Parser_TermParserM_Monad;
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
x_3 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_4 = l_Lean_Parser_monadParsecTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_TermParserM_MonadExcept;
x_1 = l_ReaderT_MonadExcept___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadRec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_Lean_Parser_TermParserM_Lean_Parser_MonadRec;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadRec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
lean::closure_set(x_3, 2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_monadBasicParser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Lean_Parser_TermParserM_Monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hasMonadLiftTTrans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_trailingTermParserCoe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_trailingTermParserCoe___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_trailingTermParserCoe(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_34, x_1, x_2);
x_51 = l_RBNode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_RBNode_isRed___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_28, x_1, x_2);
x_60 = l_RBNode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_34, x_1, x_2);
x_51 = l_RBNode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_RBNode_isRed___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_28, x_1, x_2);
x_60 = l_RBNode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_34, x_1, x_2);
x_51 = l_RBNode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_RBNode_isRed___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_28, x_1, x_2);
x_60 = l_RBNode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Name_quickLt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_Name_quickLt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Name_quickLt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Lean_Name_quickLt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_6);
x_49 = x_48;
x_50 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_34, x_1, x_2);
x_51 = l_RBNode_balance2___main___rarg(x_49, x_50);
return x_51;
}
}
}
else
{
uint8 x_52; 
x_52 = l_RBNode_isRed___main___rarg(x_28);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_34);
lean::cnstr_set_scalar(x_54, sizeof(void*)*4, x_6);
x_55 = x_54;
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::box(0);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_36;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_6);
x_58 = x_57;
x_59 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_28, x_1, x_2);
x_60 = l_RBNode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_0);
x_4 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_0, x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_RBNode_isRed___main___rarg(x_0);
if (x_7 == 0)
{
obj* x_8; 
x_8 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_0, x_1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_10; 
x_9 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_0, x_1, x_6);
x_10 = l_RBNode_setBlack___main___rarg(x_9);
return x_10;
}
}
else
{
obj* x_11; obj* x_14; uint8 x_15; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_11);
x_15 = l_RBNode_isRed___main___rarg(x_0);
if (x_15 == 0)
{
obj* x_16; 
x_16 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_0, x_1, x_14);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_0, x_1, x_14);
x_18 = l_RBNode_setBlack___main___rarg(x_17);
return x_18;
}
}
}
}
obj* l_Lean_Parser_TokenMap_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_TokenMap_insert___rarg), 3, 0);
return x_1;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at_Lean_Parser_TokenMap_insert___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at_Lean_Parser_TokenMap_insert___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_TokenMap_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_ofList___main___rarg(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = l_Lean_Parser_TokenMap_ofList___main___rarg(x_4);
x_13 = l_Lean_Parser_TokenMap_insert___rarg(x_12, x_7, x_9);
return x_13;
}
}
}
obj* l_Lean_Parser_TokenMap_ofList___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_TokenMap_ofList___main___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_ofList___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_TokenMap_ofList___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_ofList___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_TokenMap_ofList___main___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_ofList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_TokenMap_ofList___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_TokenMap_ofList___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_TokenMap_ofList(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_tokenMapNil_tokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Lean_Parser_tokenMapNil_tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokenMapNil_tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_tokenMapCons_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_tokens___rarg(x_0);
x_3 = l_Lean_Parser_tokens___rarg(x_1);
x_4 = l_List_append___rarg(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_tokenMapCons_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_tokenMapCons_tokens___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_tokenMapCons_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokenMapCons_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_tokenMapCons_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_tokenMapCons_tokens(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_commandParserConfigCoeParserConfig(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Parser_commandParserConfigCoeParserConfig___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_commandParserConfigCoeParserConfig(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_lean_parser_parsec(obj*);
obj* initialize_init_lean_parser_syntax(obj*);
obj* initialize_init_lean_parser_rec(obj*);
obj* initialize_init_lean_parser_trie(obj*);
obj* initialize_init_lean_parser_identifier(obj*);
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_message(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_syntax(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_rec(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_trie(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_identifier(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_message(w);
 l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean::mark_persistent(l_Lean_Parser_maxPrec);
 l_Lean_Parser_BasicParserM_Monad = _init_l_Lean_Parser_BasicParserM_Monad();
lean::mark_persistent(l_Lean_Parser_BasicParserM_Monad);
 l_Lean_Parser_BasicParserM_Alternative = _init_l_Lean_Parser_BasicParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_BasicParserM_Alternative);
 l_Lean_Parser_BasicParserM_MonadReader = _init_l_Lean_Parser_BasicParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_BasicParserM_MonadReader);
 l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec);
 l_Lean_Parser_BasicParserM_MonadExcept = _init_l_Lean_Parser_BasicParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_BasicParserM_MonadExcept);
 l_Lean_Parser_run___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_run___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_run___rarg___lambda__1___closed__1);
 l_Lean_Parser_run___rarg___closed__1 = _init_l_Lean_Parser_run___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_run___rarg___closed__1);
 l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1 = _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__1);
 l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2 = _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__2);
 l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3 = _init_l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Parser_mkTokenTrie___spec__1___closed__3);
 l_Lean_Parser_mkTokenTrie___closed__1 = _init_l_Lean_Parser_mkTokenTrie___closed__1();
lean::mark_persistent(l_Lean_Parser_mkTokenTrie___closed__1);
 l_Lean_Parser_CommandParserM_Monad___closed__1 = _init_l_Lean_Parser_CommandParserM_Monad___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_Monad___closed__1);
 l_Lean_Parser_CommandParserM_Alternative___closed__1 = _init_l_Lean_Parser_CommandParserM_Alternative___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_Alternative___closed__1);
 l_Lean_Parser_CommandParserM_MonadReader___closed__1 = _init_l_Lean_Parser_CommandParserM_MonadReader___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_MonadReader___closed__1);
 l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1 = _init_l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec___closed__1);
 l_Lean_Parser_CommandParserM_MonadExcept___closed__1 = _init_l_Lean_Parser_CommandParserM_MonadExcept___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_MonadExcept___closed__1);
 l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1 = _init_l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_Lean_Parser_MonadRec___closed__1);
 l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1 = _init_l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1();
lean::mark_persistent(l_Lean_Parser_CommandParserM_MonadReaderAdapter___closed__1);
 l_Lean_Parser_TermParserM_Monad = _init_l_Lean_Parser_TermParserM_Monad();
lean::mark_persistent(l_Lean_Parser_TermParserM_Monad);
 l_Lean_Parser_TermParserM_Alternative = _init_l_Lean_Parser_TermParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_TermParserM_Alternative);
 l_Lean_Parser_TermParserM_MonadReader = _init_l_Lean_Parser_TermParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_TermParserM_MonadReader);
 l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec);
 l_Lean_Parser_TermParserM_MonadExcept = _init_l_Lean_Parser_TermParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_TermParserM_MonadExcept);
 l_Lean_Parser_TermParserM_Lean_Parser_MonadRec = _init_l_Lean_Parser_TermParserM_Lean_Parser_MonadRec();
lean::mark_persistent(l_Lean_Parser_TermParserM_Lean_Parser_MonadRec);
 l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser = _init_l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser();
lean::mark_persistent(l_Lean_Parser_TermParserM_Lean_Parser_monadBasicParser);
 l_Lean_Parser_TrailingTermParserM_Monad = _init_l_Lean_Parser_TrailingTermParserM_Monad();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_Monad);
 l_Lean_Parser_TrailingTermParserM_Alternative = _init_l_Lean_Parser_TrailingTermParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_Alternative);
 l_Lean_Parser_TrailingTermParserM_MonadReader = _init_l_Lean_Parser_TrailingTermParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_MonadReader);
 l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadParsec);
 l_Lean_Parser_TrailingTermParserM_MonadExcept = _init_l_Lean_Parser_TrailingTermParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_MonadExcept);
 l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadRec = _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadRec();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_Lean_Parser_MonadRec);
 l_Lean_Parser_TrailingTermParserM_Lean_Parser_monadBasicParser = _init_l_Lean_Parser_TrailingTermParserM_Lean_Parser_monadBasicParser();
lean::mark_persistent(l_Lean_Parser_TrailingTermParserM_Lean_Parser_monadBasicParser);
return w;
}
