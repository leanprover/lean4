// Lean compiler output
// Module: init.lean.parser.module
// Imports: init.lean.parser.command
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
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__2(obj*);
extern obj* l_Lean_Parser_command_Parser___rarg___closed__1;
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__2(obj*);
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l___private_init_lean_parser_module_1__commandWrecAux(uint8, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_MessageLog_empty;
obj* l_Lean_Parser_ModuleParserM_Alternative;
obj* l_Lean_Parser_ModuleParserM_MonadReader;
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_id___boxed(obj*);
obj* l_Lean_Parser_commandParser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_ModuleParserM_Monad;
obj* l_Lean_Parser_ModuleParserM_liftParserT___boxed(obj*);
obj* l_Lean_Parser_resumeModuleParser___boxed(obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(obj*);
extern usize l_String_toSubstring___closed__1;
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1(obj*, obj*);
obj* l_Lean_Parser_parseHeader___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_ParserT_Alternative___rarg(obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_Module_header;
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l_StateT_Monad___rarg(obj*);
extern obj* l_Lean_Parser_run___rarg___closed__1;
obj* l_Lean_Parser_moduleParserConfigCoe(obj*);
obj* l_StateT_lift___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__1(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_HasView;
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_ParserT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
obj* l_Lean_Parser_Module_prelude_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___boxed(obj*, obj*);
obj* l_Option_get___main___at_Lean_Parser_run___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(obj*);
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27;
obj* l_Lean_Parser_Module_import_HasView;
obj* l_Lean_Parser_ModuleParserM_BasicParserM___boxed(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_resumeModuleParser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Module_parseCommandWithRecovery___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_parseCommandWithRecovery(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_commandParserConfigCoeParserConfig___boxed(obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import_Parser(obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_eoi_Parser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__2(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_parseHeader___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_eoi_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_Module_import;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_String_OldIterator_toEnd___main(obj*);
obj* l_Lean_Parser_Module_header_HasView;
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
obj* l_Lean_Parser_ModuleParserM_MonadState;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_parseHeader___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_eoi;
obj* l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec;
obj* l_coeB___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27;
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_StateT_MonadExcept___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHeader___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_Module_prelude_Parser___closed__1;
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_liftParserT___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_Module_import_Parser___closed__1;
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserT_Monad___rarg(obj*);
obj* l_Lean_Parser_moduleParserConfigCoe___boxed(obj*);
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_StateT_MonadFunctor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_resumeModuleParser___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath;
obj* l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView;
obj* l___private_init_lean_parser_module_1__commandWrecAux___main(uint8, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseHeader___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseHeader___closed__1;
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_ModuleParserM_MonadExcept;
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
obj* l_Lean_Parser_Module_importPath_HasView;
obj* l_Lean_Parser_resumeModuleParser(obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5;
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_command_Parser___boxed(obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___boxed(obj*);
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens;
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*, obj*);
obj* l_id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_coeTrans___rarg(obj*, obj*, obj*);
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_liftParserT(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1;
obj* l_coeT___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1(obj*);
obj* l_id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_parseCommand(obj*, obj*);
obj* l_Lean_Parser_messageOfParsecMessage___rarg(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_Module_prelude;
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4;
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1;
obj* l_id_bind___boxed(obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_liftParserT___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseCommand___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Module_header_HasView_x_27;
obj* l_StateT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1;
obj* l_String_quote(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_ParserT_MonadReader___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_StateT_MonadState___rarg(obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
extern obj* l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
obj* l_Lean_Parser_Module_prelude_HasView_x_27;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__1(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHeader(obj*);
obj* l_Lean_Parser_moduleParserConfigCoe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Parser_moduleParserConfigCoe___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_moduleParserConfigCoe(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
x_11 = l_StateT_Monad___rarg(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
x_12 = l_Lean_Parser_ParserT_Alternative___rarg(x_9);
x_13 = l_StateT_Alternative___rarg(x_11, x_12);
return x_13;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
x_12 = l_Lean_Parser_ParserT_MonadReader___rarg(x_9);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg___boxed), 4, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, lean::box(0));
lean::closure_set(x_13, 2, x_12);
return x_13;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadState() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
x_11 = l_StateT_MonadState___rarg(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg___boxed), 4, 1);
lean::closure_set(x_13, 0, x_11);
lean::inc(x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, lean::box(0));
lean::closure_set(x_15, 3, x_11);
lean::closure_set(x_15, 4, x_11);
x_16 = l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(x_9);
x_17 = l_Lean_Parser_monadParsecTrans___rarg(x_13, x_15, x_16);
return x_17;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_Lean_Parser_ParserT_Monad___rarg(x_9);
x_12 = l_Lean_Parser_ParserT_MonadExcept___rarg(x_9);
x_13 = l_StateT_MonadExcept___rarg(x_11, lean::box(0), x_12);
return x_13;
}
}
obj* l_Lean_Parser_ModuleParserM_liftParserT___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::apply_1(x_0, x_4);
x_8 = lean::apply_3(x_2, x_7, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
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
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_3);
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
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
return x_25;
}
else
{
obj* x_27; obj* x_29; obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_3);
x_27 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_29 = x_8;
} else {
 lean::inc(x_27);
 lean::dec(x_8);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_9, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_33 = x_9;
} else {
 lean::inc(x_30);
 lean::dec(x_9);
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
obj* l_Lean_Parser_ModuleParserM_liftParserT(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ModuleParserM_liftParserT___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_ModuleParserM_liftParserT___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ModuleParserM_liftParserT___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_ModuleParserM_liftParserT___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ModuleParserM_liftParserT(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_BasicParserM___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_commandParserConfigCoeParserConfig___boxed), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coeB___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_moduleParserConfigCoe___boxed), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeTrans___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coeT___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ModuleParserM_liftParserT___rarg___boxed), 7, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Parser_ModuleParserM_BasicParserM(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ModuleParserM_BasicParserM___closed__1;
return x_2;
}
}
obj* l_Lean_Parser_ModuleParserM_BasicParserM___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ModuleParserM_BasicParserM(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_prelude() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("prelude");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1() {
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
x_5 = l_Lean_Parser_Module_prelude;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1;
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
x_12 = l_Lean_Parser_Module_prelude;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
return x_13;
}
}
}
obj* _init_l_Lean_Parser_Module_prelude_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_prelude_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Module_prelude_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::mk_string("prelude");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_BasicParserM_Monad;
x_10 = l_Lean_Parser_BasicParserM_MonadExcept;
x_11 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_BasicParserM_Alternative;
x_13 = l_Lean_Parser_Module_prelude;
x_14 = l_Lean_Parser_Module_prelude_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_0 = lean::mk_string("prelude");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_4);
lean::dec(x_2);
x_7 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("prelude");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Module_prelude_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Module_prelude;
x_4 = l_Lean_Parser_Module_prelude_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_importPath() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("importPath");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__1(x_4);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_6)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_6;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
case 3:
{
obj* x_13; obj* x_14; 
x_13 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_17; 
lean::dec(x_2);
x_16 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_6;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__2(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__2(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_10 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_12 = x_2;
} else {
 lean::inc(x_10);
 lean::dec(x_2);
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
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
}
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("NOTAnIdent");
lean::inc(x_3);
x_5 = l_Lean_Parser_Substring_ofString(x_3);
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_3);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_7);
lean::cnstr_set(x_8, 3, x_1);
lean::cnstr_set(x_8, 4, x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__1(x_6);
x_10 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4;
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
x_18 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_18) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
lean::dec(x_1);
switch (lean::obj_tag(x_20)) {
case 1:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_23);
return x_27;
}
case 3:
{
obj* x_28; 
x_28 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2;
return x_28;
}
default:
{
obj* x_30; 
lean::dec(x_20);
x_30 = l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2;
return x_30;
}
}
}
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_18, 0);
lean::inc(x_31);
lean::dec(x_18);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__1(x_34);
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; obj* x_39; 
x_38 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
switch (lean::obj_tag(x_40)) {
case 1:
{
obj* x_43; obj* x_46; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
case 3:
{
obj* x_47; obj* x_48; 
x_47 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_37);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
default:
{
obj* x_50; obj* x_51; 
lean::dec(x_40);
x_50 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_37);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x_27___spec__2(x_1);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_Module_importPath;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Module_importPath_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8 x_13; 
x_13 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_13 == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_16 = x_5;
} else {
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_mjoin___rarg___closed__1;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
lean::cnstr_set(x_27, 2, x_25);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_14);
return x_28;
}
else
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_2);
x_30 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_32 = x_5;
} else {
 lean::inc(x_30);
 lean::dec(x_5);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_6);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_18);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_1);
x_39 = lean::box(0);
x_40 = l_String_splitAux___main___closed__1;
x_41 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_42 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_40, x_41, x_38, x_39, x_0, x_13, x_8);
lean::dec(x_13);
lean::dec(x_0);
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
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_46);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
x_54 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_53, x_41);
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
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_0);
x_59 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_61 = x_5;
} else {
 lean::inc(x_59);
 lean::dec(x_5);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_6, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_65 = x_6;
} else {
 lean::inc(x_62);
 lean::dec(x_6);
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
x_70 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_5, x_0, x_2, x_3, x_4);
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
x_18 = l_Lean_Parser_mkRawRes(x_1, x_12);
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
lean::dec(x_1);
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
obj* _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string(".");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2), 3, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_BasicParserM_Monad;
x_13 = l_Lean_Parser_BasicParserM_MonadExcept;
x_14 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_15 = l_Lean_Parser_BasicParserM_Alternative;
x_16 = l_Lean_Parser_Module_importPath;
x_17 = l_Lean_Parser_Module_importPath_HasView;
x_18 = l_Lean_Parser_Combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
lean::dec(x_11);
return x_18;
}
}
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_0);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_importPath_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string(".");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2), 3, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Module_importPath_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Module_importPath;
x_4 = l_Lean_Parser_Module_importPath_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_import() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("import");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_Module_importPath_HasView;
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
obj* _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_Module_importPath_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
x_12 = l_List_map___main___rarg(x_11, x_8);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_5;
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
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; 
x_13 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_13;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::box(0);
x_1 = x_17;
x_2 = x_14;
goto lbl_3;
}
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_20; obj* x_23; obj* x_26; 
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = lean::cnstr_get(x_18, 0);
lean::inc(x_23);
lean::dec(x_18);
if (lean::is_scalar(x_8)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_8;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::obj_tag(x_20) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(3);
x_28 = l_Lean_Parser_Syntax_asNode___main(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
x_29 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
x_38 = l_List_map___main___rarg(x_37, x_34);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_26);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_20, 0);
lean::inc(x_40);
lean::dec(x_20);
x_1 = x_26;
x_2 = x_40;
goto lbl_3;
}
}
case 3:
{
obj* x_44; 
lean::dec(x_8);
x_44 = lean::cnstr_get(x_9, 1);
lean::inc(x_44);
lean::dec(x_9);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; 
x_47 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_47;
}
else
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
lean::dec(x_44);
x_51 = lean::box(0);
x_1 = x_51;
x_2 = x_48;
goto lbl_3;
}
}
default:
{
obj* x_54; 
lean::dec(x_8);
lean::dec(x_18);
x_54 = lean::cnstr_get(x_9, 1);
lean::inc(x_54);
lean::dec(x_9);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; 
x_57 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_57;
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_54, 0);
lean::inc(x_58);
lean::dec(x_54);
x_61 = lean::box(0);
x_1 = x_61;
x_2 = x_58;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_62; 
x_62 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; 
x_63 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_1);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_68; obj* x_71; obj* x_72; obj* x_73; 
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
lean::dec(x_62);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
x_71 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
x_72 = l_List_map___main___rarg(x_71, x_68);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_1);
lean::cnstr_set(x_73, 1, x_72);
return x_73;
}
}
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_Module_importPath_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1;
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
x_12 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_Parser_Module_import;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::box(3);
x_22 = l_Option_getOrElse___main___rarg(x_20, x_21);
lean::dec(x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_11);
x_25 = l_Lean_Parser_Module_import;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
return x_26;
}
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Module_import_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string("import");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser), 3, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_BasicParserM_Monad;
x_13 = l_Lean_Parser_BasicParserM_MonadExcept;
x_14 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_15 = l_Lean_Parser_BasicParserM_Alternative;
x_16 = l_Lean_Parser_Module_import;
x_17 = l_Lean_Parser_Module_import_HasView;
x_18 = l_Lean_Parser_Combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
lean::dec(x_11);
return x_18;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_12; 
x_0 = lean::mk_string("import");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
x_12 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
return x_12;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string("import");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser), 3, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Module_import_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Module_import;
x_4 = l_Lean_Parser_Module_import_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_header() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("header");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_Module_import_HasView;
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
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_Module_import_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_Module_prelude_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
x_17 = l_List_map___main___rarg(x_16, x_13);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_Module_prelude_HasView;
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
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
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
x_11 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
x_12 = l_List_map___main___rarg(x_11, x_8);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3;
return x_2;
}
else
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5;
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
x_14 = l_Lean_Parser_Module_prelude_HasView;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_18 = lean::apply_1(x_15, x_12);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_5);
x_21 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
x_24 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
x_25 = l_List_map___main___rarg(x_24, x_5);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
else
{
obj* x_30; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_10);
x_30 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3;
return x_30;
}
}
}
}
}
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6;
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
x_22 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
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
x_30 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
x_31 = l_List_map___main___rarg(x_30, x_27);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
lbl_6:
{
obj* x_33; 
x_33 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_33) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3;
return x_34;
}
else
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_4, 0);
lean::inc(x_35);
lean::dec(x_4);
x_38 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4;
x_1 = x_38;
x_2 = x_35;
goto lbl_3;
}
}
else
{
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_42) == 0)
{
lean::dec(x_41);
if (lean::obj_tag(x_4) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5;
return x_46;
}
else
{
obj* x_47; obj* x_50; 
x_47 = lean::cnstr_get(x_4, 0);
lean::inc(x_47);
lean::dec(x_4);
x_50 = lean::box(0);
x_1 = x_50;
x_2 = x_47;
goto lbl_3;
}
}
else
{
obj* x_51; 
x_51 = lean::cnstr_get(x_42, 1);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_53; obj* x_56; obj* x_57; obj* x_60; obj* x_61; 
x_53 = lean::cnstr_get(x_42, 0);
lean::inc(x_53);
lean::dec(x_42);
x_56 = l_Lean_Parser_Module_prelude_HasView;
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
lean::dec(x_56);
x_60 = lean::apply_1(x_57, x_53);
if (lean::is_scalar(x_41)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_41;
}
lean::cnstr_set(x_61, 0, x_60);
if (lean::obj_tag(x_4) == 0)
{
obj* x_62; obj* x_63; 
x_62 = lean::box(3);
x_63 = l_Lean_Parser_Syntax_asNode___main(x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; 
x_64 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1;
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
x_72 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2;
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
else
{
lean::dec(x_51);
lean::dec(x_41);
lean::dec(x_42);
if (lean::obj_tag(x_4) == 0)
{
obj* x_81; 
x_81 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3;
return x_81;
}
else
{
obj* x_82; obj* x_85; 
x_82 = lean::cnstr_get(x_4, 0);
lean::inc(x_82);
lean::dec(x_4);
x_85 = l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4;
x_1 = x_85;
x_2 = x_82;
goto lbl_3;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_Module_import_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1;
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
x_14 = l_Lean_Parser_Module_header;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_Lean_Parser_Module_prelude_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_10);
x_25 = l_Lean_Parser_Syntax_mkNode(x_8, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
x_27 = l_Lean_Parser_Module_header;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_header_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_header_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Module_header_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_7 = lean::box(0);
lean::inc(x_2);
x_12 = lean::apply_3(x_0, x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
x_22 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_24 = x_13;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_13);
 x_24 = lean::box(0);
}
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_18);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_24)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_24;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_20);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_27);
x_8 = x_28;
x_9 = x_15;
goto lbl_10;
}
else
{
obj* x_29; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::cnstr_get(x_12, 1);
lean::inc(x_29);
lean::dec(x_12);
x_32 = lean::cnstr_get(x_13, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_35 = x_13;
} else {
 lean::inc(x_32);
 lean::dec(x_13);
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
x_8 = x_37;
x_9 = x_29;
goto lbl_10;
}
}
else
{
obj* x_38; obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_38 = lean::cnstr_get(x_12, 1);
lean::inc(x_38);
lean::dec(x_12);
x_41 = lean::cnstr_get(x_13, 0);
x_43 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_44 = x_13;
} else {
 lean::inc(x_41);
 lean::dec(x_13);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_41, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_41, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_41, 2);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_41, 3);
lean::inc(x_51);
lean::dec(x_41);
x_54 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_51);
lean::dec(x_51);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_Lean_Parser_noKind;
x_59 = l_Lean_Parser_Syntax_mkNode(x_58, x_57);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_45);
lean::cnstr_set(x_61, 1, x_47);
lean::cnstr_set(x_61, 2, x_49);
lean::cnstr_set(x_61, 3, x_60);
if (x_43 == 0)
{
uint8 x_62; obj* x_63; obj* x_64; 
x_62 = 0;
if (lean::is_scalar(x_44)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_44;
}
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_62);
x_64 = x_63;
x_8 = x_64;
x_9 = x_38;
goto lbl_10;
}
else
{
obj* x_65; obj* x_66; 
if (lean::is_scalar(x_44)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_44;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_43);
x_66 = x_65;
x_8 = x_66;
x_9 = x_38;
goto lbl_10;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_67; 
x_67 = lean::cnstr_get(x_4, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_69 = lean::cnstr_get(x_4, 1);
x_71 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_73 = x_4;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_4);
 x_73 = lean::box(0);
}
x_74 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_75 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_5);
return x_78;
}
else
{
obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_79 = lean::cnstr_get(x_4, 1);
x_81 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_83 = x_4;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_4);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_67, 0);
lean::inc(x_84);
lean::dec(x_67);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_84);
lean::cnstr_set(x_88, 1, x_87);
x_89 = l_Lean_Parser_noKind;
x_90 = l_Lean_Parser_Syntax_mkNode(x_89, x_88);
x_91 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_83)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_83;
}
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_79);
lean::cnstr_set(x_92, 2, x_91);
x_93 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_5);
return x_94;
}
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
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
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_2);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
else
{
uint8 x_103; 
x_103 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_103 == 0)
{
obj* x_104; obj* x_107; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_104 = lean::cnstr_get(x_8, 0);
lean::inc(x_104);
lean::dec(x_8);
x_107 = lean::cnstr_get(x_104, 2);
lean::inc(x_107);
lean::dec(x_104);
x_110 = l_mjoin___rarg___closed__1;
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_111, 0, x_107);
lean::closure_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_113, 0, x_7);
lean::cnstr_set(x_113, 1, x_2);
lean::cnstr_set(x_113, 2, x_112);
x_4 = x_113;
x_5 = x_9;
goto lbl_6;
}
else
{
lean::dec(x_2);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_BasicParserM_Monad;
x_8 = l_Lean_Parser_BasicParserM_MonadExcept;
x_9 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_10 = l_Lean_Parser_BasicParserM_Alternative;
x_11 = l_Lean_Parser_Module_header;
x_12 = l_Lean_Parser_Module_header_HasView;
x_13 = l_Lean_Parser_Combinators_node_view___rarg(x_7, x_8, x_9, x_10, x_11, x_6, x_12);
lean::dec(x_6);
return x_13;
}
}
obj* _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_10; 
x_0 = l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_tokens___rarg(x_2);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_4);
lean::dec(x_3);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_10 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_10;
}
}
obj* _init_l_Lean_Parser_Module_header_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Module_header_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Module_header;
x_4 = l_Lean_Parser_Module_header_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_eoi() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Module");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("eoi");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed), 8, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1() {
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
lean::closure_set(x_4, 0, x_3);
lean::closure_set(x_4, 1, x_0);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_4);
if (x_6 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = lean::string_append(x_11, x_10);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_16 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_13, x_15, x_14, x_14, x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 0);
x_21 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
x_24 = l_Lean_Parser_finishCommentBlock___closed__2;
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_19);
if (lean::is_scalar(x_23)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_23;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_21);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_0);
x_29 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
return x_31;
}
}
}
obj* l_Lean_Parser_Module_eoi_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(x_0, x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_16 = x_5;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
} else {
 lean::inc(x_17);
 lean::dec(x_7);
 x_19 = lean::box(0);
}
lean::inc(x_12);
x_21 = l_String_OldIterator_toEnd___main(x_12);
lean::inc(x_21);
lean::inc(x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_21);
x_25 = lean::cnstr_get(x_21, 1);
lean::inc(x_25);
lean::dec(x_21);
lean::inc(x_24);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_24);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = l_String_splitAux___main___closed__1;
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_Module_eoi;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
if (lean::is_scalar(x_19)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_19;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_17);
x_39 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_16)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_16;
}
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_12);
lean::cnstr_set(x_40, 2, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_40);
if (lean::is_scalar(x_11)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_11;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_9);
return x_42;
}
else
{
obj* x_43; obj* x_45; obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_45 = x_4;
} else {
 lean::inc(x_43);
 lean::dec(x_4);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_5, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_49 = x_5;
} else {
 lean::inc(x_46);
 lean::dec(x_5);
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
if (lean::is_scalar(x_45)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_45;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_43);
return x_52;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Module_eoi_Parser___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Module_eoi_Parser(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_Lean_Parser_messageOfParsecMessage___rarg(x_11, x_0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_4);
return x_20;
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_Lean_Parser_messageOfParsecMessage___rarg(x_11, x_0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_4);
return x_20;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_6, x_7, x_5, x_5, x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Parser_finishCommentBlock___closed__2;
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
x_19 = l_String_OldIterator_curr___main(x_2);
x_20 = l_True_Decidable;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_21 = l_Char_quoteCore(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_25 = lean::string_append(x_23, x_22);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
x_28 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_25, x_27, x_26, x_26, x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_28, 0);
x_33 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_35 = x_28;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_28);
 x_35 = lean::box(0);
}
x_36 = l_Lean_Parser_finishCommentBlock___closed__2;
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_31);
if (lean::is_scalar(x_35)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_35;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_33);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = l_String_OldIterator_next___main(x_2);
x_40 = lean::box(0);
x_41 = lean::box_uint32(x_19);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_0);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
lean::cnstr_set(x_43, 2, x_40);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_3);
return x_44;
}
}
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = 1;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_Parser___boxed), 1, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___main(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_17; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
x_10 = l_String_OldIterator_remaining___main(x_4);
x_17 = lean::nat_dec_eq(x_10, x_6);
lean::dec(x_10);
if (x_17 == 0)
{
if (x_0 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 0);
lean::inc(x_24);
x_26 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
lean::inc(x_4);
x_28 = l_Lean_Parser_commandParser_run(x_22, x_26, x_24, x_4, x_5);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_31 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 x_33 = x_28;
} else {
 lean::inc(x_31);
 lean::dec(x_28);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_29, 0);
x_36 = lean::cnstr_get(x_29, 1);
x_38 = lean::cnstr_get(x_29, 2);
if (lean::is_exclusive(x_29)) {
 x_40 = x_29;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_29);
 x_40 = lean::box(0);
}
lean::inc(x_2);
if (lean::is_scalar(x_33)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_33;
}
lean::cnstr_set(x_42, 0, x_34);
lean::cnstr_set(x_42, 1, x_2);
x_43 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_40)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_40;
}
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_36);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_46 = lean::cnstr_get(x_45, 0);
x_48 = lean::cnstr_get(x_45, 1);
x_50 = lean::cnstr_get(x_45, 2);
if (lean::is_exclusive(x_45)) {
 x_52 = x_45;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_45);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_46, 0);
x_55 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_57 = x_46;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_46);
 x_57 = lean::box(0);
}
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_53);
x_59 = 0;
x_60 = lean::box(x_59);
if (lean::is_scalar(x_57)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_57;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_63 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_63 = x_52;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_48);
lean::cnstr_set(x_63, 2, x_43);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_63);
x_65 = l_Lean_Parser_finishCommentBlock___closed__2;
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_64);
x_19 = x_66;
x_20 = x_31;
goto lbl_21;
}
else
{
obj* x_67; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_67 = lean::cnstr_get(x_45, 0);
x_69 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 x_70 = x_45;
} else {
 lean::inc(x_67);
 lean::dec(x_45);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_69);
x_72 = x_71;
x_73 = l_Lean_Parser_finishCommentBlock___closed__2;
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_72);
x_19 = x_74;
x_20 = x_31;
goto lbl_21;
}
}
else
{
obj* x_75; obj* x_78; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_75 = lean::cnstr_get(x_28, 1);
lean::inc(x_75);
lean::dec(x_28);
x_78 = lean::cnstr_get(x_29, 0);
x_80 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 x_81 = x_29;
} else {
 lean::inc(x_78);
 lean::dec(x_29);
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
x_84 = l_Lean_Parser_finishCommentBlock___closed__2;
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_84, x_83);
x_19 = x_85;
x_20 = x_75;
goto lbl_21;
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
lean::dec(x_4);
x_14 = x_19;
x_15 = x_20;
goto lbl_16;
}
else
{
uint8 x_87; 
x_87 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (x_87 == 0)
{
obj* x_88; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_98; obj* x_99; obj* x_101; obj* x_104; obj* x_105; 
x_88 = lean::cnstr_get(x_19, 0);
lean::inc(x_88);
lean::dec(x_19);
x_91 = l_String_splitAux___main___closed__1;
x_92 = l_Lean_Parser_command_Parser___rarg___closed__1;
x_93 = l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
lean::inc(x_4);
x_95 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_95, 0, x_4);
lean::cnstr_set(x_95, 1, x_91);
lean::cnstr_set(x_95, 2, x_92);
lean::cnstr_set(x_95, 3, x_93);
lean::inc(x_3);
lean::inc(x_2);
x_98 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(x_95, x_2, x_3, x_4, x_20);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
x_104 = l_Lean_Parser_finishCommentBlock___closed__2;
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_99);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_108; obj* x_110; obj* x_113; obj* x_114; obj* x_116; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_128; obj* x_129; 
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_105, 2);
lean::inc(x_110);
lean::dec(x_105);
x_116 = lean::cnstr_get(x_106, 1);
lean::inc(x_116);
lean::dec(x_106);
x_122 = lean::cnstr_get(x_3, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_122, 0);
lean::inc(x_124);
lean::dec(x_122);
lean::inc(x_108);
x_128 = l_Lean_Parser_token(x_124, x_108, x_101);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_131 = lean::cnstr_get(x_128, 1);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 x_133 = x_128;
} else {
 lean::inc(x_131);
 lean::dec(x_128);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_129, 0);
x_136 = lean::cnstr_get(x_129, 1);
x_138 = lean::cnstr_get(x_129, 2);
if (lean::is_exclusive(x_129)) {
 x_140 = x_129;
} else {
 lean::inc(x_134);
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_129);
 x_140 = lean::box(0);
}
lean::inc(x_116);
if (lean::is_scalar(x_133)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_133;
}
lean::cnstr_set(x_142, 0, x_134);
lean::cnstr_set(x_142, 1, x_116);
x_143 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_140)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_140;
}
lean::cnstr_set(x_144, 0, x_142);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_138, x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_146 = lean::cnstr_get(x_145, 0);
x_148 = lean::cnstr_get(x_145, 1);
x_150 = lean::cnstr_get(x_145, 2);
if (lean::is_exclusive(x_145)) {
 x_152 = x_145;
} else {
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_145);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_146, 1);
if (lean::is_exclusive(x_146)) {
 lean::cnstr_release(x_146, 0);
 x_155 = x_146;
} else {
 lean::inc(x_153);
 lean::dec(x_146);
 x_155 = lean::box(0);
}
x_156 = lean::box(0);
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_153);
if (lean::is_scalar(x_152)) {
 x_158 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_158 = x_152;
}
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_148);
lean::cnstr_set(x_158, 2, x_143);
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_150, x_158);
x_160 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_159);
x_119 = x_160;
x_120 = x_131;
goto lbl_121;
}
else
{
obj* x_161; obj* x_163; uint8 x_164; obj* x_165; obj* x_166; 
x_161 = lean::cnstr_get(x_145, 0);
if (lean::is_exclusive(x_145)) {
 x_163 = x_145;
} else {
 lean::inc(x_161);
 lean::dec(x_145);
 x_163 = lean::box(0);
}
x_164 = 0;
if (lean::is_scalar(x_163)) {
 x_165 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_165 = x_163;
}
lean::cnstr_set(x_165, 0, x_161);
lean::cnstr_set_scalar(x_165, sizeof(void*)*1, x_164);
x_166 = x_165;
x_119 = x_166;
x_120 = x_131;
goto lbl_121;
}
}
else
{
obj* x_167; obj* x_170; obj* x_172; uint8 x_173; obj* x_174; obj* x_175; 
x_167 = lean::cnstr_get(x_128, 1);
lean::inc(x_167);
lean::dec(x_128);
x_170 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_172 = x_129;
} else {
 lean::inc(x_170);
 lean::dec(x_129);
 x_172 = lean::box(0);
}
x_173 = 0;
if (lean::is_scalar(x_172)) {
 x_174 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_174 = x_172;
}
lean::cnstr_set(x_174, 0, x_170);
lean::cnstr_set_scalar(x_174, sizeof(void*)*1, x_173);
x_175 = x_174;
x_119 = x_175;
x_120 = x_167;
goto lbl_121;
}
lbl_115:
{
if (lean::obj_tag(x_113) == 0)
{
obj* x_176; obj* x_178; obj* x_180; obj* x_182; obj* x_183; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_176 = lean::cnstr_get(x_113, 0);
x_178 = lean::cnstr_get(x_113, 1);
x_180 = lean::cnstr_get(x_113, 2);
if (lean::is_exclusive(x_113)) {
 x_182 = x_113;
} else {
 lean::inc(x_176);
 lean::inc(x_178);
 lean::inc(x_180);
 lean::dec(x_113);
 x_182 = lean::box(0);
}
x_183 = lean::cnstr_get(x_176, 1);
if (lean::is_exclusive(x_176)) {
 lean::cnstr_release(x_176, 0);
 x_185 = x_176;
} else {
 lean::inc(x_183);
 lean::dec(x_176);
 x_185 = lean::box(0);
}
x_186 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
if (lean::is_scalar(x_185)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_185;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_183);
x_188 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_182)) {
 x_189 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_189 = x_182;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_178);
lean::cnstr_set(x_189, 2, x_188);
x_190 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_180, x_189);
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_190);
x_192 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_88, x_191);
x_14 = x_192;
x_15 = x_114;
goto lbl_16;
}
else
{
obj* x_193; uint8 x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
x_193 = lean::cnstr_get(x_113, 0);
x_195 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
if (lean::is_exclusive(x_113)) {
 x_196 = x_113;
} else {
 lean::inc(x_193);
 lean::dec(x_113);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_193);
lean::cnstr_set_scalar(x_197, sizeof(void*)*1, x_195);
x_198 = x_197;
x_199 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_198);
x_200 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_88, x_199);
x_14 = x_200;
x_15 = x_114;
goto lbl_16;
}
}
lbl_121:
{
if (lean::obj_tag(x_119) == 0)
{
lean::dec(x_108);
lean::dec(x_116);
x_113 = x_119;
x_114 = x_120;
goto lbl_115;
}
else
{
uint8 x_203; 
x_203 = lean::cnstr_get_scalar<uint8>(x_119, sizeof(void*)*1);
if (x_203 == 0)
{
obj* x_204; obj* x_207; obj* x_208; 
x_204 = lean::cnstr_get(x_119, 0);
lean::inc(x_204);
lean::dec(x_119);
x_207 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_116, x_3, x_108, x_120);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
if (lean::obj_tag(x_208) == 0)
{
obj* x_210; obj* x_212; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_210 = lean::cnstr_get(x_208, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_207, 1);
lean::inc(x_212);
lean::dec(x_207);
x_215 = lean::cnstr_get(x_208, 1);
x_217 = lean::cnstr_get(x_208, 2);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 x_219 = x_208;
} else {
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_208);
 x_219 = lean::box(0);
}
x_220 = lean::cnstr_get(x_210, 1);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_release(x_210, 0);
 x_222 = x_210;
} else {
 lean::inc(x_220);
 lean::dec(x_210);
 x_222 = lean::box(0);
}
x_223 = lean::box(0);
if (lean::is_scalar(x_222)) {
 x_224 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_224 = x_222;
}
lean::cnstr_set(x_224, 0, x_223);
lean::cnstr_set(x_224, 1, x_220);
x_225 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_219)) {
 x_226 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_226 = x_219;
}
lean::cnstr_set(x_226, 0, x_224);
lean::cnstr_set(x_226, 1, x_215);
lean::cnstr_set(x_226, 2, x_225);
x_227 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_217, x_226);
x_228 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_204, x_227);
x_113 = x_228;
x_114 = x_212;
goto lbl_115;
}
else
{
obj* x_229; obj* x_232; uint8 x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
x_229 = lean::cnstr_get(x_207, 1);
lean::inc(x_229);
lean::dec(x_207);
x_232 = lean::cnstr_get(x_208, 0);
x_234 = lean::cnstr_get_scalar<uint8>(x_208, sizeof(void*)*1);
if (lean::is_exclusive(x_208)) {
 x_235 = x_208;
} else {
 lean::inc(x_232);
 lean::dec(x_208);
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
x_238 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_204, x_237);
x_113 = x_238;
x_114 = x_229;
goto lbl_115;
}
}
else
{
lean::dec(x_108);
lean::dec(x_116);
x_113 = x_119;
x_114 = x_120;
goto lbl_115;
}
}
}
}
else
{
obj* x_241; uint8 x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; 
x_241 = lean::cnstr_get(x_105, 0);
x_243 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (lean::is_exclusive(x_105)) {
 x_244 = x_105;
} else {
 lean::inc(x_241);
 lean::dec(x_105);
 x_244 = lean::box(0);
}
if (lean::is_scalar(x_244)) {
 x_245 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_245 = x_244;
}
lean::cnstr_set(x_245, 0, x_241);
lean::cnstr_set_scalar(x_245, sizeof(void*)*1, x_243);
x_246 = x_245;
x_247 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_88, x_246);
x_14 = x_247;
x_15 = x_101;
goto lbl_16;
}
}
else
{
lean::dec(x_4);
x_14 = x_19;
x_15 = x_20;
goto lbl_16;
}
}
}
}
else
{
obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_256; obj* x_258; obj* x_259; 
x_252 = lean::cnstr_get(x_3, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_3, 0);
lean::inc(x_254);
x_256 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
lean::inc(x_4);
x_258 = l_Lean_Parser_commandParser_run(x_252, x_256, x_254, x_4, x_5);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
if (lean::obj_tag(x_259) == 0)
{
obj* x_261; obj* x_263; obj* x_264; obj* x_266; obj* x_268; obj* x_270; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_261 = lean::cnstr_get(x_258, 1);
if (lean::is_exclusive(x_258)) {
 lean::cnstr_release(x_258, 0);
 x_263 = x_258;
} else {
 lean::inc(x_261);
 lean::dec(x_258);
 x_263 = lean::box(0);
}
x_264 = lean::cnstr_get(x_259, 0);
x_266 = lean::cnstr_get(x_259, 1);
x_268 = lean::cnstr_get(x_259, 2);
if (lean::is_exclusive(x_259)) {
 x_270 = x_259;
} else {
 lean::inc(x_264);
 lean::inc(x_266);
 lean::inc(x_268);
 lean::dec(x_259);
 x_270 = lean::box(0);
}
lean::inc(x_2);
if (lean::is_scalar(x_263)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_263;
}
lean::cnstr_set(x_272, 0, x_264);
lean::cnstr_set(x_272, 1, x_2);
x_273 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_270)) {
 x_274 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_274 = x_270;
}
lean::cnstr_set(x_274, 0, x_272);
lean::cnstr_set(x_274, 1, x_266);
lean::cnstr_set(x_274, 2, x_273);
x_275 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_268, x_274);
if (lean::obj_tag(x_275) == 0)
{
obj* x_276; obj* x_278; obj* x_280; obj* x_282; obj* x_283; obj* x_285; obj* x_287; obj* x_288; uint8 x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; 
x_276 = lean::cnstr_get(x_275, 0);
x_278 = lean::cnstr_get(x_275, 1);
x_280 = lean::cnstr_get(x_275, 2);
if (lean::is_exclusive(x_275)) {
 x_282 = x_275;
} else {
 lean::inc(x_276);
 lean::inc(x_278);
 lean::inc(x_280);
 lean::dec(x_275);
 x_282 = lean::box(0);
}
x_283 = lean::cnstr_get(x_276, 0);
x_285 = lean::cnstr_get(x_276, 1);
if (lean::is_exclusive(x_276)) {
 x_287 = x_276;
} else {
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_276);
 x_287 = lean::box(0);
}
x_288 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_288, 0, x_283);
x_289 = 0;
x_290 = lean::box(x_289);
if (lean::is_scalar(x_287)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_287;
}
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_288);
x_292 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_292, 0, x_291);
lean::cnstr_set(x_292, 1, x_285);
if (lean::is_scalar(x_282)) {
 x_293 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_293 = x_282;
}
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_278);
lean::cnstr_set(x_293, 2, x_273);
x_294 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_280, x_293);
x_295 = l_Lean_Parser_finishCommentBlock___closed__2;
x_296 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_295, x_294);
x_249 = x_296;
x_250 = x_261;
goto lbl_251;
}
else
{
obj* x_297; uint8 x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
x_297 = lean::cnstr_get(x_275, 0);
x_299 = lean::cnstr_get_scalar<uint8>(x_275, sizeof(void*)*1);
if (lean::is_exclusive(x_275)) {
 x_300 = x_275;
} else {
 lean::inc(x_297);
 lean::dec(x_275);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set_scalar(x_301, sizeof(void*)*1, x_299);
x_302 = x_301;
x_303 = l_Lean_Parser_finishCommentBlock___closed__2;
x_304 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_303, x_302);
x_249 = x_304;
x_250 = x_261;
goto lbl_251;
}
}
else
{
obj* x_305; obj* x_308; uint8 x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; 
x_305 = lean::cnstr_get(x_258, 1);
lean::inc(x_305);
lean::dec(x_258);
x_308 = lean::cnstr_get(x_259, 0);
x_310 = lean::cnstr_get_scalar<uint8>(x_259, sizeof(void*)*1);
if (lean::is_exclusive(x_259)) {
 x_311 = x_259;
} else {
 lean::inc(x_308);
 lean::dec(x_259);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_308);
lean::cnstr_set_scalar(x_312, sizeof(void*)*1, x_310);
x_313 = x_312;
x_314 = l_Lean_Parser_finishCommentBlock___closed__2;
x_315 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_314, x_313);
x_249 = x_315;
x_250 = x_305;
goto lbl_251;
}
lbl_251:
{
if (lean::obj_tag(x_249) == 0)
{
lean::dec(x_4);
x_14 = x_249;
x_15 = x_250;
goto lbl_16;
}
else
{
uint8 x_317; 
x_317 = lean::cnstr_get_scalar<uint8>(x_249, sizeof(void*)*1);
if (x_317 == 0)
{
obj* x_318; obj* x_321; obj* x_322; obj* x_324; obj* x_325; obj* x_327; obj* x_329; obj* x_333; obj* x_334; 
x_318 = lean::cnstr_get(x_249, 0);
lean::inc(x_318);
lean::dec(x_249);
x_327 = lean::cnstr_get(x_3, 0);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_327, 0);
lean::inc(x_329);
lean::dec(x_327);
lean::inc(x_4);
x_333 = l_Lean_Parser_token(x_329, x_4, x_250);
x_334 = lean::cnstr_get(x_333, 0);
lean::inc(x_334);
if (lean::obj_tag(x_334) == 0)
{
obj* x_336; obj* x_338; obj* x_339; obj* x_341; obj* x_343; obj* x_345; obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
x_336 = lean::cnstr_get(x_333, 1);
if (lean::is_exclusive(x_333)) {
 lean::cnstr_release(x_333, 0);
 x_338 = x_333;
} else {
 lean::inc(x_336);
 lean::dec(x_333);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_334, 0);
x_341 = lean::cnstr_get(x_334, 1);
x_343 = lean::cnstr_get(x_334, 2);
if (lean::is_exclusive(x_334)) {
 x_345 = x_334;
} else {
 lean::inc(x_339);
 lean::inc(x_341);
 lean::inc(x_343);
 lean::dec(x_334);
 x_345 = lean::box(0);
}
lean::inc(x_2);
if (lean::is_scalar(x_338)) {
 x_347 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_347 = x_338;
}
lean::cnstr_set(x_347, 0, x_339);
lean::cnstr_set(x_347, 1, x_2);
x_348 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_345)) {
 x_349 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_349 = x_345;
}
lean::cnstr_set(x_349, 0, x_347);
lean::cnstr_set(x_349, 1, x_341);
lean::cnstr_set(x_349, 2, x_348);
x_350 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_343, x_349);
if (lean::obj_tag(x_350) == 0)
{
obj* x_351; obj* x_353; obj* x_355; obj* x_357; obj* x_358; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
x_351 = lean::cnstr_get(x_350, 0);
x_353 = lean::cnstr_get(x_350, 1);
x_355 = lean::cnstr_get(x_350, 2);
if (lean::is_exclusive(x_350)) {
 x_357 = x_350;
} else {
 lean::inc(x_351);
 lean::inc(x_353);
 lean::inc(x_355);
 lean::dec(x_350);
 x_357 = lean::box(0);
}
x_358 = lean::cnstr_get(x_351, 1);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 x_360 = x_351;
} else {
 lean::inc(x_358);
 lean::dec(x_351);
 x_360 = lean::box(0);
}
x_361 = lean::box(0);
if (lean::is_scalar(x_360)) {
 x_362 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_362 = x_360;
}
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_358);
if (lean::is_scalar(x_357)) {
 x_363 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_363 = x_357;
}
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_353);
lean::cnstr_set(x_363, 2, x_348);
x_364 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_355, x_363);
x_365 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_364);
x_324 = x_365;
x_325 = x_336;
goto lbl_326;
}
else
{
obj* x_366; obj* x_368; uint8 x_369; obj* x_370; obj* x_371; 
x_366 = lean::cnstr_get(x_350, 0);
if (lean::is_exclusive(x_350)) {
 x_368 = x_350;
} else {
 lean::inc(x_366);
 lean::dec(x_350);
 x_368 = lean::box(0);
}
x_369 = 0;
if (lean::is_scalar(x_368)) {
 x_370 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_370 = x_368;
}
lean::cnstr_set(x_370, 0, x_366);
lean::cnstr_set_scalar(x_370, sizeof(void*)*1, x_369);
x_371 = x_370;
x_324 = x_371;
x_325 = x_336;
goto lbl_326;
}
}
else
{
obj* x_372; obj* x_375; obj* x_377; uint8 x_378; obj* x_379; obj* x_380; 
x_372 = lean::cnstr_get(x_333, 1);
lean::inc(x_372);
lean::dec(x_333);
x_375 = lean::cnstr_get(x_334, 0);
if (lean::is_exclusive(x_334)) {
 x_377 = x_334;
} else {
 lean::inc(x_375);
 lean::dec(x_334);
 x_377 = lean::box(0);
}
x_378 = 0;
if (lean::is_scalar(x_377)) {
 x_379 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_379 = x_377;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set_scalar(x_379, sizeof(void*)*1, x_378);
x_380 = x_379;
x_324 = x_380;
x_325 = x_372;
goto lbl_326;
}
lbl_323:
{
if (lean::obj_tag(x_321) == 0)
{
obj* x_381; obj* x_383; obj* x_385; obj* x_387; obj* x_388; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
x_381 = lean::cnstr_get(x_321, 0);
x_383 = lean::cnstr_get(x_321, 1);
x_385 = lean::cnstr_get(x_321, 2);
if (lean::is_exclusive(x_321)) {
 x_387 = x_321;
} else {
 lean::inc(x_381);
 lean::inc(x_383);
 lean::inc(x_385);
 lean::dec(x_321);
 x_387 = lean::box(0);
}
x_388 = lean::cnstr_get(x_381, 1);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 x_390 = x_381;
} else {
 lean::inc(x_388);
 lean::dec(x_381);
 x_390 = lean::box(0);
}
x_391 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
if (lean::is_scalar(x_390)) {
 x_392 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_392 = x_390;
}
lean::cnstr_set(x_392, 0, x_391);
lean::cnstr_set(x_392, 1, x_388);
x_393 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_387)) {
 x_394 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_394 = x_387;
}
lean::cnstr_set(x_394, 0, x_392);
lean::cnstr_set(x_394, 1, x_383);
lean::cnstr_set(x_394, 2, x_393);
x_395 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_385, x_394);
x_396 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_393, x_395);
x_397 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_318, x_396);
x_14 = x_397;
x_15 = x_322;
goto lbl_16;
}
else
{
obj* x_398; uint8 x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; 
x_398 = lean::cnstr_get(x_321, 0);
x_400 = lean::cnstr_get_scalar<uint8>(x_321, sizeof(void*)*1);
if (lean::is_exclusive(x_321)) {
 x_401 = x_321;
} else {
 lean::inc(x_398);
 lean::dec(x_321);
 x_401 = lean::box(0);
}
if (lean::is_scalar(x_401)) {
 x_402 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_402 = x_401;
}
lean::cnstr_set(x_402, 0, x_398);
lean::cnstr_set_scalar(x_402, sizeof(void*)*1, x_400);
x_403 = x_402;
x_404 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_405 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_404, x_403);
x_406 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_318, x_405);
x_14 = x_406;
x_15 = x_322;
goto lbl_16;
}
}
lbl_326:
{
if (lean::obj_tag(x_324) == 0)
{
lean::dec(x_4);
x_321 = x_324;
x_322 = x_325;
goto lbl_323;
}
else
{
uint8 x_408; 
x_408 = lean::cnstr_get_scalar<uint8>(x_324, sizeof(void*)*1);
if (x_408 == 0)
{
obj* x_409; obj* x_413; obj* x_414; 
x_409 = lean::cnstr_get(x_324, 0);
lean::inc(x_409);
lean::dec(x_324);
lean::inc(x_2);
x_413 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_2, x_3, x_4, x_325);
x_414 = lean::cnstr_get(x_413, 0);
lean::inc(x_414);
if (lean::obj_tag(x_414) == 0)
{
obj* x_416; obj* x_418; obj* x_421; obj* x_423; obj* x_425; obj* x_426; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; 
x_416 = lean::cnstr_get(x_414, 0);
lean::inc(x_416);
x_418 = lean::cnstr_get(x_413, 1);
lean::inc(x_418);
lean::dec(x_413);
x_421 = lean::cnstr_get(x_414, 1);
x_423 = lean::cnstr_get(x_414, 2);
if (lean::is_exclusive(x_414)) {
 lean::cnstr_release(x_414, 0);
 x_425 = x_414;
} else {
 lean::inc(x_421);
 lean::inc(x_423);
 lean::dec(x_414);
 x_425 = lean::box(0);
}
x_426 = lean::cnstr_get(x_416, 1);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 x_428 = x_416;
} else {
 lean::inc(x_426);
 lean::dec(x_416);
 x_428 = lean::box(0);
}
x_429 = lean::box(0);
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_429);
lean::cnstr_set(x_430, 1, x_426);
x_431 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_425)) {
 x_432 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_432 = x_425;
}
lean::cnstr_set(x_432, 0, x_430);
lean::cnstr_set(x_432, 1, x_421);
lean::cnstr_set(x_432, 2, x_431);
x_433 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_423, x_432);
x_434 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_409, x_433);
x_321 = x_434;
x_322 = x_418;
goto lbl_323;
}
else
{
obj* x_435; obj* x_438; uint8 x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; 
x_435 = lean::cnstr_get(x_413, 1);
lean::inc(x_435);
lean::dec(x_413);
x_438 = lean::cnstr_get(x_414, 0);
x_440 = lean::cnstr_get_scalar<uint8>(x_414, sizeof(void*)*1);
if (lean::is_exclusive(x_414)) {
 x_441 = x_414;
} else {
 lean::inc(x_438);
 lean::dec(x_414);
 x_441 = lean::box(0);
}
if (lean::is_scalar(x_441)) {
 x_442 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_442 = x_441;
}
lean::cnstr_set(x_442, 0, x_438);
lean::cnstr_set_scalar(x_442, sizeof(void*)*1, x_440);
x_443 = x_442;
x_444 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_409, x_443);
x_321 = x_444;
x_322 = x_435;
goto lbl_323;
}
}
else
{
lean::dec(x_4);
x_321 = x_324;
x_322 = x_325;
goto lbl_323;
}
}
}
}
else
{
lean::dec(x_4);
x_14 = x_249;
x_15 = x_250;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_448; obj* x_450; 
lean::dec(x_9);
x_448 = l_Lean_Parser_Module_eoi_Parser(x_2, x_3, x_4, x_5);
lean::dec(x_3);
x_450 = lean::cnstr_get(x_448, 0);
lean::inc(x_450);
if (lean::obj_tag(x_450) == 0)
{
obj* x_452; obj* x_454; obj* x_456; obj* x_457; obj* x_459; obj* x_461; obj* x_462; obj* x_464; obj* x_466; uint8 x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; 
x_452 = lean::cnstr_get(x_450, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get(x_448, 1);
if (lean::is_exclusive(x_448)) {
 lean::cnstr_release(x_448, 0);
 x_456 = x_448;
} else {
 lean::inc(x_454);
 lean::dec(x_448);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_450, 1);
x_459 = lean::cnstr_get(x_450, 2);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 x_461 = x_450;
} else {
 lean::inc(x_457);
 lean::inc(x_459);
 lean::dec(x_450);
 x_461 = lean::box(0);
}
x_462 = lean::cnstr_get(x_452, 0);
x_464 = lean::cnstr_get(x_452, 1);
if (lean::is_exclusive(x_452)) {
 x_466 = x_452;
} else {
 lean::inc(x_462);
 lean::inc(x_464);
 lean::dec(x_452);
 x_466 = lean::box(0);
}
x_467 = 0;
x_468 = lean::box(x_467);
if (lean::is_scalar(x_466)) {
 x_469 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_469 = x_466;
}
lean::cnstr_set(x_469, 0, x_468);
lean::cnstr_set(x_469, 1, x_462);
if (lean::is_scalar(x_456)) {
 x_470 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_470 = x_456;
}
lean::cnstr_set(x_470, 0, x_469);
lean::cnstr_set(x_470, 1, x_464);
x_471 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_461)) {
 x_472 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_472 = x_461;
}
lean::cnstr_set(x_472, 0, x_470);
lean::cnstr_set(x_472, 1, x_457);
lean::cnstr_set(x_472, 2, x_471);
x_473 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_459, x_472);
x_474 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_475 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_474, x_473);
x_476 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_476, 0, x_475);
lean::cnstr_set(x_476, 1, x_454);
return x_476;
}
else
{
obj* x_477; obj* x_479; obj* x_480; uint8 x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; obj* x_488; 
x_477 = lean::cnstr_get(x_448, 1);
if (lean::is_exclusive(x_448)) {
 lean::cnstr_release(x_448, 0);
 x_479 = x_448;
} else {
 lean::inc(x_477);
 lean::dec(x_448);
 x_479 = lean::box(0);
}
x_480 = lean::cnstr_get(x_450, 0);
x_482 = lean::cnstr_get_scalar<uint8>(x_450, sizeof(void*)*1);
if (lean::is_exclusive(x_450)) {
 x_483 = x_450;
} else {
 lean::inc(x_480);
 lean::dec(x_450);
 x_483 = lean::box(0);
}
if (lean::is_scalar(x_483)) {
 x_484 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_484 = x_483;
}
lean::cnstr_set(x_484, 0, x_480);
lean::cnstr_set_scalar(x_484, sizeof(void*)*1, x_482);
x_485 = x_484;
x_486 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_487 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_486, x_485);
if (lean::is_scalar(x_479)) {
 x_488 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_488 = x_479;
}
lean::cnstr_set(x_488, 0, x_487);
lean::cnstr_set(x_488, 1, x_477);
return x_488;
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_489; obj* x_491; obj* x_493; 
x_489 = lean::cnstr_get(x_11, 0);
lean::inc(x_489);
x_491 = lean::cnstr_get(x_489, 0);
lean::inc(x_491);
x_493 = lean::cnstr_get(x_491, 1);
lean::inc(x_493);
if (lean::obj_tag(x_493) == 0)
{
obj* x_495; obj* x_497; obj* x_500; obj* x_503; uint8 x_506; obj* x_507; obj* x_509; obj* x_511; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; 
x_495 = lean::cnstr_get(x_11, 1);
lean::inc(x_495);
x_497 = lean::cnstr_get(x_11, 2);
lean::inc(x_497);
lean::dec(x_11);
x_500 = lean::cnstr_get(x_489, 1);
lean::inc(x_500);
lean::dec(x_489);
x_503 = lean::cnstr_get(x_491, 0);
lean::inc(x_503);
lean::dec(x_491);
x_506 = lean::unbox(x_503);
x_507 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_506, x_9, x_500, x_3, x_495, x_12);
lean::dec(x_9);
x_509 = lean::cnstr_get(x_507, 0);
x_511 = lean::cnstr_get(x_507, 1);
if (lean::is_exclusive(x_507)) {
 x_513 = x_507;
} else {
 lean::inc(x_509);
 lean::inc(x_511);
 lean::dec(x_507);
 x_513 = lean::box(0);
}
x_514 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_497, x_509);
x_515 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_516 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_515, x_514);
if (lean::is_scalar(x_513)) {
 x_517 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_517 = x_513;
}
lean::cnstr_set(x_517, 0, x_516);
lean::cnstr_set(x_517, 1, x_511);
return x_517;
}
else
{
obj* x_520; obj* x_522; obj* x_524; obj* x_525; obj* x_527; obj* x_528; obj* x_530; obj* x_531; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; 
lean::dec(x_9);
lean::dec(x_3);
x_520 = lean::cnstr_get(x_11, 1);
x_522 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_524 = x_11;
} else {
 lean::inc(x_520);
 lean::inc(x_522);
 lean::dec(x_11);
 x_524 = lean::box(0);
}
x_525 = lean::cnstr_get(x_489, 1);
if (lean::is_exclusive(x_489)) {
 lean::cnstr_release(x_489, 0);
 x_527 = x_489;
} else {
 lean::inc(x_525);
 lean::dec(x_489);
 x_527 = lean::box(0);
}
x_528 = lean::cnstr_get(x_491, 0);
if (lean::is_exclusive(x_491)) {
 lean::cnstr_release(x_491, 1);
 x_530 = x_491;
} else {
 lean::inc(x_528);
 lean::dec(x_491);
 x_530 = lean::box(0);
}
x_531 = lean::cnstr_get(x_493, 0);
lean::inc(x_531);
lean::dec(x_493);
if (lean::is_scalar(x_530)) {
 x_534 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_534 = x_530;
}
lean::cnstr_set(x_534, 0, x_528);
lean::cnstr_set(x_534, 1, x_531);
if (lean::is_scalar(x_527)) {
 x_535 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_535 = x_527;
}
lean::cnstr_set(x_535, 0, x_534);
lean::cnstr_set(x_535, 1, x_525);
x_536 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_524)) {
 x_537 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_537 = x_524;
}
lean::cnstr_set(x_537, 0, x_535);
lean::cnstr_set(x_537, 1, x_520);
lean::cnstr_set(x_537, 2, x_536);
x_538 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_522, x_537);
x_539 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_540 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_539, x_538);
x_541 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_541, 0, x_540);
lean::cnstr_set(x_541, 1, x_12);
return x_541;
}
}
else
{
obj* x_544; uint8 x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; 
lean::dec(x_9);
lean::dec(x_3);
x_544 = lean::cnstr_get(x_11, 0);
x_546 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_547 = x_11;
} else {
 lean::inc(x_544);
 lean::dec(x_11);
 x_547 = lean::box(0);
}
if (lean::is_scalar(x_547)) {
 x_548 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_548 = x_547;
}
lean::cnstr_set(x_548, 0, x_544);
lean::cnstr_set_scalar(x_548, sizeof(void*)*1, x_546);
x_549 = x_548;
x_550 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_551 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_550, x_549);
x_552 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_552, 0, x_551);
lean::cnstr_set(x_552, 1, x_12);
return x_552;
}
}
lbl_16:
{
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_2);
x_11 = x_14;
x_12 = x_15;
goto lbl_13;
}
else
{
obj* x_554; uint8 x_556; obj* x_558; obj* x_562; obj* x_563; 
x_554 = lean::cnstr_get(x_14, 0);
lean::inc(x_554);
x_556 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::dec(x_14);
x_558 = lean::cnstr_get(x_554, 0);
lean::inc(x_558);
lean::inc(x_3);
lean::inc(x_554);
x_562 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(x_554, x_2, x_3, x_558, x_15);
x_563 = lean::cnstr_get(x_562, 0);
lean::inc(x_563);
if (lean::obj_tag(x_563) == 0)
{
obj* x_565; obj* x_567; obj* x_569; obj* x_570; obj* x_572; obj* x_574; obj* x_575; obj* x_577; obj* x_578; obj* x_581; obj* x_583; uint8 x_584; obj* x_585; obj* x_586; obj* x_587; obj* x_588; obj* x_589; obj* x_590; 
x_565 = lean::cnstr_get(x_563, 0);
lean::inc(x_565);
x_567 = lean::cnstr_get(x_562, 1);
if (lean::is_exclusive(x_562)) {
 lean::cnstr_release(x_562, 0);
 x_569 = x_562;
} else {
 lean::inc(x_567);
 lean::dec(x_562);
 x_569 = lean::box(0);
}
x_570 = lean::cnstr_get(x_563, 1);
x_572 = lean::cnstr_get(x_563, 2);
if (lean::is_exclusive(x_563)) {
 lean::cnstr_release(x_563, 0);
 x_574 = x_563;
} else {
 lean::inc(x_570);
 lean::inc(x_572);
 lean::dec(x_563);
 x_574 = lean::box(0);
}
x_575 = lean::cnstr_get(x_565, 1);
if (lean::is_exclusive(x_565)) {
 lean::cnstr_release(x_565, 0);
 x_577 = x_565;
} else {
 lean::inc(x_575);
 lean::dec(x_565);
 x_577 = lean::box(0);
}
x_578 = lean::cnstr_get(x_554, 3);
lean::inc(x_578);
lean::dec(x_554);
x_581 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_578);
lean::dec(x_578);
x_583 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_583, 0, x_581);
x_584 = 1;
x_585 = lean::box(x_584);
if (lean::is_scalar(x_577)) {
 x_586 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_586 = x_577;
}
lean::cnstr_set(x_586, 0, x_585);
lean::cnstr_set(x_586, 1, x_583);
if (lean::is_scalar(x_569)) {
 x_587 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_587 = x_569;
}
lean::cnstr_set(x_587, 0, x_586);
lean::cnstr_set(x_587, 1, x_575);
x_588 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_574)) {
 x_589 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_589 = x_574;
}
lean::cnstr_set(x_589, 0, x_587);
lean::cnstr_set(x_589, 1, x_570);
lean::cnstr_set(x_589, 2, x_588);
x_590 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_572, x_589);
if (lean::obj_tag(x_590) == 0)
{
x_11 = x_590;
x_12 = x_567;
goto lbl_13;
}
else
{
uint8 x_591; 
x_591 = lean::cnstr_get_scalar<uint8>(x_590, sizeof(void*)*1);
if (x_556 == 0)
{
obj* x_592; obj* x_594; obj* x_595; obj* x_596; 
x_592 = lean::cnstr_get(x_590, 0);
if (lean::is_exclusive(x_590)) {
 x_594 = x_590;
} else {
 lean::inc(x_592);
 lean::dec(x_590);
 x_594 = lean::box(0);
}
if (lean::is_scalar(x_594)) {
 x_595 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_595 = x_594;
}
lean::cnstr_set(x_595, 0, x_592);
lean::cnstr_set_scalar(x_595, sizeof(void*)*1, x_591);
x_596 = x_595;
x_11 = x_596;
x_12 = x_567;
goto lbl_13;
}
else
{
obj* x_597; obj* x_599; obj* x_600; obj* x_601; 
x_597 = lean::cnstr_get(x_590, 0);
if (lean::is_exclusive(x_590)) {
 x_599 = x_590;
} else {
 lean::inc(x_597);
 lean::dec(x_590);
 x_599 = lean::box(0);
}
if (lean::is_scalar(x_599)) {
 x_600 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_600 = x_599;
}
lean::cnstr_set(x_600, 0, x_597);
lean::cnstr_set_scalar(x_600, sizeof(void*)*1, x_556);
x_601 = x_600;
x_11 = x_601;
x_12 = x_567;
goto lbl_13;
}
}
}
else
{
uint8 x_603; 
lean::dec(x_554);
x_603 = lean::cnstr_get_scalar<uint8>(x_563, sizeof(void*)*1);
if (x_556 == 0)
{
obj* x_604; obj* x_607; obj* x_609; obj* x_610; obj* x_611; 
x_604 = lean::cnstr_get(x_562, 1);
lean::inc(x_604);
lean::dec(x_562);
x_607 = lean::cnstr_get(x_563, 0);
if (lean::is_exclusive(x_563)) {
 x_609 = x_563;
} else {
 lean::inc(x_607);
 lean::dec(x_563);
 x_609 = lean::box(0);
}
if (lean::is_scalar(x_609)) {
 x_610 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_610 = x_609;
}
lean::cnstr_set(x_610, 0, x_607);
lean::cnstr_set_scalar(x_610, sizeof(void*)*1, x_603);
x_611 = x_610;
x_11 = x_611;
x_12 = x_604;
goto lbl_13;
}
else
{
obj* x_612; obj* x_615; obj* x_617; obj* x_618; obj* x_619; 
x_612 = lean::cnstr_get(x_562, 1);
lean::inc(x_612);
lean::dec(x_562);
x_615 = lean::cnstr_get(x_563, 0);
if (lean::is_exclusive(x_563)) {
 x_617 = x_563;
} else {
 lean::inc(x_615);
 lean::dec(x_563);
 x_617 = lean::box(0);
}
if (lean::is_scalar(x_617)) {
 x_618 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_618 = x_617;
}
lean::cnstr_set(x_618, 0, x_615);
lean::cnstr_set_scalar(x_618, sizeof(void*)*1, x_556);
x_619 = x_618;
x_11 = x_619;
x_12 = x_612;
goto lbl_13;
}
}
}
}
}
else
{
obj* x_620; obj* x_621; obj* x_622; obj* x_623; 
x_620 = lean::box(0);
x_621 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_622 = l_mjoin___rarg___closed__1;
x_623 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_621, x_622, x_620, x_620, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_623;
}
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_0);
x_7 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_6, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_7;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_0);
x_7 = l___private_init_lean_parser_module_1__commandWrecAux(x_6, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Module_parseCommandWithRecovery(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
x_9 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_0, x_7, x_1, x_2, x_3, x_4);
lean::dec(x_7);
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
x_16 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
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
}
obj* l_Lean_Parser_Module_parseCommandWithRecovery___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l_Lean_Parser_Module_parseCommandWithRecovery(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_2(x_0, x_1, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
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
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_17 = x_4;
} else {
 lean::inc(x_15);
 lean::dec(x_4);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_resumeModuleParser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_MessageLog_empty;
x_5 = lean::apply_4(x_0, x_4, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_17 = x_6;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_8, 0);
x_20 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_22 = x_8;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_8);
 x_22 = lean::box(0);
}
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_23, 0, x_18);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
x_25 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_13);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
x_32 = lean::cnstr_get(x_27, 2);
if (lean::is_exclusive(x_27)) {
 x_34 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_27);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_28, 0);
x_37 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_39 = x_28;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_28);
 x_39 = lean::box(0);
}
lean::inc(x_30);
x_41 = lean::apply_1(x_35, x_30);
if (lean::is_scalar(x_39)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_39;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
x_43 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_34)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_34;
}
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_30);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_44);
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_10);
return x_46;
}
else
{
obj* x_47; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_47 = lean::cnstr_get(x_27, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (lean::is_exclusive(x_27)) {
 x_50 = x_27;
} else {
 lean::inc(x_47);
 lean::dec(x_27);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = x_51;
if (lean::is_scalar(x_12)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_12;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_10);
return x_53;
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_54 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_56 = x_5;
} else {
 lean::inc(x_54);
 lean::dec(x_5);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_6, 0);
x_59 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_60 = x_6;
} else {
 lean::inc(x_57);
 lean::dec(x_6);
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
obj* l_Lean_Parser_resumeModuleParser___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_resumeModuleParser___rarg___lambda__1), 4, 2);
lean::closure_set(x_5, 0, x_3);
lean::closure_set(x_5, 1, x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_String_splitAux___main___closed__1;
x_10 = l_Lean_Parser_run___rarg___closed__1;
x_11 = l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(x_5, x_6, x_9, x_10);
x_12 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_release(x_11, 1);
 x_14 = x_11;
} else {
 lean::inc(x_12);
 lean::dec(x_11);
 x_14 = lean::box(0);
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_2);
x_16 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_18 = x_12;
} else {
 lean::inc(x_16);
 lean::dec(x_12);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_16, 3);
lean::inc(x_19);
x_21 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_19);
lean::dec(x_19);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_Lean_Parser_messageOfParsecMessage___rarg(x_29, x_16);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_21);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_55; uint8 x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_14);
lean::dec(x_0);
x_37 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_39 = x_12;
} else {
 lean::inc(x_37);
 lean::dec(x_12);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
x_45 = lean::cnstr_get(x_40, 0);
x_47 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_49 = x_40;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
x_50 = lean::apply_1(x_2, x_45);
x_51 = lean::cnstr_get(x_50, 0);
x_53 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
lean::dec(x_53);
x_58 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_58, 0, x_47);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
if (lean::is_scalar(x_55)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_55;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_39;
}
lean::cnstr_set(x_61, 0, x_60);
if (lean::is_scalar(x_49)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_49;
}
lean::cnstr_set(x_62, 0, x_51);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
}
obj* l_Lean_Parser_resumeModuleParser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_resumeModuleParser___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_resumeModuleParser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_resumeModuleParser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
x_7 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 2);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_10, 1);
lean::inc(x_22);
lean::dec(x_10);
x_25 = lean::apply_5(x_1, x_20, x_22, x_3, x_15, x_12);
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
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_26);
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
obj* x_35; obj* x_37; obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_1);
lean::dec(x_3);
x_35 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_8, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_41 = x_8;
} else {
 lean::inc(x_38);
 lean::dec(x_8);
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
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_parseHeader___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_Lean_Parser_parseHeader___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_4, 0);
x_6 = l_Lean_Parser_whitespace(x_5, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
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
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_11;
}
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_0);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_27 = x_6;
} else {
 lean::inc(x_25);
 lean::dec(x_6);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_7, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_31 = x_7;
} else {
 lean::inc(x_28);
 lean::dec(x_7);
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
obj* l_Lean_Parser_parseHeader___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_Lean_Parser_Module_header;
x_12 = l_Lean_Parser_Module_header_Parser___closed__1;
x_13 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_11, x_12, x_8, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_16 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_18 = x_13;
} else {
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
x_23 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_25 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_18;
}
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_16);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_34 = x_13;
} else {
 lean::inc(x_32);
 lean::dec(x_13);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_14, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_38 = x_14;
} else {
 lean::inc(x_35);
 lean::dec(x_14);
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
obj* _init_l_Lean_Parser_parseHeader___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__2___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__3___boxed), 5, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg), 6, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_parseHeader(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_9; obj* x_12; usize x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_String_toSubstring___closed__1;
x_14 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_13);
x_15 = x_14;
x_16 = 0;
x_17 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_16);
x_18 = x_17;
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__1), 2, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = l_Lean_Parser_parseHeader___closed__1;
x_22 = l_Lean_Parser_resumeModuleParser___rarg(x_0, x_18, x_20, x_21);
return x_22;
}
}
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_parseHeader___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseHeader___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseHeader___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_parseHeader___lambda__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Lean_Parser_parseCommand___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_10, 0, x_7);
x_11 = lean::unbox(x_4);
lean::cnstr_set_scalar(x_10, sizeof(void*)*1, x_11);
x_12 = x_10;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_parseCommand(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseCommand___lambda__1), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_5 = lean::box(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_parseCommandWithRecovery___boxed), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_resumeModuleParser___rarg(x_0, x_1, x_3, x_6);
return x_7;
}
}
obj* initialize_init_lean_parser_command(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_module(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_command(w);
 l_Lean_Parser_ModuleParserM_Monad = _init_l_Lean_Parser_ModuleParserM_Monad();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_Monad);
 l_Lean_Parser_ModuleParserM_Alternative = _init_l_Lean_Parser_ModuleParserM_Alternative();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_Alternative);
 l_Lean_Parser_ModuleParserM_MonadReader = _init_l_Lean_Parser_ModuleParserM_MonadReader();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_MonadReader);
 l_Lean_Parser_ModuleParserM_MonadState = _init_l_Lean_Parser_ModuleParserM_MonadState();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_MonadState);
 l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec = _init_l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec);
 l_Lean_Parser_ModuleParserM_MonadExcept = _init_l_Lean_Parser_ModuleParserM_MonadExcept();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_MonadExcept);
 l_Lean_Parser_ModuleParserM_BasicParserM___closed__1 = _init_l_Lean_Parser_ModuleParserM_BasicParserM___closed__1();
lean::mark_persistent(l_Lean_Parser_ModuleParserM_BasicParserM___closed__1);
 l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean::mark_persistent(l_Lean_Parser_Module_prelude);
 l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Module_prelude_HasView_x_27 = _init_l_Lean_Parser_Module_prelude_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Module_prelude_HasView_x_27);
 l_Lean_Parser_Module_prelude_HasView = _init_l_Lean_Parser_Module_prelude_HasView();
lean::mark_persistent(l_Lean_Parser_Module_prelude_HasView);
 l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView);
 l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_Module_prelude_Parser___closed__1 = _init_l_Lean_Parser_Module_prelude_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_prelude_Parser___closed__1);
 l_Lean_Parser_Module_importPath = _init_l_Lean_Parser_Module_importPath();
lean::mark_persistent(l_Lean_Parser_Module_importPath);
 l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_Module_importPath_HasView_x_27 = _init_l_Lean_Parser_Module_importPath_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x_27);
 l_Lean_Parser_Module_importPath_HasView = _init_l_Lean_Parser_Module_importPath_HasView();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView);
 l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView);
 l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_Module_importPath_Parser___closed__1 = _init_l_Lean_Parser_Module_importPath_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_importPath_Parser___closed__1);
 l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean::mark_persistent(l_Lean_Parser_Module_import);
 l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_Module_import_HasView_x_27 = _init_l_Lean_Parser_Module_import_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x_27);
 l_Lean_Parser_Module_import_HasView = _init_l_Lean_Parser_Module_import_HasView();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView);
 l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView);
 l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_Module_import_Parser___closed__1 = _init_l_Lean_Parser_Module_import_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import_Parser___closed__1);
 l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean::mark_persistent(l_Lean_Parser_Module_header);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_Module_header_HasView_x_27 = _init_l_Lean_Parser_Module_header_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x_27);
 l_Lean_Parser_Module_header_HasView = _init_l_Lean_Parser_Module_header_HasView();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView);
 l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView);
 l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_Module_header_Parser___closed__1 = _init_l_Lean_Parser_Module_header_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header_Parser___closed__1);
 l_Lean_Parser_Module_eoi = _init_l_Lean_Parser_Module_eoi();
lean::mark_persistent(l_Lean_Parser_Module_eoi);
 l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1 = _init_l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1);
 l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1 = _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1);
 l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2 = _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2);
 l_Lean_Parser_parseHeader___closed__1 = _init_l_Lean_Parser_parseHeader___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHeader___closed__1);
return w;
}
