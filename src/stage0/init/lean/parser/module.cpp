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
obj* l_id___rarg___boxed(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(obj*);
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2(obj*, obj*, obj*);
extern obj* l_Id_Monad;
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27;
obj* l_Lean_Parser_Module_import_HasView;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM___boxed(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_resumeModuleParser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
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
obj* l_Lean_Parser_Module_eoi_Parser___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__2(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_parseHeader___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_eoi_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_Module_import;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_String_OldIterator_toEnd___main(obj*);
extern obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
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
obj* l_Lean_Parser_Module_import_Parser___closed__1;
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParserT_Monad___rarg(obj*);
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_moduleParserConfigCoe___boxed(obj*);
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3;
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
obj* l_coeTrans___rarg(obj*, obj*, obj*);
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_liftParserT(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1___closed__1;
obj* l_coeT___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x_27___lambda__1(obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_parseCommand(obj*, obj*);
obj* l_Lean_Parser_messageOfParsecMessage___rarg(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_Module_prelude;
obj* l_Lean_Parser_Module_header_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_HasView_x_27___lambda__1___closed__1;
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
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj*, uint8, obj*, obj*, obj*);
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
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParserT_Alternative___rarg(x_0);
x_3 = l_StateT_Alternative___rarg(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParserT_MonadReader___rarg(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg___boxed), 4, 3);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, lean::box(0));
lean::closure_set(x_3, 2, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadState() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
x_2 = l_StateT_MonadState___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg___boxed), 4, 1);
lean::closure_set(x_3, 0, x_1);
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, lean::box(0));
lean::closure_set(x_5, 3, x_1);
lean::closure_set(x_5, 4, x_1);
x_6 = l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(x_0);
x_7 = l_Lean_Parser_monadParsecTrans___rarg(x_3, x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_Id_Monad;
x_1 = l_Lean_Parser_ParserT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_ParserT_MonadExcept___rarg(x_0);
x_3 = l_StateT_MonadExcept___rarg(x_1, lean::box(0), x_2);
return x_3;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = l_Lean_Parser_Module_prelude;
x_4 = l_Lean_Parser_Syntax_mkNode(x_3, x_2);
return x_4;
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
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_Module_prelude;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
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
x_5 = lean::mk_nat_obj(0ul);
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
x_1 = lean::mk_nat_obj(0ul);
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
x_5 = lean::mk_nat_obj(0ul);
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
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_3, x_4, x_0, x_1, x_2);
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
x_8 = lean::box(3);
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
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
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
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_18);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_1);
x_39 = lean::box(0);
x_40 = l_String_splitAux___main___closed__1;
x_41 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_68 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_3, x_4, x_0, x_1, x_2);
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
obj* x_13; 
lean::dec(x_8);
x_13 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_16; obj* x_19; obj* x_22; 
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::dec(x_9);
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
lean::dec(x_14);
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_8;
}
lean::cnstr_set(x_22, 0, x_19);
if (lean::obj_tag(x_16) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
x_34 = l_List_map___main___rarg(x_33, x_30);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_16, 0);
lean::inc(x_36);
lean::dec(x_16);
x_1 = x_22;
x_2 = x_36;
goto lbl_3;
}
}
case 3:
{
obj* x_40; 
lean::dec(x_8);
x_40 = lean::cnstr_get(x_9, 1);
lean::inc(x_40);
lean::dec(x_9);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; 
x_43 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_43;
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
x_47 = lean::box(0);
x_1 = x_47;
x_2 = x_44;
goto lbl_3;
}
}
default:
{
obj* x_50; 
lean::dec(x_14);
lean::dec(x_8);
x_50 = lean::cnstr_get(x_9, 1);
lean::inc(x_50);
lean::dec(x_9);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; 
x_53 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__3;
return x_53;
}
else
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_57 = lean::box(0);
x_1 = x_57;
x_2 = x_54;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_58; 
x_58 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; 
x_59 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__1;
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_1);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
else
{
obj* x_61; obj* x_64; obj* x_67; obj* x_68; obj* x_69; 
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Parser_Module_import_HasView_x_27___lambda__1___closed__2;
x_68 = l_List_map___main___rarg(x_67, x_64);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_1);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
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
x_12 = lean::box(3);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_Parser_Module_import;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
x_21 = l_Lean_Parser_Module_import;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
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
x_5 = lean::mk_nat_obj(0ul);
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
x_1 = lean::mk_nat_obj(0ul);
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
x_5 = lean::mk_nat_obj(0ul);
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
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_3, x_4, x_0, x_1, x_2);
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
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
if (x_1 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_8 = lean::box(0);
lean::inc(x_3);
x_13 = lean::apply_3(x_0, x_2, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_9 = x_14;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_22 = x_14;
} else {
 lean::inc(x_19);
 lean::dec(x_14);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_19, 3);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_25 = lean::cnstr_get(x_13, 1);
lean::inc(x_25);
lean::dec(x_13);
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_19, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_19, 2);
lean::inc(x_32);
lean::dec(x_19);
x_35 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_28);
lean::cnstr_set(x_36, 1, x_30);
lean::cnstr_set(x_36, 2, x_32);
lean::cnstr_set(x_36, 3, x_35);
if (x_21 == 0)
{
uint8 x_37; obj* x_38; obj* x_39; 
x_37 = 0;
if (lean::is_scalar(x_22)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_22;
}
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
x_39 = x_38;
x_9 = x_39;
x_10 = x_25;
goto lbl_11;
}
else
{
uint8 x_40; obj* x_41; obj* x_42; 
x_40 = 1;
if (lean::is_scalar(x_22)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_22;
}
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_40);
x_42 = x_41;
x_9 = x_42;
x_10 = x_25;
goto lbl_11;
}
}
else
{
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_43 = lean::cnstr_get(x_13, 1);
lean::inc(x_43);
lean::dec(x_13);
x_46 = lean::cnstr_get(x_19, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_19, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_19, 2);
lean::inc(x_50);
lean::dec(x_19);
x_53 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_55 = x_23;
} else {
 lean::inc(x_53);
 lean::dec(x_23);
 x_55 = lean::box(0);
}
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_Lean_Parser_noKind;
x_59 = l_Lean_Parser_Syntax_mkNode(x_58, x_57);
if (lean::is_scalar(x_55)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_55;
}
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_46);
lean::cnstr_set(x_61, 1, x_48);
lean::cnstr_set(x_61, 2, x_50);
lean::cnstr_set(x_61, 3, x_60);
if (x_21 == 0)
{
uint8 x_62; obj* x_63; obj* x_64; 
x_62 = 0;
if (lean::is_scalar(x_22)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_22;
}
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_62);
x_64 = x_63;
x_9 = x_64;
x_10 = x_43;
goto lbl_11;
}
else
{
uint8 x_65; obj* x_66; obj* x_67; 
x_65 = 1;
if (lean::is_scalar(x_22)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_22;
}
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_65);
x_67 = x_66;
x_9 = x_67;
x_10 = x_43;
goto lbl_11;
}
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_68 = lean::cnstr_get(x_9, 0);
x_70 = lean::cnstr_get(x_9, 1);
x_72 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_74 = x_9;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_9);
 x_74 = lean::box(0);
}
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_68);
x_76 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_77 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_77 = x_74;
}
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_76);
x_78 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_77);
if (lean::obj_tag(x_78) == 0)
{
lean::dec(x_3);
x_5 = x_78;
x_6 = x_10;
goto lbl_7;
}
else
{
uint8 x_80; 
x_80 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (x_80 == 0)
{
obj* x_81; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
x_84 = lean::cnstr_get(x_81, 2);
lean::inc(x_84);
lean::dec(x_81);
x_87 = l_mjoin___rarg___closed__1;
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_88, 0, x_84);
lean::closure_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_90, 0, x_8);
lean::cnstr_set(x_90, 1, x_3);
lean::cnstr_set(x_90, 2, x_89);
x_5 = x_90;
x_6 = x_10;
goto lbl_7;
}
else
{
lean::dec(x_3);
x_5 = x_78;
x_6 = x_10;
goto lbl_7;
}
}
}
else
{
uint8 x_92; 
x_92 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_92 == 0)
{
obj* x_93; obj* x_96; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_93 = lean::cnstr_get(x_9, 0);
lean::inc(x_93);
lean::dec(x_9);
x_96 = lean::cnstr_get(x_93, 2);
lean::inc(x_96);
lean::dec(x_93);
x_99 = l_mjoin___rarg___closed__1;
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_100, 0, x_96);
lean::closure_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
x_102 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_102, 0, x_8);
lean::cnstr_set(x_102, 1, x_3);
lean::cnstr_set(x_102, 2, x_101);
x_5 = x_102;
x_6 = x_10;
goto lbl_7;
}
else
{
obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_106 = x_9;
} else {
 lean::inc(x_104);
 lean::dec(x_9);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_92);
x_108 = x_107;
x_5 = x_108;
x_6 = x_10;
goto lbl_7;
}
}
}
}
else
{
obj* x_109; 
x_109 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_109;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_110; 
x_110 = lean::cnstr_get(x_5, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_112; obj* x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_112 = lean::cnstr_get(x_5, 1);
x_114 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_116 = x_5;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_5);
 x_116 = lean::box(0);
}
x_117 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_118 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_116)) {
 x_119 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_119 = x_116;
}
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_112);
lean::cnstr_set(x_119, 2, x_118);
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_119);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_6);
return x_121;
}
else
{
obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_122 = lean::cnstr_get(x_5, 1);
x_124 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_126 = x_5;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_5);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_110, 0);
lean::inc(x_127);
lean::dec(x_110);
x_130 = lean::box(0);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set(x_131, 1, x_130);
x_132 = l_Lean_Parser_noKind;
x_133 = l_Lean_Parser_Syntax_mkNode(x_132, x_131);
x_134 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_126)) {
 x_135 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_135 = x_126;
}
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_122);
lean::cnstr_set(x_135, 2, x_134);
x_136 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_124, x_135);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_6);
return x_137;
}
}
else
{
obj* x_138; uint8 x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_138 = lean::cnstr_get(x_5, 0);
x_140 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_141 = x_5;
} else {
 lean::inc(x_138);
 lean::dec(x_5);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_138);
lean::cnstr_set_scalar(x_142, sizeof(void*)*1, x_140);
x_143 = x_142;
x_144 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_6);
return x_144;
}
}
}
}
obj* _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed), 5, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_BasicParserM_Monad;
x_10 = l_Lean_Parser_BasicParserM_MonadExcept;
x_11 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_BasicParserM_Alternative;
x_13 = l_Lean_Parser_Module_header;
x_14 = l_Lean_Parser_Module_header_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(x_0, x_5, x_2, x_3, x_4);
return x_6;
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
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed), 5, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
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
obj* l_Lean_Parser_Module_header_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Module_header;
x_4 = l_Lean_Parser_Module_header_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_3, x_4, x_0, x_1, x_2);
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
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_4);
if (x_6 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = lean::string_append(x_11, x_10);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_16 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_13, x_15, x_14, x_14, x_0, x_1, x_2, x_3);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_16, 0);
x_20 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_22 = x_16;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_16);
 x_22 = lean::box(0);
}
x_23 = l_Lean_Parser_finishCommentBlock___closed__2;
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_18);
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_20);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_0);
x_28 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_3);
return x_30;
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
lean::dec(x_4);
lean::dec(x_5);
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
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_6, x_7, x_5, x_5, x_0, x_1, x_2, x_3);
lean::dec(x_0);
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
x_15 = l_Lean_Parser_finishCommentBlock___closed__2;
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
x_19 = l_True_Decidable;
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
x_27 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_24, x_26, x_25, x_25, x_0, x_1, x_2, x_3);
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
x_34 = l_Lean_Parser_finishCommentBlock___closed__2;
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
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = l_String_OldIterator_next___main(x_2);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_18);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_37);
lean::cnstr_set(x_41, 2, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_3);
return x_42;
}
}
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(3);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 1;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2() {
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
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3() {
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
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_17; uint8 x_19; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_1, x_8);
x_10 = l_String_OldIterator_remaining___main(x_4);
x_19 = lean::nat_dec_eq(x_10, x_6);
lean::dec(x_10);
if (x_19 == 0)
{
if (x_0 == 0)
{
uint8 x_21; 
x_21 = 1;
x_17 = x_21;
goto lbl_18;
}
else
{
uint8 x_22; 
x_22 = 0;
x_17 = x_22;
goto lbl_18;
}
}
else
{
obj* x_24; obj* x_26; 
lean::dec(x_9);
x_24 = l_Lean_Parser_Module_eoi_Parser(x_2, x_3, x_4, x_5);
lean::dec(x_3);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_26, 1);
x_35 = lean::cnstr_get(x_26, 2);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_37 = x_26;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_26);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_28, 0);
x_40 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_42 = x_28;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_28);
 x_42 = lean::box(0);
}
x_43 = 0;
x_44 = lean::box(x_43);
if (lean::is_scalar(x_42)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_42;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_38);
if (lean::is_scalar(x_32)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_32;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_40);
x_47 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_37)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_37;
}
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_33);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_48);
x_50 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_30);
return x_52;
}
else
{
obj* x_53; obj* x_55; obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_53 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_55 = x_24;
} else {
 lean::inc(x_53);
 lean::dec(x_24);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_26, 0);
x_58 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_59 = x_26;
} else {
 lean::inc(x_56);
 lean::dec(x_26);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_58);
x_61 = x_60;
x_62 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_61);
if (lean::is_scalar(x_55)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_55;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_53);
return x_64;
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_65; obj* x_67; obj* x_69; 
x_65 = lean::cnstr_get(x_11, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_76; obj* x_79; uint8 x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_71 = lean::cnstr_get(x_11, 1);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_11, 2);
lean::inc(x_73);
lean::dec(x_11);
x_76 = lean::cnstr_get(x_65, 1);
lean::inc(x_76);
lean::dec(x_65);
x_79 = lean::cnstr_get(x_67, 0);
lean::inc(x_79);
lean::dec(x_67);
x_82 = lean::unbox(x_79);
x_83 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_82, x_9, x_76, x_3, x_71, x_12);
lean::dec(x_9);
x_85 = lean::cnstr_get(x_83, 0);
x_87 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_89 = x_83;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_83);
 x_89 = lean::box(0);
}
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_85);
x_91 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_90);
if (lean::is_scalar(x_89)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_89;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_87);
return x_93;
}
else
{
obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_9);
lean::dec(x_3);
x_96 = lean::cnstr_get(x_11, 1);
x_98 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_100 = x_11;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_11);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 x_103 = x_65;
} else {
 lean::inc(x_101);
 lean::dec(x_65);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 1);
 x_106 = x_67;
} else {
 lean::inc(x_104);
 lean::dec(x_67);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_69, 0);
lean::inc(x_107);
lean::dec(x_69);
if (lean::is_scalar(x_106)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_106;
}
lean::cnstr_set(x_110, 0, x_104);
lean::cnstr_set(x_110, 1, x_107);
if (lean::is_scalar(x_103)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_103;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_101);
x_112 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_100)) {
 x_113 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_113 = x_100;
}
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set(x_113, 1, x_96);
lean::cnstr_set(x_113, 2, x_112);
x_114 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_113);
x_115 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_114);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_12);
return x_117;
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_9);
lean::dec(x_3);
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
x_126 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_126, x_125);
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_12);
return x_128;
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
obj* x_130; uint8 x_132; obj* x_134; obj* x_138; obj* x_139; 
x_130 = lean::cnstr_get(x_14, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::dec(x_14);
x_134 = lean::cnstr_get(x_130, 0);
lean::inc(x_134);
lean::inc(x_3);
lean::inc(x_130);
x_138 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(x_130, x_2, x_3, x_134, x_15);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_141; obj* x_143; 
x_141 = lean::cnstr_get(x_139, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_130, 3);
lean::inc(x_143);
lean::dec(x_130);
if (lean::obj_tag(x_143) == 0)
{
obj* x_146; obj* x_149; obj* x_151; obj* x_153; obj* x_154; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_146 = lean::cnstr_get(x_138, 1);
lean::inc(x_146);
lean::dec(x_138);
x_149 = lean::cnstr_get(x_139, 1);
x_151 = lean::cnstr_get(x_139, 2);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 x_153 = x_139;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::dec(x_139);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 x_156 = x_141;
} else {
 lean::inc(x_154);
 lean::dec(x_141);
 x_156 = lean::box(0);
}
x_157 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
if (lean::is_scalar(x_156)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_156;
}
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_154);
x_159 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_153)) {
 x_160 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_160 = x_153;
}
lean::cnstr_set(x_160, 0, x_158);
lean::cnstr_set(x_160, 1, x_149);
lean::cnstr_set(x_160, 2, x_159);
x_161 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_151, x_160);
if (lean::obj_tag(x_161) == 0)
{
x_11 = x_161;
x_12 = x_146;
goto lbl_13;
}
else
{
uint8 x_162; 
x_162 = lean::cnstr_get_scalar<uint8>(x_161, sizeof(void*)*1);
if (x_132 == 0)
{
obj* x_163; obj* x_165; obj* x_166; obj* x_167; 
x_163 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 x_165 = x_161;
} else {
 lean::inc(x_163);
 lean::dec(x_161);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_162);
x_167 = x_166;
x_11 = x_167;
x_12 = x_146;
goto lbl_13;
}
else
{
obj* x_168; obj* x_170; uint8 x_171; obj* x_172; obj* x_173; 
x_168 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 x_170 = x_161;
} else {
 lean::inc(x_168);
 lean::dec(x_161);
 x_170 = lean::box(0);
}
x_171 = 1;
if (lean::is_scalar(x_170)) {
 x_172 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_172 = x_170;
}
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set_scalar(x_172, sizeof(void*)*1, x_171);
x_173 = x_172;
x_11 = x_173;
x_12 = x_146;
goto lbl_13;
}
}
}
else
{
obj* x_174; obj* x_176; obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_188; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_174 = lean::cnstr_get(x_138, 1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 x_176 = x_138;
} else {
 lean::inc(x_174);
 lean::dec(x_138);
 x_176 = lean::box(0);
}
x_177 = lean::cnstr_get(x_139, 1);
x_179 = lean::cnstr_get(x_139, 2);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 x_181 = x_139;
} else {
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_139);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 x_184 = x_141;
} else {
 lean::inc(x_182);
 lean::dec(x_141);
 x_184 = lean::box(0);
}
x_185 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_187 = x_143;
} else {
 lean::inc(x_185);
 lean::dec(x_143);
 x_187 = lean::box(0);
}
if (lean::is_scalar(x_187)) {
 x_188 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_188 = x_187;
}
lean::cnstr_set(x_188, 0, x_185);
x_189 = 1;
x_190 = lean::box(x_189);
if (lean::is_scalar(x_184)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_184;
}
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_188);
if (lean::is_scalar(x_176)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_176;
}
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_182);
x_193 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_181)) {
 x_194 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_194 = x_181;
}
lean::cnstr_set(x_194, 0, x_192);
lean::cnstr_set(x_194, 1, x_177);
lean::cnstr_set(x_194, 2, x_193);
x_195 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_194);
if (lean::obj_tag(x_195) == 0)
{
x_11 = x_195;
x_12 = x_174;
goto lbl_13;
}
else
{
uint8 x_196; 
x_196 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (x_132 == 0)
{
obj* x_197; obj* x_199; obj* x_200; obj* x_201; 
x_197 = lean::cnstr_get(x_195, 0);
if (lean::is_exclusive(x_195)) {
 x_199 = x_195;
} else {
 lean::inc(x_197);
 lean::dec(x_195);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_197);
lean::cnstr_set_scalar(x_200, sizeof(void*)*1, x_196);
x_201 = x_200;
x_11 = x_201;
x_12 = x_174;
goto lbl_13;
}
else
{
obj* x_202; obj* x_204; obj* x_205; obj* x_206; 
x_202 = lean::cnstr_get(x_195, 0);
if (lean::is_exclusive(x_195)) {
 x_204 = x_195;
} else {
 lean::inc(x_202);
 lean::dec(x_195);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_202);
lean::cnstr_set_scalar(x_205, sizeof(void*)*1, x_189);
x_206 = x_205;
x_11 = x_206;
x_12 = x_174;
goto lbl_13;
}
}
}
}
else
{
uint8 x_208; 
lean::dec(x_130);
x_208 = lean::cnstr_get_scalar<uint8>(x_139, sizeof(void*)*1);
if (x_132 == 0)
{
obj* x_209; obj* x_212; obj* x_214; obj* x_215; obj* x_216; 
x_209 = lean::cnstr_get(x_138, 1);
lean::inc(x_209);
lean::dec(x_138);
x_212 = lean::cnstr_get(x_139, 0);
if (lean::is_exclusive(x_139)) {
 x_214 = x_139;
} else {
 lean::inc(x_212);
 lean::dec(x_139);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
lean::cnstr_set_scalar(x_215, sizeof(void*)*1, x_208);
x_216 = x_215;
x_11 = x_216;
x_12 = x_209;
goto lbl_13;
}
else
{
obj* x_217; obj* x_220; obj* x_222; uint8 x_223; obj* x_224; obj* x_225; 
x_217 = lean::cnstr_get(x_138, 1);
lean::inc(x_217);
lean::dec(x_138);
x_220 = lean::cnstr_get(x_139, 0);
if (lean::is_exclusive(x_139)) {
 x_222 = x_139;
} else {
 lean::inc(x_220);
 lean::dec(x_139);
 x_222 = lean::box(0);
}
x_223 = 1;
if (lean::is_scalar(x_222)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_222;
}
lean::cnstr_set(x_224, 0, x_220);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_223);
x_225 = x_224;
x_11 = x_225;
x_12 = x_217;
goto lbl_13;
}
}
}
}
lbl_18:
{
obj* x_226; obj* x_227; obj* x_229; obj* x_231; obj* x_233; obj* x_235; obj* x_236; 
x_229 = lean::cnstr_get(x_3, 1);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_3, 0);
lean::inc(x_231);
x_233 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3;
lean::inc(x_4);
x_235 = l_Lean_Parser_commandParser_run(x_229, x_233, x_231, x_4, x_5);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
if (lean::obj_tag(x_236) == 0)
{
obj* x_238; obj* x_240; obj* x_241; obj* x_243; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
x_238 = lean::cnstr_get(x_235, 1);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 x_240 = x_235;
} else {
 lean::inc(x_238);
 lean::dec(x_235);
 x_240 = lean::box(0);
}
x_241 = lean::cnstr_get(x_236, 0);
x_243 = lean::cnstr_get(x_236, 1);
x_245 = lean::cnstr_get(x_236, 2);
if (lean::is_exclusive(x_236)) {
 x_247 = x_236;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::inc(x_245);
 lean::dec(x_236);
 x_247 = lean::box(0);
}
lean::inc(x_2);
if (lean::is_scalar(x_240)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_240;
}
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_2);
x_250 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_247)) {
 x_251 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_251 = x_247;
}
lean::cnstr_set(x_251, 0, x_249);
lean::cnstr_set(x_251, 1, x_243);
lean::cnstr_set(x_251, 2, x_250);
x_252 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_251);
if (lean::obj_tag(x_252) == 0)
{
obj* x_253; obj* x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_265; uint8 x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
x_253 = lean::cnstr_get(x_252, 0);
x_255 = lean::cnstr_get(x_252, 1);
x_257 = lean::cnstr_get(x_252, 2);
if (lean::is_exclusive(x_252)) {
 x_259 = x_252;
} else {
 lean::inc(x_253);
 lean::inc(x_255);
 lean::inc(x_257);
 lean::dec(x_252);
 x_259 = lean::box(0);
}
x_260 = lean::cnstr_get(x_253, 0);
x_262 = lean::cnstr_get(x_253, 1);
if (lean::is_exclusive(x_253)) {
 x_264 = x_253;
} else {
 lean::inc(x_260);
 lean::inc(x_262);
 lean::dec(x_253);
 x_264 = lean::box(0);
}
x_265 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_265, 0, x_260);
x_266 = 0;
x_267 = lean::box(x_266);
if (lean::is_scalar(x_264)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_264;
}
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_265);
x_269 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_262);
if (lean::is_scalar(x_259)) {
 x_270 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_270 = x_259;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_255);
lean::cnstr_set(x_270, 2, x_250);
x_271 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_257, x_270);
x_272 = l_Lean_Parser_finishCommentBlock___closed__2;
x_273 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_272, x_271);
x_226 = x_273;
x_227 = x_238;
goto lbl_228;
}
else
{
obj* x_274; uint8 x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
x_274 = lean::cnstr_get(x_252, 0);
x_276 = lean::cnstr_get_scalar<uint8>(x_252, sizeof(void*)*1);
if (lean::is_exclusive(x_252)) {
 x_277 = x_252;
} else {
 lean::inc(x_274);
 lean::dec(x_252);
 x_277 = lean::box(0);
}
if (lean::is_scalar(x_277)) {
 x_278 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_278 = x_277;
}
lean::cnstr_set(x_278, 0, x_274);
lean::cnstr_set_scalar(x_278, sizeof(void*)*1, x_276);
x_279 = x_278;
x_280 = l_Lean_Parser_finishCommentBlock___closed__2;
x_281 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_280, x_279);
x_226 = x_281;
x_227 = x_238;
goto lbl_228;
}
}
else
{
obj* x_282; obj* x_285; uint8 x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
x_282 = lean::cnstr_get(x_235, 1);
lean::inc(x_282);
lean::dec(x_235);
x_285 = lean::cnstr_get(x_236, 0);
x_287 = lean::cnstr_get_scalar<uint8>(x_236, sizeof(void*)*1);
if (lean::is_exclusive(x_236)) {
 x_288 = x_236;
} else {
 lean::inc(x_285);
 lean::dec(x_236);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_285);
lean::cnstr_set_scalar(x_289, sizeof(void*)*1, x_287);
x_290 = x_289;
x_291 = l_Lean_Parser_finishCommentBlock___closed__2;
x_292 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_291, x_290);
x_226 = x_292;
x_227 = x_282;
goto lbl_228;
}
lbl_228:
{
if (lean::obj_tag(x_226) == 0)
{
lean::dec(x_4);
x_14 = x_226;
x_15 = x_227;
goto lbl_16;
}
else
{
obj* x_294; uint8 x_296; obj* x_297; obj* x_298; 
x_294 = lean::cnstr_get(x_226, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get_scalar<uint8>(x_226, sizeof(void*)*1);
if (x_296 == 0)
{
lean::dec(x_226);
if (x_17 == 0)
{
obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
x_301 = lean::box(0);
lean::inc(x_2);
x_303 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_303, 0, x_301);
lean::cnstr_set(x_303, 1, x_2);
x_304 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_305 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_305, 0, x_303);
lean::cnstr_set(x_305, 1, x_4);
lean::cnstr_set(x_305, 2, x_304);
x_297 = x_305;
x_298 = x_227;
goto lbl_299;
}
else
{
obj* x_306; obj* x_307; obj* x_308; obj* x_310; obj* x_313; obj* x_314; obj* x_316; obj* x_319; obj* x_320; 
x_306 = l_String_splitAux___main___closed__1;
x_307 = l_Lean_Parser_command_Parser___rarg___closed__1;
x_308 = l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
lean::inc(x_4);
x_310 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_310, 0, x_4);
lean::cnstr_set(x_310, 1, x_306);
lean::cnstr_set(x_310, 2, x_307);
lean::cnstr_set(x_310, 3, x_308);
lean::inc(x_3);
lean::inc(x_2);
x_313 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_310, x_2, x_3, x_4, x_227);
x_314 = lean::cnstr_get(x_313, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_313, 1);
lean::inc(x_316);
lean::dec(x_313);
x_319 = l_Lean_Parser_finishCommentBlock___closed__2;
x_320 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_319, x_314);
x_297 = x_320;
x_298 = x_316;
goto lbl_299;
}
}
else
{
lean::dec(x_294);
lean::dec(x_4);
x_14 = x_226;
x_15 = x_227;
goto lbl_16;
}
lbl_299:
{
if (lean::obj_tag(x_297) == 0)
{
obj* x_323; obj* x_325; obj* x_327; obj* x_330; obj* x_331; obj* x_333; obj* x_336; obj* x_337; obj* x_339; obj* x_341; obj* x_345; obj* x_346; 
x_323 = lean::cnstr_get(x_297, 0);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_297, 1);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_297, 2);
lean::inc(x_327);
lean::dec(x_297);
x_333 = lean::cnstr_get(x_323, 1);
lean::inc(x_333);
lean::dec(x_323);
x_339 = lean::cnstr_get(x_3, 0);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_339, 0);
lean::inc(x_341);
lean::dec(x_339);
lean::inc(x_325);
x_345 = l_Lean_Parser_token(x_341, x_325, x_298);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
if (lean::obj_tag(x_346) == 0)
{
obj* x_348; obj* x_350; obj* x_351; obj* x_353; obj* x_355; obj* x_357; obj* x_359; obj* x_360; obj* x_361; obj* x_362; 
x_348 = lean::cnstr_get(x_345, 1);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 x_350 = x_345;
} else {
 lean::inc(x_348);
 lean::dec(x_345);
 x_350 = lean::box(0);
}
x_351 = lean::cnstr_get(x_346, 0);
x_353 = lean::cnstr_get(x_346, 1);
x_355 = lean::cnstr_get(x_346, 2);
if (lean::is_exclusive(x_346)) {
 x_357 = x_346;
} else {
 lean::inc(x_351);
 lean::inc(x_353);
 lean::inc(x_355);
 lean::dec(x_346);
 x_357 = lean::box(0);
}
lean::inc(x_333);
if (lean::is_scalar(x_350)) {
 x_359 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_359 = x_350;
}
lean::cnstr_set(x_359, 0, x_351);
lean::cnstr_set(x_359, 1, x_333);
x_360 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_357)) {
 x_361 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_361 = x_357;
}
lean::cnstr_set(x_361, 0, x_359);
lean::cnstr_set(x_361, 1, x_353);
lean::cnstr_set(x_361, 2, x_360);
x_362 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_355, x_361);
if (lean::obj_tag(x_362) == 0)
{
obj* x_363; obj* x_365; obj* x_367; obj* x_369; obj* x_370; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
x_363 = lean::cnstr_get(x_362, 0);
x_365 = lean::cnstr_get(x_362, 1);
x_367 = lean::cnstr_get(x_362, 2);
if (lean::is_exclusive(x_362)) {
 x_369 = x_362;
} else {
 lean::inc(x_363);
 lean::inc(x_365);
 lean::inc(x_367);
 lean::dec(x_362);
 x_369 = lean::box(0);
}
x_370 = lean::cnstr_get(x_363, 1);
if (lean::is_exclusive(x_363)) {
 lean::cnstr_release(x_363, 0);
 x_372 = x_363;
} else {
 lean::inc(x_370);
 lean::dec(x_363);
 x_372 = lean::box(0);
}
x_373 = lean::box(0);
if (lean::is_scalar(x_372)) {
 x_374 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_374 = x_372;
}
lean::cnstr_set(x_374, 0, x_373);
lean::cnstr_set(x_374, 1, x_370);
if (lean::is_scalar(x_369)) {
 x_375 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_375 = x_369;
}
lean::cnstr_set(x_375, 0, x_374);
lean::cnstr_set(x_375, 1, x_365);
lean::cnstr_set(x_375, 2, x_360);
x_376 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_367, x_375);
x_377 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_376);
x_336 = x_377;
x_337 = x_348;
goto lbl_338;
}
else
{
obj* x_378; obj* x_380; uint8 x_381; obj* x_382; obj* x_383; 
x_378 = lean::cnstr_get(x_362, 0);
if (lean::is_exclusive(x_362)) {
 x_380 = x_362;
} else {
 lean::inc(x_378);
 lean::dec(x_362);
 x_380 = lean::box(0);
}
x_381 = 0;
if (lean::is_scalar(x_380)) {
 x_382 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_382 = x_380;
}
lean::cnstr_set(x_382, 0, x_378);
lean::cnstr_set_scalar(x_382, sizeof(void*)*1, x_381);
x_383 = x_382;
x_336 = x_383;
x_337 = x_348;
goto lbl_338;
}
}
else
{
obj* x_384; obj* x_387; obj* x_389; uint8 x_390; obj* x_391; obj* x_392; 
x_384 = lean::cnstr_get(x_345, 1);
lean::inc(x_384);
lean::dec(x_345);
x_387 = lean::cnstr_get(x_346, 0);
if (lean::is_exclusive(x_346)) {
 x_389 = x_346;
} else {
 lean::inc(x_387);
 lean::dec(x_346);
 x_389 = lean::box(0);
}
x_390 = 0;
if (lean::is_scalar(x_389)) {
 x_391 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_391 = x_389;
}
lean::cnstr_set(x_391, 0, x_387);
lean::cnstr_set_scalar(x_391, sizeof(void*)*1, x_390);
x_392 = x_391;
x_336 = x_392;
x_337 = x_384;
goto lbl_338;
}
lbl_332:
{
if (lean::obj_tag(x_330) == 0)
{
obj* x_393; obj* x_395; obj* x_397; obj* x_399; obj* x_400; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; 
x_393 = lean::cnstr_get(x_330, 0);
x_395 = lean::cnstr_get(x_330, 1);
x_397 = lean::cnstr_get(x_330, 2);
if (lean::is_exclusive(x_330)) {
 x_399 = x_330;
} else {
 lean::inc(x_393);
 lean::inc(x_395);
 lean::inc(x_397);
 lean::dec(x_330);
 x_399 = lean::box(0);
}
x_400 = lean::cnstr_get(x_393, 1);
if (lean::is_exclusive(x_393)) {
 lean::cnstr_release(x_393, 0);
 x_402 = x_393;
} else {
 lean::inc(x_400);
 lean::dec(x_393);
 x_402 = lean::box(0);
}
x_403 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
if (lean::is_scalar(x_402)) {
 x_404 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_404 = x_402;
}
lean::cnstr_set(x_404, 0, x_403);
lean::cnstr_set(x_404, 1, x_400);
x_405 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_399)) {
 x_406 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_406 = x_399;
}
lean::cnstr_set(x_406, 0, x_404);
lean::cnstr_set(x_406, 1, x_395);
lean::cnstr_set(x_406, 2, x_405);
x_407 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_397, x_406);
x_408 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_327, x_407);
x_409 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_294, x_408);
x_14 = x_409;
x_15 = x_331;
goto lbl_16;
}
else
{
obj* x_410; uint8 x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; 
x_410 = lean::cnstr_get(x_330, 0);
x_412 = lean::cnstr_get_scalar<uint8>(x_330, sizeof(void*)*1);
if (lean::is_exclusive(x_330)) {
 x_413 = x_330;
} else {
 lean::inc(x_410);
 lean::dec(x_330);
 x_413 = lean::box(0);
}
if (lean::is_scalar(x_413)) {
 x_414 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_414 = x_413;
}
lean::cnstr_set(x_414, 0, x_410);
lean::cnstr_set_scalar(x_414, sizeof(void*)*1, x_412);
x_415 = x_414;
x_416 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_327, x_415);
x_417 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_294, x_416);
x_14 = x_417;
x_15 = x_331;
goto lbl_16;
}
}
lbl_338:
{
if (lean::obj_tag(x_336) == 0)
{
lean::dec(x_333);
lean::dec(x_325);
x_330 = x_336;
x_331 = x_337;
goto lbl_332;
}
else
{
uint8 x_420; 
x_420 = lean::cnstr_get_scalar<uint8>(x_336, sizeof(void*)*1);
if (x_420 == 0)
{
obj* x_421; obj* x_424; obj* x_425; 
x_421 = lean::cnstr_get(x_336, 0);
lean::inc(x_421);
lean::dec(x_336);
x_424 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(x_333, x_3, x_325, x_337);
x_425 = lean::cnstr_get(x_424, 0);
lean::inc(x_425);
if (lean::obj_tag(x_425) == 0)
{
obj* x_427; obj* x_429; obj* x_432; obj* x_434; obj* x_436; obj* x_437; obj* x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
x_427 = lean::cnstr_get(x_425, 0);
lean::inc(x_427);
x_429 = lean::cnstr_get(x_424, 1);
lean::inc(x_429);
lean::dec(x_424);
x_432 = lean::cnstr_get(x_425, 1);
x_434 = lean::cnstr_get(x_425, 2);
if (lean::is_exclusive(x_425)) {
 lean::cnstr_release(x_425, 0);
 x_436 = x_425;
} else {
 lean::inc(x_432);
 lean::inc(x_434);
 lean::dec(x_425);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_427, 1);
if (lean::is_exclusive(x_427)) {
 lean::cnstr_release(x_427, 0);
 x_439 = x_427;
} else {
 lean::inc(x_437);
 lean::dec(x_427);
 x_439 = lean::box(0);
}
x_440 = lean::box(0);
if (lean::is_scalar(x_439)) {
 x_441 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_441 = x_439;
}
lean::cnstr_set(x_441, 0, x_440);
lean::cnstr_set(x_441, 1, x_437);
x_442 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_436)) {
 x_443 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_443 = x_436;
}
lean::cnstr_set(x_443, 0, x_441);
lean::cnstr_set(x_443, 1, x_432);
lean::cnstr_set(x_443, 2, x_442);
x_444 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_434, x_443);
x_445 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_421, x_444);
x_330 = x_445;
x_331 = x_429;
goto lbl_332;
}
else
{
obj* x_446; obj* x_449; uint8 x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; 
x_446 = lean::cnstr_get(x_424, 1);
lean::inc(x_446);
lean::dec(x_424);
x_449 = lean::cnstr_get(x_425, 0);
x_451 = lean::cnstr_get_scalar<uint8>(x_425, sizeof(void*)*1);
if (lean::is_exclusive(x_425)) {
 x_452 = x_425;
} else {
 lean::inc(x_449);
 lean::dec(x_425);
 x_452 = lean::box(0);
}
if (lean::is_scalar(x_452)) {
 x_453 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_453 = x_452;
}
lean::cnstr_set(x_453, 0, x_449);
lean::cnstr_set_scalar(x_453, sizeof(void*)*1, x_451);
x_454 = x_453;
x_455 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_421, x_454);
x_330 = x_455;
x_331 = x_446;
goto lbl_332;
}
}
else
{
lean::dec(x_333);
lean::dec(x_325);
x_330 = x_336;
x_331 = x_337;
goto lbl_332;
}
}
}
}
else
{
obj* x_458; uint8 x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
x_458 = lean::cnstr_get(x_297, 0);
x_460 = lean::cnstr_get_scalar<uint8>(x_297, sizeof(void*)*1);
if (lean::is_exclusive(x_297)) {
 x_461 = x_297;
} else {
 lean::inc(x_458);
 lean::dec(x_297);
 x_461 = lean::box(0);
}
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_458);
lean::cnstr_set_scalar(x_462, sizeof(void*)*1, x_460);
x_463 = x_462;
x_464 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_294, x_463);
x_14 = x_464;
x_15 = x_298;
goto lbl_16;
}
}
}
}
}
}
else
{
obj* x_465; obj* x_466; obj* x_467; obj* x_468; 
x_465 = lean::box(0);
x_466 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_467 = l_mjoin___rarg___closed__1;
x_468 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_466, x_467, x_465, x_465, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_468;
}
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(x_0, x_1, x_2, x_3);
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
x_6 = lean::mk_nat_obj(1ul);
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
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_24; obj* x_27; obj* x_30; obj* x_31; 
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
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
lean::dec(x_0);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_Lean_Parser_messageOfParsecMessage___rarg(x_27, x_16);
if (lean::is_scalar(x_18)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_18;
}
lean::cnstr_set(x_31, 0, x_30);
if (lean::obj_tag(x_19) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(3);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_19, 0);
lean::inc(x_34);
lean::dec(x_19);
if (lean::is_scalar(x_14)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_14;
}
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_31);
return x_37;
}
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_58; uint8 x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_14);
lean::dec(x_0);
x_40 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_42 = x_12;
} else {
 lean::inc(x_40);
 lean::dec(x_12);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_43, 0);
x_50 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_52 = x_43;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_43);
 x_52 = lean::box(0);
}
x_53 = lean::apply_1(x_2, x_48);
x_54 = lean::cnstr_get(x_53, 0);
x_56 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_58 = x_53;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_53);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
lean::dec(x_56);
x_61 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_61, 0, x_50);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_59);
x_62 = x_61;
if (lean::is_scalar(x_58)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_58;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
if (lean::is_scalar(x_52)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_52;
}
lean::cnstr_set(x_65, 0, x_54);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
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
x_13 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_11, x_12, x_8, x_3, x_4);
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
obj* x_1; obj* x_3; obj* x_6; obj* x_9; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
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
x_12 = lean::mk_nat_obj(0ul);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_12);
x_14 = 0;
x_15 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
lean::inc(x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_16);
x_19 = l_Lean_Parser_parseHeader___closed__1;
x_20 = l_Lean_Parser_resumeModuleParser___rarg(x_0, x_16, x_18, x_19);
return x_20;
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
 l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3 = _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3);
 l_Lean_Parser_parseHeader___closed__1 = _init_l_Lean_Parser_parseHeader___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHeader___closed__1);
return w;
}
