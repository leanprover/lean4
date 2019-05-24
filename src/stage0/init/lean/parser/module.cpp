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
extern obj* l_Lean_Parser_command_Parser___rarg___closed__1;
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l___private_init_lean_parser_module_1__commandWrecAux(uint8, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_MessageLog_empty;
obj* l_Lean_Parser_ModuleParserM_Alternative;
obj* l_Lean_Parser_ModuleParserM_MonadReader;
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_commandParser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_ModuleParserM_Monad;
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1(obj*, obj*);
obj* l_Lean_Parser_parseHeader___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_ParserT_Alternative___rarg(obj*);
obj* l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1;
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_Module_header;
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l_StateT_Monad___rarg(obj*);
extern obj* l_Lean_Parser_run___rarg___closed__1;
obj* l_Lean_Parser_moduleParserConfigCoe(obj*);
obj* l_Lean_Parser_Module_header_Parser___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Module_prelude_HasView;
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_ParserT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_Module_header_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
obj* l_Lean_Parser_Module_prelude_Parser(obj*, obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__1(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(obj*);
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2(obj*, obj*, obj*);
extern obj* l_Id_Monad;
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x27;
obj* l_Lean_Parser_Module_import_HasView;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM___boxed(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_resumeModuleParser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_Module_parseCommandWithRecovery___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_parseCommandWithRecovery(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_commandParserConfigCoeParserConfig___boxed(obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_import_Parser(obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_eoi_Parser___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_parseHeader___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Module_import_HasView_x27;
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3;
extern obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_StateT_MonadExcept___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHeader___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_Module_prelude_Parser___closed__1;
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6;
obj* l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2;
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
obj* l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_ModuleParserM_MonadExcept;
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
obj* l_Lean_Parser_Module_importPath_HasView;
obj* l_Lean_Parser_resumeModuleParser(obj*);
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5;
obj* l_Lean_Parser_Module_import_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Module_importPath_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_command_Parser___boxed(obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_BasicParserM___closed__1;
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*, obj*);
obj* l_coeTrans___rarg(obj*, obj*, obj*);
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(obj*, obj*);
obj* l_Lean_Parser_ModuleParserM_liftParserT(obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1;
obj* l_coeT___rarg(obj*, obj*);
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1(obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_parseCommand(obj*, obj*);
obj* l_Lean_Parser_messageOfParsecMessage___rarg(obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_Module_prelude;
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Module_header_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_parseCommand___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Module_import_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Module_header_HasView_x27;
obj* l_StateT_Alternative___rarg(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_ParserT_MonadReader___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1;
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_StateT_MonadState___rarg(obj*);
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
obj* l_StateT_lift___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
obj* l_Lean_Parser_Module_prelude_HasView_x27;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj*, uint8, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHeader(obj*);
obj* l_Lean_Parser_moduleParserConfigCoe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_moduleParserConfigCoe___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_moduleParserConfigCoe(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Monad() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
x_3 = l_StateT_Monad___rarg(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Alternative() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
x_3 = l_Lean_Parser_ParserT_Alternative___rarg(x_1);
x_4 = l_StateT_Alternative___rarg(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadReader() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
x_3 = l_Lean_Parser_ParserT_MonadReader___rarg(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg), 4, 3);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadState() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
x_3 = l_StateT_MonadState___rarg(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_Lean_Parser_MonadParsec() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_lift___rarg), 4, 1);
lean::closure_set(x_3, 0, x_2);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_MonadFunctor___boxed), 6, 5);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, lean::box(0));
lean::closure_set(x_4, 3, x_2);
lean::closure_set(x_4, 4, x_2);
x_5 = l_Lean_Parser_ParserT_Lean_Parser_MonadParsec___rarg(x_1);
x_6 = l_Lean_Parser_monadParsecTrans___rarg(x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_MonadExcept() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Id_Monad;
x_2 = l_Lean_Parser_ParserT_Monad___rarg(x_1);
x_3 = l_Lean_Parser_ParserT_MonadExcept___rarg(x_1);
x_4 = l_StateT_MonadExcept___rarg(x_2, lean::box(0), x_3);
return x_4;
}
}
obj* l_Lean_Parser_ModuleParserM_liftParserT___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::apply_1(x_1, x_5);
x_9 = lean::apply_3(x_3, x_8, x_6, x_7);
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
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_10, 0);
x_16 = lean::cnstr_get(x_10, 2);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 0, x_15);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_10, 2, x_17);
lean::cnstr_set(x_10, 0, x_9);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_10);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_10, 0);
x_21 = lean::cnstr_get(x_10, 1);
x_22 = lean::cnstr_get(x_10, 2);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_10);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 0, x_20);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_9);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_27 = lean::cnstr_get(x_9, 1);
lean::inc(x_27);
lean::dec(x_9);
x_28 = lean::cnstr_get(x_10, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_10, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_10, 2);
lean::inc(x_30);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_31 = x_10;
} else {
 lean::dec_ref(x_10);
 x_31 = lean::box(0);
}
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_4);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_29);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_27);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_4);
x_37 = !lean::is_exclusive(x_9);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = lean::cnstr_get(x_9, 0);
lean::dec(x_38);
x_39 = !lean::is_exclusive(x_10);
if (x_39 == 0)
{
return x_9;
}
else
{
obj* x_40; uint8 x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_10, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_40);
lean::dec(x_10);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_41);
lean::cnstr_set(x_9, 0, x_42);
return x_9;
}
}
else
{
obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_9, 1);
lean::inc(x_43);
lean::dec(x_9);
x_44 = lean::cnstr_get(x_10, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_46 = x_10;
} else {
 lean::dec_ref(x_10);
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
obj* l_Lean_Parser_ModuleParserM_liftParserT(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ModuleParserM_liftParserT___rarg), 7, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_ModuleParserM_BasicParserM___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_commandParserConfigCoeParserConfig___boxed), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeB___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_moduleParserConfigCoe___boxed), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coeTrans___rarg), 3, 2);
lean::closure_set(x_4, 0, x_3);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coeT___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ModuleParserM_liftParserT___rarg), 7, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_Lean_Parser_ModuleParserM_BasicParserM(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ModuleParserM_BasicParserM___closed__1;
return x_3;
}
}
obj* l_Lean_Parser_ModuleParserM_BasicParserM___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ModuleParserM_BasicParserM(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_prelude() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Module");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("prelude");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_Module_prelude;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1;
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
x_7 = l_Lean_Parser_Module_prelude;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
}
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__2(obj* x_1) {
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
obj* _init_l_Lean_Parser_Module_prelude_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Module_prelude_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_prelude_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_prelude_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::mk_string("prelude");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_BasicParserM_Monad;
x_9 = l_Lean_Parser_BasicParserM_MonadExcept;
x_10 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_BasicParserM_Alternative;
x_12 = l_Lean_Parser_Module_prelude;
x_13 = l_Lean_Parser_Module_prelude_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_string("prelude");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_4);
lean::dec(x_3);
x_6 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_prelude_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string("prelude");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_Module_prelude_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Module_prelude;
x_5 = l_Lean_Parser_Module_prelude_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_importPath() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Module");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("importPath");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___elambda__1___spec__1(obj* x_1) {
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___elambda__1___spec__1(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_4);
x_7 = lean::box(3);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_12 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___elambda__1___spec__1(x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_10);
x_13 = lean::box(3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
}
}
}
}
obj* l_Lean_Parser_Module_importPath_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___elambda__1___spec__1(x_2);
x_5 = l_Lean_Parser_noKind;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_3);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_Module_importPath;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
obj* l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(obj* x_1) {
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
else
{
obj* x_9; 
lean::dec(x_4);
x_9 = lean::box(0);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_9);
return x_1;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_12 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_10);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::mk_string("NOTAnIdent");
lean::inc(x_4);
x_5 = l_Lean_Parser_Substring_ofString(x_4);
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_4);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_7);
lean::cnstr_set(x_8, 3, x_2);
lean::cnstr_set(x_8, 4, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(x_5);
x_7 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_Module_importPath_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_22; 
x_22 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
lean::dec(x_22);
x_23 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4;
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; 
x_26 = lean::box(3);
x_2 = x_25;
x_3 = x_26;
goto block_21;
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_2 = x_28;
x_3 = x_27;
goto block_21;
}
}
block_21:
{
obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2;
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
if (lean::obj_tag(x_6) == 1)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_6);
x_10 = l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2;
return x_10;
}
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = l_List_map___main___at_Lean_Parser_Module_importPath_HasView_x27___spec__1(x_12);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_2);
x_14 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
if (lean::obj_tag(x_16) == 1)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_16);
x_19 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_importPath_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_importPath_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
x_5 = l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_5, 0);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
lean::dec(x_6);
x_15 = lean::cnstr_get(x_14, 2);
lean::inc(x_15);
lean::dec(x_14);
x_16 = l_mjoin___rarg___closed__1;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_3);
lean::cnstr_set(x_20, 2, x_18);
lean::cnstr_set(x_5, 0, x_20);
return x_5;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_5, 1);
lean::inc(x_21);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_6, 0);
lean::inc(x_22);
lean::dec(x_6);
x_23 = lean::cnstr_get(x_22, 2);
lean::inc(x_23);
lean::dec(x_22);
x_24 = l_mjoin___rarg___closed__1;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_3);
lean::cnstr_set(x_28, 2, x_26);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_21);
return x_29;
}
}
else
{
uint8 x_30; 
lean::dec(x_3);
x_30 = !lean::is_exclusive(x_5);
if (x_30 == 0)
{
obj* x_31; 
x_31 = lean::cnstr_get(x_5, 0);
lean::dec(x_31);
return x_5;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_5, 1);
lean::inc(x_32);
lean::dec(x_5);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_6);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2(obj* x_1, obj* x_2, obj* x_3) {
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
x_38 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_17 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_65 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_49 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_94 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_78 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_104 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_112 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
x_122 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
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
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_6, x_1, x_3, x_4, x_5);
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
x_15 = l_Lean_Parser_mkRawRes(x_2, x_12);
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
x_20 = l_Lean_Parser_mkRawRes(x_2, x_18);
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
x_28 = l_Lean_Parser_mkRawRes(x_2, x_25);
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
lean::dec(x_2);
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
obj* _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_1 = lean::mk_string(".");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2), 3, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_BasicParserM_Monad;
x_14 = l_Lean_Parser_BasicParserM_MonadExcept;
x_15 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_16 = l_Lean_Parser_BasicParserM_Alternative;
x_17 = l_Lean_Parser_Module_importPath;
x_18 = l_Lean_Parser_Module_importPath_HasView;
x_19 = l_Lean_Parser_Combinators_node_view___rarg(x_13, x_14, x_15, x_16, x_17, x_12, x_18);
lean::dec(x_12);
return x_19;
}
}
obj* l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_1);
x_4 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_importPath_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::mk_string(".");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__2), 3, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_Lean_Parser_Module_importPath_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Module_importPath;
x_5 = l_Lean_Parser_Module_importPath_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_import() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Module");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("import");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_importPath_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_Module_import_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1;
x_5 = l_List_map___main___rarg(x_4, x_3);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_Module_import;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_9);
x_17 = l_Lean_Parser_Module_import;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_Module_importPath_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_importPath_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_3);
x_4 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2;
x_9 = l_List_map___main___rarg(x_8, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_Module_import_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_13; 
x_13 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
x_14 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
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
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
x_18 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
lean::dec(x_19);
lean::cnstr_set(x_13, 0, x_21);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_20);
x_22 = lean::box(3);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_23);
x_24 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1;
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
x_28 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2;
x_29 = l_List_map___main___rarg(x_28, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_13);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_20, 0);
lean::inc(x_31);
lean::dec(x_20);
x_2 = x_13;
x_3 = x_31;
goto block_12;
}
}
else
{
obj* x_32; 
lean::dec(x_19);
lean::free_heap_obj(x_13);
x_32 = lean::cnstr_get(x_17, 1);
lean::inc(x_32);
lean::dec(x_17);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; 
lean::dec(x_32);
x_33 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
return x_33;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
lean::dec(x_32);
x_35 = lean::box(0);
x_2 = x_35;
x_3 = x_34;
goto block_12;
}
}
}
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_13, 0);
lean::inc(x_36);
lean::dec(x_13);
x_37 = lean::cnstr_get(x_36, 1);
lean::inc(x_37);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
lean::dec(x_37);
x_38 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
return x_38;
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
lean::dec(x_39);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; obj* x_44; 
lean::dec(x_40);
x_43 = lean::box(3);
x_44 = l_Lean_Parser_Syntax_asNode___main(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_44);
x_45 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1;
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
lean::dec(x_44);
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_49 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2;
x_50 = l_List_map___main___rarg(x_49, x_48);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_42);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_40, 0);
lean::inc(x_52);
lean::dec(x_40);
x_2 = x_42;
x_3 = x_52;
goto block_12;
}
}
else
{
obj* x_53; 
lean::dec(x_39);
x_53 = lean::cnstr_get(x_37, 1);
lean::inc(x_53);
lean::dec(x_37);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
lean::dec(x_53);
x_54 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3;
return x_54;
}
else
{
obj* x_55; obj* x_56; 
x_55 = lean::cnstr_get(x_53, 0);
lean::inc(x_55);
lean::dec(x_53);
x_56 = lean::box(0);
x_2 = x_56;
x_3 = x_55;
goto block_12;
}
}
}
}
}
block_12:
{
obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_4);
x_5 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2;
x_10 = l_List_map___main___rarg(x_9, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
}
obj* _init_l_Lean_Parser_Module_import_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_import_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_import_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::mk_string("import");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_BasicParserM_Monad;
x_12 = l_Lean_Parser_BasicParserM_MonadExcept;
x_13 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_14 = l_Lean_Parser_BasicParserM_Alternative;
x_15 = l_Lean_Parser_Module_import;
x_16 = l_Lean_Parser_Module_import_HasView;
x_17 = l_Lean_Parser_Combinators_node_view___rarg(x_11, x_12, x_13, x_14, x_15, x_10, x_16);
lean::dec(x_10);
return x_17;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_string("import");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = l_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_7);
lean::dec(x_7);
lean::dec(x_3);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_import_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::mk_string("import");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_importPath_Parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_identUnivSpec_Parser_Lean_Parser_HasTokens___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_Module_import_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Module_import;
x_5 = l_Lean_Parser_Module_import_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_header() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Module");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("header");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_import_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_Module_header_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1;
x_5 = l_List_map___main___rarg(x_4, x_3);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_10 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_Module_header;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_15 = l_Lean_Parser_Module_prelude_HasView;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_8);
x_19 = l_Lean_Parser_Syntax_mkNode(x_6, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_9);
x_21 = l_Lean_Parser_Module_header;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_Module_import_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Module_import_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_Module_prelude_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_6);
x_7 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_12 = l_List_map___main___rarg(x_11, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Module_prelude_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_3);
x_4 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_9 = l_List_map___main___rarg(x_8, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
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
x_7 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_8);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_Module_prelude_HasView;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_9);
lean::cnstr_set(x_2, 0, x_12);
x_13 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_14 = l_List_map___main___rarg(x_13, x_6);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_8);
lean::dec(x_6);
lean::free_heap_obj(x_2);
x_16 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
return x_16;
}
}
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; 
lean::dec(x_18);
x_19 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5;
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_20);
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_22 = l_Lean_Parser_Module_prelude_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::apply_1(x_23, x_21);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_27 = l_List_map___main___rarg(x_26, x_18);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; 
lean::dec(x_20);
lean::dec(x_18);
x_29 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
return x_29;
}
}
}
}
}
}
obj* l_Lean_Parser_Module_header_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_13; obj* x_14; obj* x_68; 
x_68 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
lean::dec(x_68);
x_69 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6;
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
x_13 = x_71;
x_14 = x_72;
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
x_13 = x_74;
x_14 = x_73;
goto block_67;
}
}
block_12:
{
obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_4);
x_5 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_10 = l_List_map___main___rarg(x_9, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
block_67:
{
obj* x_15; 
x_15 = l_Lean_Parser_Syntax_asNode___main(x_14);
if (lean::obj_tag(x_15) == 0)
{
lean::dec(x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
lean::dec(x_13);
x_16 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_18 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4;
x_2 = x_18;
x_3 = x_17;
goto block_12;
}
}
else
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_15);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_15, 0);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_21);
lean::free_heap_obj(x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_22; 
lean::dec(x_13);
x_22 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5;
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_24 = lean::box(0);
x_2 = x_24;
x_3 = x_23;
goto block_12;
}
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_21, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_25);
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
lean::dec(x_21);
x_27 = l_Lean_Parser_Module_prelude_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::apply_1(x_28, x_26);
lean::cnstr_set(x_15, 0, x_29);
if (lean::obj_tag(x_13) == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_13);
x_30 = lean::box(3);
x_31 = l_Lean_Parser_Syntax_asNode___main(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_31);
x_32 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_15);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_36 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_37 = l_List_map___main___rarg(x_36, x_35);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_15);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_13, 0);
lean::inc(x_39);
lean::dec(x_13);
x_2 = x_15;
x_3 = x_39;
goto block_12;
}
}
else
{
lean::dec(x_25);
lean::dec(x_21);
lean::free_heap_obj(x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_40; 
lean::dec(x_13);
x_40 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
return x_40;
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_13, 0);
lean::inc(x_41);
lean::dec(x_13);
x_42 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4;
x_2 = x_42;
x_3 = x_41;
goto block_12;
}
}
}
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_15, 0);
lean::inc(x_43);
lean::dec(x_15);
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
lean::dec(x_44);
if (lean::obj_tag(x_13) == 0)
{
obj* x_45; 
lean::dec(x_13);
x_45 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5;
return x_45;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_13, 0);
lean::inc(x_46);
lean::dec(x_13);
x_47 = lean::box(0);
x_2 = x_47;
x_3 = x_46;
goto block_12;
}
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_44, 1);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_48);
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
lean::dec(x_44);
x_50 = l_Lean_Parser_Module_prelude_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::apply_1(x_51, x_49);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
if (lean::obj_tag(x_13) == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_13);
x_54 = lean::box(3);
x_55 = l_Lean_Parser_Syntax_asNode___main(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_55);
x_56 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1;
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_55, 0);
lean::inc(x_58);
lean::dec(x_55);
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
lean::dec(x_58);
x_60 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2;
x_61 = l_List_map___main___rarg(x_60, x_59);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_53);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_13, 0);
lean::inc(x_63);
lean::dec(x_13);
x_2 = x_53;
x_3 = x_63;
goto block_12;
}
}
else
{
lean::dec(x_48);
lean::dec(x_44);
if (lean::obj_tag(x_13) == 0)
{
obj* x_64; 
lean::dec(x_13);
x_64 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3;
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = lean::cnstr_get(x_13, 0);
lean::inc(x_65);
lean::dec(x_13);
x_66 = l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4;
x_2 = x_66;
x_3 = x_65;
goto block_12;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_header_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_header_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_header_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Module_header_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Module_header_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
if (x_2 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_93; obj* x_94; 
x_52 = lean::box(0);
lean::inc(x_4);
x_93 = lean::apply_3(x_1, x_3, x_4, x_5);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; 
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
lean::dec(x_93);
x_53 = x_94;
x_54 = x_95;
goto block_92;
}
else
{
obj* x_96; obj* x_97; 
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_96, 3);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; uint8 x_99; 
lean::dec(x_97);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
x_99 = !lean::is_exclusive(x_94);
if (x_99 == 0)
{
uint8 x_100; obj* x_101; uint8 x_102; 
x_100 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
x_101 = lean::cnstr_get(x_94, 0);
lean::dec(x_101);
x_102 = !lean::is_exclusive(x_96);
if (x_102 == 0)
{
obj* x_103; obj* x_104; 
x_103 = lean::cnstr_get(x_96, 3);
lean::dec(x_103);
x_104 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
lean::cnstr_set(x_96, 3, x_104);
if (x_100 == 0)
{
uint8 x_105; 
x_105 = 0;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_105);
x_53 = x_94;
x_54 = x_98;
goto block_92;
}
else
{
uint8 x_106; 
x_106 = 1;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_106);
x_53 = x_94;
x_54 = x_98;
goto block_92;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_107 = lean::cnstr_get(x_96, 0);
x_108 = lean::cnstr_get(x_96, 1);
x_109 = lean::cnstr_get(x_96, 2);
lean::inc(x_109);
lean::inc(x_108);
lean::inc(x_107);
lean::dec(x_96);
x_110 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
x_111 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set(x_111, 1, x_108);
lean::cnstr_set(x_111, 2, x_109);
lean::cnstr_set(x_111, 3, x_110);
if (x_100 == 0)
{
uint8 x_112; 
x_112 = 0;
lean::cnstr_set(x_94, 0, x_111);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_112);
x_53 = x_94;
x_54 = x_98;
goto block_92;
}
else
{
uint8 x_113; 
x_113 = 1;
lean::cnstr_set(x_94, 0, x_111);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_113);
x_53 = x_94;
x_54 = x_98;
goto block_92;
}
}
}
else
{
uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_114 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
lean::dec(x_94);
x_115 = lean::cnstr_get(x_96, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_96, 1);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_96, 2);
lean::inc(x_117);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 lean::cnstr_release(x_96, 2);
 lean::cnstr_release(x_96, 3);
 x_118 = x_96;
} else {
 lean::dec_ref(x_96);
 x_118 = lean::box(0);
}
x_119 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_118)) {
 x_120 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_120 = x_118;
}
lean::cnstr_set(x_120, 0, x_115);
lean::cnstr_set(x_120, 1, x_116);
lean::cnstr_set(x_120, 2, x_117);
lean::cnstr_set(x_120, 3, x_119);
if (x_114 == 0)
{
uint8 x_121; obj* x_122; 
x_121 = 0;
x_122 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_121);
x_53 = x_122;
x_54 = x_98;
goto block_92;
}
else
{
uint8 x_123; obj* x_124; 
x_123 = 1;
x_124 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_123);
x_53 = x_124;
x_54 = x_98;
goto block_92;
}
}
}
else
{
obj* x_125; uint8 x_126; 
x_125 = lean::cnstr_get(x_93, 1);
lean::inc(x_125);
lean::dec(x_93);
x_126 = !lean::is_exclusive(x_94);
if (x_126 == 0)
{
uint8 x_127; obj* x_128; uint8 x_129; 
x_127 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
x_128 = lean::cnstr_get(x_94, 0);
lean::dec(x_128);
x_129 = !lean::is_exclusive(x_96);
if (x_129 == 0)
{
obj* x_130; uint8 x_131; 
x_130 = lean::cnstr_get(x_96, 3);
lean::dec(x_130);
x_131 = !lean::is_exclusive(x_97);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_132 = lean::cnstr_get(x_97, 0);
x_133 = lean::box(0);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_132);
lean::cnstr_set(x_134, 1, x_133);
x_135 = l_Lean_Parser_noKind;
x_136 = l_Lean_Parser_Syntax_mkNode(x_135, x_134);
lean::cnstr_set(x_97, 0, x_136);
if (x_127 == 0)
{
uint8 x_137; 
x_137 = 0;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_137);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
else
{
uint8 x_138; 
x_138 = 1;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_138);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_139 = lean::cnstr_get(x_97, 0);
lean::inc(x_139);
lean::dec(x_97);
x_140 = lean::box(0);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_139);
lean::cnstr_set(x_141, 1, x_140);
x_142 = l_Lean_Parser_noKind;
x_143 = l_Lean_Parser_Syntax_mkNode(x_142, x_141);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_96, 3, x_144);
if (x_127 == 0)
{
uint8 x_145; 
x_145 = 0;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_145);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
else
{
uint8 x_146; 
x_146 = 1;
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_146);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
}
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_147 = lean::cnstr_get(x_96, 0);
x_148 = lean::cnstr_get(x_96, 1);
x_149 = lean::cnstr_get(x_96, 2);
lean::inc(x_149);
lean::inc(x_148);
lean::inc(x_147);
lean::dec(x_96);
x_150 = lean::cnstr_get(x_97, 0);
lean::inc(x_150);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 x_151 = x_97;
} else {
 lean::dec_ref(x_97);
 x_151 = lean::box(0);
}
x_152 = lean::box(0);
x_153 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set(x_153, 1, x_152);
x_154 = l_Lean_Parser_noKind;
x_155 = l_Lean_Parser_Syntax_mkNode(x_154, x_153);
if (lean::is_scalar(x_151)) {
 x_156 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_156 = x_151;
}
lean::cnstr_set(x_156, 0, x_155);
x_157 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_157, 0, x_147);
lean::cnstr_set(x_157, 1, x_148);
lean::cnstr_set(x_157, 2, x_149);
lean::cnstr_set(x_157, 3, x_156);
if (x_127 == 0)
{
uint8 x_158; 
x_158 = 0;
lean::cnstr_set(x_94, 0, x_157);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_158);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
else
{
uint8 x_159; 
x_159 = 1;
lean::cnstr_set(x_94, 0, x_157);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_159);
x_53 = x_94;
x_54 = x_125;
goto block_92;
}
}
}
else
{
uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_160 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
lean::dec(x_94);
x_161 = lean::cnstr_get(x_96, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_96, 1);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_96, 2);
lean::inc(x_163);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 lean::cnstr_release(x_96, 2);
 lean::cnstr_release(x_96, 3);
 x_164 = x_96;
} else {
 lean::dec_ref(x_96);
 x_164 = lean::box(0);
}
x_165 = lean::cnstr_get(x_97, 0);
lean::inc(x_165);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 x_166 = x_97;
} else {
 lean::dec_ref(x_97);
 x_166 = lean::box(0);
}
x_167 = lean::box(0);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_165);
lean::cnstr_set(x_168, 1, x_167);
x_169 = l_Lean_Parser_noKind;
x_170 = l_Lean_Parser_Syntax_mkNode(x_169, x_168);
if (lean::is_scalar(x_166)) {
 x_171 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_171 = x_166;
}
lean::cnstr_set(x_171, 0, x_170);
if (lean::is_scalar(x_164)) {
 x_172 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_172 = x_164;
}
lean::cnstr_set(x_172, 0, x_161);
lean::cnstr_set(x_172, 1, x_162);
lean::cnstr_set(x_172, 2, x_163);
lean::cnstr_set(x_172, 3, x_171);
if (x_160 == 0)
{
uint8 x_173; obj* x_174; 
x_173 = 0;
x_174 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_174, 0, x_172);
lean::cnstr_set_scalar(x_174, sizeof(void*)*1, x_173);
x_53 = x_174;
x_54 = x_125;
goto block_92;
}
else
{
uint8 x_175; obj* x_176; 
x_175 = 1;
x_176 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_176, 0, x_172);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_175);
x_53 = x_176;
x_54 = x_125;
goto block_92;
}
}
}
}
block_92:
{
if (lean::obj_tag(x_53) == 0)
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_53);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::cnstr_get(x_53, 0);
x_57 = lean::cnstr_get(x_53, 2);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_56);
x_59 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_53, 2, x_59);
lean::cnstr_set(x_53, 0, x_58);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_53);
if (lean::obj_tag(x_60) == 0)
{
lean::dec(x_4);
x_6 = x_60;
x_7 = x_54;
goto block_51;
}
else
{
uint8 x_61; 
x_61 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
lean::dec(x_60);
x_63 = lean::cnstr_get(x_62, 2);
lean::inc(x_63);
lean::dec(x_62);
x_64 = l_mjoin___rarg___closed__1;
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_52);
lean::cnstr_set(x_67, 1, x_4);
lean::cnstr_set(x_67, 2, x_66);
x_6 = x_67;
x_7 = x_54;
goto block_51;
}
else
{
lean::dec(x_4);
x_6 = x_60;
x_7 = x_54;
goto block_51;
}
}
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_68 = lean::cnstr_get(x_53, 0);
x_69 = lean::cnstr_get(x_53, 1);
x_70 = lean::cnstr_get(x_53, 2);
lean::inc(x_70);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_53);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_68);
x_72 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_69);
lean::cnstr_set(x_73, 2, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_73);
if (lean::obj_tag(x_74) == 0)
{
lean::dec(x_4);
x_6 = x_74;
x_7 = x_54;
goto block_51;
}
else
{
uint8 x_75; 
x_75 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_76 = lean::cnstr_get(x_74, 0);
lean::inc(x_76);
lean::dec(x_74);
x_77 = lean::cnstr_get(x_76, 2);
lean::inc(x_77);
lean::dec(x_76);
x_78 = l_mjoin___rarg___closed__1;
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_79, 0, x_77);
lean::closure_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_52);
lean::cnstr_set(x_81, 1, x_4);
lean::cnstr_set(x_81, 2, x_80);
x_6 = x_81;
x_7 = x_54;
goto block_51;
}
else
{
lean::dec(x_4);
x_6 = x_74;
x_7 = x_54;
goto block_51;
}
}
}
}
else
{
uint8 x_82; 
x_82 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_53, 0);
lean::inc(x_83);
lean::dec(x_53);
x_84 = lean::cnstr_get(x_83, 2);
lean::inc(x_84);
lean::dec(x_83);
x_85 = l_mjoin___rarg___closed__1;
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_86, 0, x_84);
lean::closure_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_52);
lean::cnstr_set(x_88, 1, x_4);
lean::cnstr_set(x_88, 2, x_87);
x_6 = x_88;
x_7 = x_54;
goto block_51;
}
else
{
uint8 x_89; 
lean::dec(x_4);
x_89 = !lean::is_exclusive(x_53);
if (x_89 == 0)
{
x_6 = x_53;
x_7 = x_54;
goto block_51;
}
else
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_53, 0);
lean::inc(x_90);
lean::dec(x_53);
x_91 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_82);
x_6 = x_91;
x_7 = x_54;
goto block_51;
}
}
}
}
}
else
{
obj* x_177; 
x_177 = lean::apply_3(x_1, x_3, x_4, x_5);
return x_177;
}
block_51:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 2);
x_11 = lean::cnstr_get(x_6, 0);
lean::dec(x_11);
x_12 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_13);
lean::cnstr_set(x_6, 0, x_12);
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_6);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
x_18 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
return x_22;
}
}
else
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_6);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_6, 2);
x_25 = lean::cnstr_get(x_6, 0);
lean::dec(x_25);
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
lean::dec(x_8);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_noKind;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_31);
lean::cnstr_set(x_6, 0, x_30);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_6);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_7);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_34 = lean::cnstr_get(x_6, 1);
x_35 = lean::cnstr_get(x_6, 2);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::cnstr_get(x_8, 0);
lean::inc(x_36);
lean::dec(x_8);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_noKind;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_7);
return x_44;
}
}
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_6);
if (x_45 == 0)
{
obj* x_46; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_6);
lean::cnstr_set(x_46, 1, x_7);
return x_46;
}
else
{
obj* x_47; uint8 x_48; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_6, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_47);
lean::dec(x_6);
x_49 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_7);
return x_50;
}
}
}
}
}
obj* _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_2 = 0;
x_3 = lean::box(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed), 5, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_BasicParserM_Monad;
x_11 = l_Lean_Parser_BasicParserM_MonadExcept;
x_12 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_13 = l_Lean_Parser_BasicParserM_Alternative;
x_14 = l_Lean_Parser_Module_header;
x_15 = l_Lean_Parser_Module_header_HasView;
x_16 = l_Lean_Parser_Combinators_node_view___rarg(x_10, x_11, x_12, x_13, x_14, x_9, x_15);
lean::dec(x_9);
return x_16;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_Module_header_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Module_prelude_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_Module_import_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_tokens___rarg(x_3);
x_5 = lean::box(0);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_5);
lean::dec(x_4);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_8 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_Module_header_Parser___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_prelude_Parser), 3, 0);
x_2 = 0;
x_3 = lean::box(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_Module_header_Parser_Lean_Parser_HasView___spec__1___boxed), 5, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_import_Parser), 3, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_Module_importPath_Parser_Lean_Parser_HasView___spec__1), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Module_header_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Module_header;
x_5 = l_Lean_Parser_Module_header_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_Module_eoi() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("Module");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("eoi");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_1, 2);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_1);
lean::closure_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_5, x_6);
lean::dec(x_5);
if (x_7 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_8 = l_String_OldIterator_curr___main(x_3);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_12 = lean::string_append(x_11, x_10);
x_13 = lean::box(0);
x_14 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_15 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_12, x_14, x_13, x_13, x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = l_Lean_Parser_finishCommentBlock___closed__2;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_17);
lean::cnstr_set(x_15, 0, x_19);
return x_15;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_15, 0);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_15);
x_22 = l_Lean_Parser_finishCommentBlock___closed__2;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_21);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_3);
lean::cnstr_set(x_28, 2, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
return x_29;
}
}
}
obj* l_Lean_Parser_Module_eoi_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
x_10 = !lean::is_exclusive(x_6);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_11 = lean::cnstr_get(x_6, 1);
x_12 = lean::cnstr_get(x_6, 2);
x_13 = lean::cnstr_get(x_6, 0);
lean::dec(x_13);
x_14 = !lean::is_exclusive(x_7);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_15 = lean::cnstr_get(x_7, 0);
lean::dec(x_15);
lean::inc(x_11);
x_16 = l_String_OldIterator_toEnd___main(x_11);
lean::inc(x_16, 2);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
lean::dec(x_16);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_19, 2, x_17);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = l_String_splitAux___main___closed__1;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_Module_eoi;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
lean::cnstr_set(x_7, 0, x_27);
x_28 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
lean::cnstr_set(x_6, 2, x_28);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_6);
lean::cnstr_set(x_5, 0, x_29);
return x_5;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_30 = lean::cnstr_get(x_7, 1);
lean::inc(x_30);
lean::dec(x_7);
lean::inc(x_11);
x_31 = l_String_OldIterator_toEnd___main(x_11);
lean::inc(x_31, 2);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
lean::dec(x_31);
lean::inc(x_32);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set(x_34, 2, x_32);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = l_String_splitAux___main___closed__1;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_Parser_Module_eoi;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_30);
x_44 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
lean::cnstr_set(x_6, 2, x_44);
lean::cnstr_set(x_6, 0, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_6);
lean::cnstr_set(x_5, 0, x_45);
return x_5;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_46 = lean::cnstr_get(x_6, 1);
x_47 = lean::cnstr_get(x_6, 2);
lean::inc(x_47);
lean::inc(x_46);
lean::dec(x_6);
x_48 = lean::cnstr_get(x_7, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_49 = x_7;
} else {
 lean::dec_ref(x_7);
 x_49 = lean::box(0);
}
lean::inc(x_46);
x_50 = l_String_OldIterator_toEnd___main(x_46);
lean::inc(x_50, 2);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::cnstr_get(x_50, 1);
lean::inc(x_52);
lean::dec(x_50);
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = l_String_splitAux___main___closed__1;
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_Lean_Parser_Module_eoi;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
if (lean::is_scalar(x_49)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_49;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_48);
x_63 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_46);
lean::cnstr_set(x_64, 2, x_63);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_64);
lean::cnstr_set(x_5, 0, x_65);
return x_5;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_66 = lean::cnstr_get(x_5, 1);
lean::inc(x_66);
lean::dec(x_5);
x_67 = lean::cnstr_get(x_6, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_6, 2);
lean::inc(x_68);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_69 = x_6;
} else {
 lean::dec_ref(x_6);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_7, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_71 = x_7;
} else {
 lean::dec_ref(x_7);
 x_71 = lean::box(0);
}
lean::inc(x_67);
x_72 = l_String_OldIterator_toEnd___main(x_67);
lean::inc(x_72, 2);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
lean::dec(x_72);
lean::inc(x_73);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set(x_75, 2, x_73);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = l_String_splitAux___main___closed__1;
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_80);
x_82 = l_Lean_Parser_Module_eoi;
x_83 = l_Lean_Parser_Syntax_mkNode(x_82, x_81);
if (lean::is_scalar(x_71)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_71;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_70);
x_85 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_69)) {
 x_86 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_86 = x_69;
}
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_67);
lean::cnstr_set(x_86, 2, x_85);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_66);
return x_88;
}
}
else
{
uint8 x_89; 
x_89 = !lean::is_exclusive(x_5);
if (x_89 == 0)
{
obj* x_90; uint8 x_91; 
x_90 = lean::cnstr_get(x_5, 0);
lean::dec(x_90);
x_91 = !lean::is_exclusive(x_6);
if (x_91 == 0)
{
return x_5;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; 
x_92 = lean::cnstr_get(x_6, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_92);
lean::dec(x_6);
x_94 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_93);
lean::cnstr_set(x_5, 0, x_94);
return x_5;
}
}
else
{
obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; 
x_95 = lean::cnstr_get(x_5, 1);
lean::inc(x_95);
lean::dec(x_5);
x_96 = lean::cnstr_get(x_6, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_98 = x_6;
} else {
 lean::dec_ref(x_6);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_95);
return x_100;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Module_eoi_Parser___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Module_eoi_Parser(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_6, 0);
x_8 = lean::cnstr_get(x_7, 0);
x_9 = l_Lean_Parser_messageOfParsecMessage___rarg(x_8, x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_5);
return x_15;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_Lean_Parser_finishCommentBlock___closed__2;
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
x_16 = l_Lean_Parser_finishCommentBlock___closed__2;
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
x_20 = l_True_Decidable;
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
x_27 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_24, x_26, x_25, x_25, x_1, x_2, x_3, x_4);
lean::dec(x_1);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = l_Lean_Parser_finishCommentBlock___closed__2;
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
x_34 = l_Lean_Parser_finishCommentBlock___closed__2;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_33);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = l_String_OldIterator_next___main(x_3);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_19);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_1);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_37);
lean::cnstr_set(x_41, 2, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
return x_42;
}
}
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_6, 0);
x_8 = lean::cnstr_get(x_7, 0);
x_9 = l_Lean_Parser_messageOfParsecMessage___rarg(x_8, x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_5);
return x_15;
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 1;
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_Parser___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___main(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_92; obj* x_93; uint8 x_254; uint8 x_589; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
x_11 = l_String_OldIterator_remaining___main(x_5);
x_589 = lean::nat_dec_eq(x_11, x_7);
lean::dec(x_11);
if (x_589 == 0)
{
if (x_1 == 0)
{
uint8 x_590; 
x_590 = 1;
x_254 = x_590;
goto block_588;
}
else
{
uint8 x_591; 
x_591 = 0;
x_254 = x_591;
goto block_588;
}
}
else
{
obj* x_592; obj* x_593; 
lean::dec(x_10);
x_592 = l_Lean_Parser_Module_eoi_Parser(x_3, x_4, x_5, x_6);
lean::dec(x_4);
x_593 = lean::cnstr_get(x_592, 0);
lean::inc(x_593);
if (lean::obj_tag(x_593) == 0)
{
obj* x_594; uint8 x_595; 
x_594 = lean::cnstr_get(x_593, 0);
lean::inc(x_594);
x_595 = !lean::is_exclusive(x_592);
if (x_595 == 0)
{
obj* x_596; obj* x_597; uint8 x_598; 
x_596 = lean::cnstr_get(x_592, 1);
x_597 = lean::cnstr_get(x_592, 0);
lean::dec(x_597);
x_598 = !lean::is_exclusive(x_593);
if (x_598 == 0)
{
obj* x_599; obj* x_600; uint8 x_601; 
x_599 = lean::cnstr_get(x_593, 2);
x_600 = lean::cnstr_get(x_593, 0);
lean::dec(x_600);
x_601 = !lean::is_exclusive(x_594);
if (x_601 == 0)
{
obj* x_602; obj* x_603; uint8 x_604; obj* x_605; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; 
x_602 = lean::cnstr_get(x_594, 0);
x_603 = lean::cnstr_get(x_594, 1);
x_604 = 0;
x_605 = lean::box(x_604);
lean::cnstr_set(x_594, 1, x_602);
lean::cnstr_set(x_594, 0, x_605);
lean::cnstr_set(x_592, 1, x_603);
lean::cnstr_set(x_592, 0, x_594);
x_606 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_593, 2, x_606);
lean::cnstr_set(x_593, 0, x_592);
x_607 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_599, x_593);
x_608 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_609 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_608, x_607);
x_610 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_610, 0, x_609);
lean::cnstr_set(x_610, 1, x_596);
return x_610;
}
else
{
obj* x_611; obj* x_612; uint8 x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; obj* x_620; 
x_611 = lean::cnstr_get(x_594, 0);
x_612 = lean::cnstr_get(x_594, 1);
lean::inc(x_612);
lean::inc(x_611);
lean::dec(x_594);
x_613 = 0;
x_614 = lean::box(x_613);
x_615 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_615, 0, x_614);
lean::cnstr_set(x_615, 1, x_611);
lean::cnstr_set(x_592, 1, x_612);
lean::cnstr_set(x_592, 0, x_615);
x_616 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_593, 2, x_616);
lean::cnstr_set(x_593, 0, x_592);
x_617 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_599, x_593);
x_618 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_619 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_618, x_617);
x_620 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_620, 0, x_619);
lean::cnstr_set(x_620, 1, x_596);
return x_620;
}
}
else
{
obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; uint8 x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; 
x_621 = lean::cnstr_get(x_593, 1);
x_622 = lean::cnstr_get(x_593, 2);
lean::inc(x_622);
lean::inc(x_621);
lean::dec(x_593);
x_623 = lean::cnstr_get(x_594, 0);
lean::inc(x_623);
x_624 = lean::cnstr_get(x_594, 1);
lean::inc(x_624);
if (lean::is_exclusive(x_594)) {
 lean::cnstr_release(x_594, 0);
 lean::cnstr_release(x_594, 1);
 x_625 = x_594;
} else {
 lean::dec_ref(x_594);
 x_625 = lean::box(0);
}
x_626 = 0;
x_627 = lean::box(x_626);
if (lean::is_scalar(x_625)) {
 x_628 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_628 = x_625;
}
lean::cnstr_set(x_628, 0, x_627);
lean::cnstr_set(x_628, 1, x_623);
lean::cnstr_set(x_592, 1, x_624);
lean::cnstr_set(x_592, 0, x_628);
x_629 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_630 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_630, 0, x_592);
lean::cnstr_set(x_630, 1, x_621);
lean::cnstr_set(x_630, 2, x_629);
x_631 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_622, x_630);
x_632 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_633 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_632, x_631);
x_634 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_634, 0, x_633);
lean::cnstr_set(x_634, 1, x_596);
return x_634;
}
}
else
{
obj* x_635; obj* x_636; obj* x_637; obj* x_638; obj* x_639; obj* x_640; obj* x_641; uint8 x_642; obj* x_643; obj* x_644; obj* x_645; obj* x_646; obj* x_647; obj* x_648; obj* x_649; obj* x_650; obj* x_651; 
x_635 = lean::cnstr_get(x_592, 1);
lean::inc(x_635);
lean::dec(x_592);
x_636 = lean::cnstr_get(x_593, 1);
lean::inc(x_636);
x_637 = lean::cnstr_get(x_593, 2);
lean::inc(x_637);
if (lean::is_exclusive(x_593)) {
 lean::cnstr_release(x_593, 0);
 lean::cnstr_release(x_593, 1);
 lean::cnstr_release(x_593, 2);
 x_638 = x_593;
} else {
 lean::dec_ref(x_593);
 x_638 = lean::box(0);
}
x_639 = lean::cnstr_get(x_594, 0);
lean::inc(x_639);
x_640 = lean::cnstr_get(x_594, 1);
lean::inc(x_640);
if (lean::is_exclusive(x_594)) {
 lean::cnstr_release(x_594, 0);
 lean::cnstr_release(x_594, 1);
 x_641 = x_594;
} else {
 lean::dec_ref(x_594);
 x_641 = lean::box(0);
}
x_642 = 0;
x_643 = lean::box(x_642);
if (lean::is_scalar(x_641)) {
 x_644 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_644 = x_641;
}
lean::cnstr_set(x_644, 0, x_643);
lean::cnstr_set(x_644, 1, x_639);
x_645 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_645, 0, x_644);
lean::cnstr_set(x_645, 1, x_640);
x_646 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_638)) {
 x_647 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_647 = x_638;
}
lean::cnstr_set(x_647, 0, x_645);
lean::cnstr_set(x_647, 1, x_636);
lean::cnstr_set(x_647, 2, x_646);
x_648 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_637, x_647);
x_649 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_650 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_649, x_648);
x_651 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_651, 0, x_650);
lean::cnstr_set(x_651, 1, x_635);
return x_651;
}
}
else
{
uint8 x_652; 
x_652 = !lean::is_exclusive(x_592);
if (x_652 == 0)
{
obj* x_653; uint8 x_654; 
x_653 = lean::cnstr_get(x_592, 0);
lean::dec(x_653);
x_654 = !lean::is_exclusive(x_593);
if (x_654 == 0)
{
obj* x_655; obj* x_656; 
x_655 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_656 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_655, x_593);
lean::cnstr_set(x_592, 0, x_656);
return x_592;
}
else
{
obj* x_657; uint8 x_658; obj* x_659; obj* x_660; obj* x_661; 
x_657 = lean::cnstr_get(x_593, 0);
x_658 = lean::cnstr_get_scalar<uint8>(x_593, sizeof(void*)*1);
lean::inc(x_657);
lean::dec(x_593);
x_659 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_659, 0, x_657);
lean::cnstr_set_scalar(x_659, sizeof(void*)*1, x_658);
x_660 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_661 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_660, x_659);
lean::cnstr_set(x_592, 0, x_661);
return x_592;
}
}
else
{
obj* x_662; obj* x_663; uint8 x_664; obj* x_665; obj* x_666; obj* x_667; obj* x_668; obj* x_669; 
x_662 = lean::cnstr_get(x_592, 1);
lean::inc(x_662);
lean::dec(x_592);
x_663 = lean::cnstr_get(x_593, 0);
lean::inc(x_663);
x_664 = lean::cnstr_get_scalar<uint8>(x_593, sizeof(void*)*1);
if (lean::is_exclusive(x_593)) {
 lean::cnstr_release(x_593, 0);
 x_665 = x_593;
} else {
 lean::dec_ref(x_593);
 x_665 = lean::box(0);
}
if (lean::is_scalar(x_665)) {
 x_666 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_666 = x_665;
}
lean::cnstr_set(x_666, 0, x_663);
lean::cnstr_set_scalar(x_666, sizeof(void*)*1, x_664);
x_667 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_668 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_667, x_666);
x_669 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_669, 0, x_668);
lean::cnstr_set(x_669, 1, x_662);
return x_669;
}
}
}
block_91:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; uint8 x_23; 
lean::dec(x_16);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_12, 2);
lean::inc(x_18);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
lean::dec(x_15);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
x_22 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_21, x_10, x_19, x_4, x_17, x_13);
lean::dec(x_10);
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_24);
x_26 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_25);
lean::cnstr_set(x_22, 0, x_27);
return x_22;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_28 = lean::cnstr_get(x_22, 0);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_22);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_28);
x_31 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8 x_34; 
lean::dec(x_10);
lean::dec(x_4);
x_34 = !lean::is_exclusive(x_12);
if (x_34 == 0)
{
obj* x_35; obj* x_36; uint8 x_37; 
x_35 = lean::cnstr_get(x_12, 2);
x_36 = lean::cnstr_get(x_12, 0);
lean::dec(x_36);
x_37 = !lean::is_exclusive(x_14);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = lean::cnstr_get(x_14, 0);
lean::dec(x_38);
x_39 = !lean::is_exclusive(x_15);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_40 = lean::cnstr_get(x_15, 1);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
lean::dec(x_16);
lean::cnstr_set(x_15, 1, x_41);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_12, 2, x_42);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_12);
x_44 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_13);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get(x_15, 0);
lean::inc(x_47);
lean::dec(x_15);
x_48 = lean::cnstr_get(x_16, 0);
lean::inc(x_48);
lean::dec(x_16);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set(x_14, 0, x_49);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_12, 2, x_50);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_12);
x_52 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_13);
return x_54;
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_55 = lean::cnstr_get(x_14, 1);
lean::inc(x_55);
lean::dec(x_14);
x_56 = lean::cnstr_get(x_15, 0);
lean::inc(x_56);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_57 = x_15;
} else {
 lean::dec_ref(x_15);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_16, 0);
lean::inc(x_58);
lean::dec(x_16);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
x_61 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_12, 2, x_61);
lean::cnstr_set(x_12, 0, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_12);
x_63 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_62);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_13);
return x_65;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_66 = lean::cnstr_get(x_12, 1);
x_67 = lean::cnstr_get(x_12, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_12);
x_68 = lean::cnstr_get(x_14, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_69 = x_14;
} else {
 lean::dec_ref(x_14);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_15, 0);
lean::inc(x_70);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_71 = x_15;
} else {
 lean::dec_ref(x_15);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_16, 0);
lean::inc(x_72);
lean::dec(x_16);
if (lean::is_scalar(x_71)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_71;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_72);
if (lean::is_scalar(x_69)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_69;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_68);
x_75 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_66);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_76);
x_78 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_77);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_13);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_10);
lean::dec(x_4);
x_81 = !lean::is_exclusive(x_12);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_12);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_13);
return x_84;
}
else
{
obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_85 = lean::cnstr_get(x_12, 0);
x_86 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
lean::inc(x_85);
lean::dec(x_12);
x_87 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_86);
x_88 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_87);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_13);
return x_90;
}
}
}
block_253:
{
if (lean::obj_tag(x_92) == 0)
{
lean::dec(x_3);
x_12 = x_92;
x_13 = x_93;
goto block_91;
}
else
{
obj* x_94; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_92, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get_scalar<uint8>(x_92, sizeof(void*)*1);
lean::dec(x_92);
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
lean::inc(x_94);
x_97 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(x_94, x_3, x_4, x_96, x_93);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; 
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_94, 3);
lean::inc(x_100);
lean::dec(x_94);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; uint8 x_102; 
lean::dec(x_100);
x_101 = lean::cnstr_get(x_97, 1);
lean::inc(x_101);
lean::dec(x_97);
x_102 = !lean::is_exclusive(x_98);
if (x_102 == 0)
{
obj* x_103; obj* x_104; uint8 x_105; 
x_103 = lean::cnstr_get(x_98, 2);
x_104 = lean::cnstr_get(x_98, 0);
lean::dec(x_104);
x_105 = !lean::is_exclusive(x_99);
if (x_105 == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_106 = lean::cnstr_get(x_99, 0);
lean::dec(x_106);
x_107 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
lean::cnstr_set(x_99, 0, x_107);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_98, 2, x_108);
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_98);
if (lean::obj_tag(x_109) == 0)
{
x_12 = x_109;
x_13 = x_101;
goto block_91;
}
else
{
if (x_95 == 0)
{
uint8 x_110; 
x_110 = !lean::is_exclusive(x_109);
if (x_110 == 0)
{
x_12 = x_109;
x_13 = x_101;
goto block_91;
}
else
{
obj* x_111; uint8 x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_109, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
lean::inc(x_111);
lean::dec(x_109);
x_113 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_112);
x_12 = x_113;
x_13 = x_101;
goto block_91;
}
}
else
{
uint8 x_114; 
x_114 = !lean::is_exclusive(x_109);
if (x_114 == 0)
{
uint8 x_115; 
x_115 = 1;
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_115);
x_12 = x_109;
x_13 = x_101;
goto block_91;
}
else
{
obj* x_116; uint8 x_117; obj* x_118; 
x_116 = lean::cnstr_get(x_109, 0);
lean::inc(x_116);
lean::dec(x_109);
x_117 = 1;
x_118 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_117);
x_12 = x_118;
x_13 = x_101;
goto block_91;
}
}
}
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_119 = lean::cnstr_get(x_99, 1);
lean::inc(x_119);
lean::dec(x_99);
x_120 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_119);
x_122 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_98, 2, x_122);
lean::cnstr_set(x_98, 0, x_121);
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_98);
if (lean::obj_tag(x_123) == 0)
{
x_12 = x_123;
x_13 = x_101;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_124; uint8 x_125; obj* x_126; obj* x_127; 
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*1);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_126 = x_123;
} else {
 lean::dec_ref(x_123);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*1, x_125);
x_12 = x_127;
x_13 = x_101;
goto block_91;
}
else
{
obj* x_128; obj* x_129; uint8 x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_123, 0);
lean::inc(x_128);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_129 = x_123;
} else {
 lean::dec_ref(x_123);
 x_129 = lean::box(0);
}
x_130 = 1;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_128);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_130);
x_12 = x_131;
x_13 = x_101;
goto block_91;
}
}
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_132 = lean::cnstr_get(x_98, 1);
x_133 = lean::cnstr_get(x_98, 2);
lean::inc(x_133);
lean::inc(x_132);
lean::dec(x_98);
x_134 = lean::cnstr_get(x_99, 1);
lean::inc(x_134);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_135 = x_99;
} else {
 lean::dec_ref(x_99);
 x_135 = lean::box(0);
}
x_136 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__1;
if (lean::is_scalar(x_135)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_135;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_134);
x_138 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_139 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_139, 0, x_137);
lean::cnstr_set(x_139, 1, x_132);
lean::cnstr_set(x_139, 2, x_138);
x_140 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_133, x_139);
if (lean::obj_tag(x_140) == 0)
{
x_12 = x_140;
x_13 = x_101;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_141; uint8 x_142; obj* x_143; obj* x_144; 
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_142 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 x_143 = x_140;
} else {
 lean::dec_ref(x_140);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_142);
x_12 = x_144;
x_13 = x_101;
goto block_91;
}
else
{
obj* x_145; obj* x_146; uint8 x_147; obj* x_148; 
x_145 = lean::cnstr_get(x_140, 0);
lean::inc(x_145);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 x_146 = x_140;
} else {
 lean::dec_ref(x_140);
 x_146 = lean::box(0);
}
x_147 = 1;
if (lean::is_scalar(x_146)) {
 x_148 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_148 = x_146;
}
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set_scalar(x_148, sizeof(void*)*1, x_147);
x_12 = x_148;
x_13 = x_101;
goto block_91;
}
}
}
}
else
{
uint8 x_149; 
x_149 = !lean::is_exclusive(x_97);
if (x_149 == 0)
{
obj* x_150; obj* x_151; uint8 x_152; 
x_150 = lean::cnstr_get(x_97, 1);
x_151 = lean::cnstr_get(x_97, 0);
lean::dec(x_151);
x_152 = !lean::is_exclusive(x_98);
if (x_152 == 0)
{
obj* x_153; obj* x_154; uint8 x_155; 
x_153 = lean::cnstr_get(x_98, 2);
x_154 = lean::cnstr_get(x_98, 0);
lean::dec(x_154);
x_155 = !lean::is_exclusive(x_99);
if (x_155 == 0)
{
obj* x_156; obj* x_157; uint8 x_158; 
x_156 = lean::cnstr_get(x_99, 1);
x_157 = lean::cnstr_get(x_99, 0);
lean::dec(x_157);
x_158 = !lean::is_exclusive(x_100);
if (x_158 == 0)
{
uint8 x_159; obj* x_160; obj* x_161; obj* x_162; 
x_159 = 1;
x_160 = lean::box(x_159);
lean::cnstr_set(x_99, 1, x_100);
lean::cnstr_set(x_99, 0, x_160);
lean::cnstr_set(x_97, 1, x_156);
lean::cnstr_set(x_97, 0, x_99);
x_161 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_98, 2, x_161);
lean::cnstr_set(x_98, 0, x_97);
x_162 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_153, x_98);
if (lean::obj_tag(x_162) == 0)
{
x_12 = x_162;
x_13 = x_150;
goto block_91;
}
else
{
if (x_95 == 0)
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_162);
if (x_163 == 0)
{
x_12 = x_162;
x_13 = x_150;
goto block_91;
}
else
{
obj* x_164; uint8 x_165; obj* x_166; 
x_164 = lean::cnstr_get(x_162, 0);
x_165 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
lean::inc(x_164);
lean::dec(x_162);
x_166 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_166, 0, x_164);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_165);
x_12 = x_166;
x_13 = x_150;
goto block_91;
}
}
else
{
uint8 x_167; 
x_167 = !lean::is_exclusive(x_162);
if (x_167 == 0)
{
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_159);
x_12 = x_162;
x_13 = x_150;
goto block_91;
}
else
{
obj* x_168; obj* x_169; 
x_168 = lean::cnstr_get(x_162, 0);
lean::inc(x_168);
lean::dec(x_162);
x_169 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_159);
x_12 = x_169;
x_13 = x_150;
goto block_91;
}
}
}
}
else
{
obj* x_170; obj* x_171; uint8 x_172; obj* x_173; obj* x_174; obj* x_175; 
x_170 = lean::cnstr_get(x_100, 0);
lean::inc(x_170);
lean::dec(x_100);
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
x_172 = 1;
x_173 = lean::box(x_172);
lean::cnstr_set(x_99, 1, x_171);
lean::cnstr_set(x_99, 0, x_173);
lean::cnstr_set(x_97, 1, x_156);
lean::cnstr_set(x_97, 0, x_99);
x_174 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_98, 2, x_174);
lean::cnstr_set(x_98, 0, x_97);
x_175 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_153, x_98);
if (lean::obj_tag(x_175) == 0)
{
x_12 = x_175;
x_13 = x_150;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_176; uint8 x_177; obj* x_178; obj* x_179; 
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get_scalar<uint8>(x_175, sizeof(void*)*1);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 x_178 = x_175;
} else {
 lean::dec_ref(x_175);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set_scalar(x_179, sizeof(void*)*1, x_177);
x_12 = x_179;
x_13 = x_150;
goto block_91;
}
else
{
obj* x_180; obj* x_181; obj* x_182; 
x_180 = lean::cnstr_get(x_175, 0);
lean::inc(x_180);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 x_181 = x_175;
} else {
 lean::dec_ref(x_175);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_180);
lean::cnstr_set_scalar(x_182, sizeof(void*)*1, x_172);
x_12 = x_182;
x_13 = x_150;
goto block_91;
}
}
}
}
else
{
obj* x_183; obj* x_184; obj* x_185; obj* x_186; uint8 x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_183 = lean::cnstr_get(x_99, 1);
lean::inc(x_183);
lean::dec(x_99);
x_184 = lean::cnstr_get(x_100, 0);
lean::inc(x_184);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_185 = x_100;
} else {
 lean::dec_ref(x_100);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_184);
x_187 = 1;
x_188 = lean::box(x_187);
x_189 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_189, 0, x_188);
lean::cnstr_set(x_189, 1, x_186);
lean::cnstr_set(x_97, 1, x_183);
lean::cnstr_set(x_97, 0, x_189);
x_190 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_98, 2, x_190);
lean::cnstr_set(x_98, 0, x_97);
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_153, x_98);
if (lean::obj_tag(x_191) == 0)
{
x_12 = x_191;
x_13 = x_150;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_192; uint8 x_193; obj* x_194; obj* x_195; 
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
x_193 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*1);
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_194 = x_191;
} else {
 lean::dec_ref(x_191);
 x_194 = lean::box(0);
}
if (lean::is_scalar(x_194)) {
 x_195 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_195 = x_194;
}
lean::cnstr_set(x_195, 0, x_192);
lean::cnstr_set_scalar(x_195, sizeof(void*)*1, x_193);
x_12 = x_195;
x_13 = x_150;
goto block_91;
}
else
{
obj* x_196; obj* x_197; obj* x_198; 
x_196 = lean::cnstr_get(x_191, 0);
lean::inc(x_196);
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_197 = x_191;
} else {
 lean::dec_ref(x_191);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_196);
lean::cnstr_set_scalar(x_198, sizeof(void*)*1, x_187);
x_12 = x_198;
x_13 = x_150;
goto block_91;
}
}
}
}
else
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_199 = lean::cnstr_get(x_98, 1);
x_200 = lean::cnstr_get(x_98, 2);
lean::inc(x_200);
lean::inc(x_199);
lean::dec(x_98);
x_201 = lean::cnstr_get(x_99, 1);
lean::inc(x_201);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_202 = x_99;
} else {
 lean::dec_ref(x_99);
 x_202 = lean::box(0);
}
x_203 = lean::cnstr_get(x_100, 0);
lean::inc(x_203);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_204 = x_100;
} else {
 lean::dec_ref(x_100);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_203);
x_206 = 1;
x_207 = lean::box(x_206);
if (lean::is_scalar(x_202)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_202;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_205);
lean::cnstr_set(x_97, 1, x_201);
lean::cnstr_set(x_97, 0, x_208);
x_209 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_210 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_210, 0, x_97);
lean::cnstr_set(x_210, 1, x_199);
lean::cnstr_set(x_210, 2, x_209);
x_211 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_210);
if (lean::obj_tag(x_211) == 0)
{
x_12 = x_211;
x_13 = x_150;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_212; uint8 x_213; obj* x_214; obj* x_215; 
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_213 = lean::cnstr_get_scalar<uint8>(x_211, sizeof(void*)*1);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_214 = x_211;
} else {
 lean::dec_ref(x_211);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
lean::cnstr_set_scalar(x_215, sizeof(void*)*1, x_213);
x_12 = x_215;
x_13 = x_150;
goto block_91;
}
else
{
obj* x_216; obj* x_217; obj* x_218; 
x_216 = lean::cnstr_get(x_211, 0);
lean::inc(x_216);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_217 = x_211;
} else {
 lean::dec_ref(x_211);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_216);
lean::cnstr_set_scalar(x_218, sizeof(void*)*1, x_206);
x_12 = x_218;
x_13 = x_150;
goto block_91;
}
}
}
}
else
{
obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; uint8 x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
x_219 = lean::cnstr_get(x_97, 1);
lean::inc(x_219);
lean::dec(x_97);
x_220 = lean::cnstr_get(x_98, 1);
lean::inc(x_220);
x_221 = lean::cnstr_get(x_98, 2);
lean::inc(x_221);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 lean::cnstr_release(x_98, 2);
 x_222 = x_98;
} else {
 lean::dec_ref(x_98);
 x_222 = lean::box(0);
}
x_223 = lean::cnstr_get(x_99, 1);
lean::inc(x_223);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_224 = x_99;
} else {
 lean::dec_ref(x_99);
 x_224 = lean::box(0);
}
x_225 = lean::cnstr_get(x_100, 0);
lean::inc(x_225);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_226 = x_100;
} else {
 lean::dec_ref(x_100);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_225);
x_228 = 1;
x_229 = lean::box(x_228);
if (lean::is_scalar(x_224)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_224;
}
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_227);
x_231 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_231, 0, x_230);
lean::cnstr_set(x_231, 1, x_223);
x_232 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_222)) {
 x_233 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_233 = x_222;
}
lean::cnstr_set(x_233, 0, x_231);
lean::cnstr_set(x_233, 1, x_220);
lean::cnstr_set(x_233, 2, x_232);
x_234 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_221, x_233);
if (lean::obj_tag(x_234) == 0)
{
x_12 = x_234;
x_13 = x_219;
goto block_91;
}
else
{
if (x_95 == 0)
{
obj* x_235; uint8 x_236; obj* x_237; obj* x_238; 
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_236 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 x_237 = x_234;
} else {
 lean::dec_ref(x_234);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_235);
lean::cnstr_set_scalar(x_238, sizeof(void*)*1, x_236);
x_12 = x_238;
x_13 = x_219;
goto block_91;
}
else
{
obj* x_239; obj* x_240; obj* x_241; 
x_239 = lean::cnstr_get(x_234, 0);
lean::inc(x_239);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 x_240 = x_234;
} else {
 lean::dec_ref(x_234);
 x_240 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_239);
lean::cnstr_set_scalar(x_241, sizeof(void*)*1, x_228);
x_12 = x_241;
x_13 = x_219;
goto block_91;
}
}
}
}
}
else
{
lean::dec(x_94);
if (x_95 == 0)
{
obj* x_242; uint8 x_243; 
x_242 = lean::cnstr_get(x_97, 1);
lean::inc(x_242);
lean::dec(x_97);
x_243 = !lean::is_exclusive(x_98);
if (x_243 == 0)
{
x_12 = x_98;
x_13 = x_242;
goto block_91;
}
else
{
obj* x_244; uint8 x_245; obj* x_246; 
x_244 = lean::cnstr_get(x_98, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_98, sizeof(void*)*1);
lean::inc(x_244);
lean::dec(x_98);
x_246 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_246, 0, x_244);
lean::cnstr_set_scalar(x_246, sizeof(void*)*1, x_245);
x_12 = x_246;
x_13 = x_242;
goto block_91;
}
}
else
{
obj* x_247; uint8 x_248; 
x_247 = lean::cnstr_get(x_97, 1);
lean::inc(x_247);
lean::dec(x_97);
x_248 = !lean::is_exclusive(x_98);
if (x_248 == 0)
{
uint8 x_249; 
x_249 = 1;
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_249);
x_12 = x_98;
x_13 = x_247;
goto block_91;
}
else
{
obj* x_250; uint8 x_251; obj* x_252; 
x_250 = lean::cnstr_get(x_98, 0);
lean::inc(x_250);
lean::dec(x_98);
x_251 = 1;
x_252 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_252, 0, x_250);
lean::cnstr_set_scalar(x_252, sizeof(void*)*1, x_251);
x_12 = x_252;
x_13 = x_247;
goto block_91;
}
}
}
}
}
block_588:
{
obj* x_255; obj* x_256; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
x_460 = lean::cnstr_get(x_4, 1);
lean::inc(x_460);
x_461 = lean::cnstr_get(x_4, 0);
lean::inc(x_461);
x_462 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__3;
lean::inc(x_5);
x_463 = l_Lean_Parser_commandParser_run(x_460, x_462, x_461, x_5, x_6);
x_464 = lean::cnstr_get(x_463, 0);
lean::inc(x_464);
if (lean::obj_tag(x_464) == 0)
{
uint8 x_465; 
x_465 = !lean::is_exclusive(x_463);
if (x_465 == 0)
{
obj* x_466; obj* x_467; uint8 x_468; 
x_466 = lean::cnstr_get(x_463, 1);
x_467 = lean::cnstr_get(x_463, 0);
lean::dec(x_467);
x_468 = !lean::is_exclusive(x_464);
if (x_468 == 0)
{
obj* x_469; obj* x_470; obj* x_471; obj* x_472; 
x_469 = lean::cnstr_get(x_464, 0);
x_470 = lean::cnstr_get(x_464, 2);
lean::inc(x_3);
lean::cnstr_set(x_463, 1, x_3);
lean::cnstr_set(x_463, 0, x_469);
x_471 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_464, 2, x_471);
lean::cnstr_set(x_464, 0, x_463);
x_472 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_470, x_464);
if (lean::obj_tag(x_472) == 0)
{
uint8 x_473; 
x_473 = !lean::is_exclusive(x_472);
if (x_473 == 0)
{
obj* x_474; uint8 x_475; 
x_474 = lean::cnstr_get(x_472, 0);
x_475 = !lean::is_exclusive(x_474);
if (x_475 == 0)
{
obj* x_476; obj* x_477; obj* x_478; obj* x_479; uint8 x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; 
x_476 = lean::cnstr_get(x_472, 2);
x_477 = lean::cnstr_get(x_474, 0);
x_478 = lean::cnstr_get(x_474, 1);
x_479 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_479, 0, x_477);
x_480 = 0;
x_481 = lean::box(x_480);
lean::cnstr_set(x_474, 1, x_479);
lean::cnstr_set(x_474, 0, x_481);
x_482 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_482, 0, x_474);
lean::cnstr_set(x_482, 1, x_478);
lean::cnstr_set(x_472, 2, x_471);
lean::cnstr_set(x_472, 0, x_482);
x_483 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_476, x_472);
x_484 = l_Lean_Parser_finishCommentBlock___closed__2;
x_485 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_484, x_483);
x_255 = x_485;
x_256 = x_466;
goto block_459;
}
else
{
obj* x_486; obj* x_487; obj* x_488; obj* x_489; uint8 x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; obj* x_495; obj* x_496; 
x_486 = lean::cnstr_get(x_472, 2);
x_487 = lean::cnstr_get(x_474, 0);
x_488 = lean::cnstr_get(x_474, 1);
lean::inc(x_488);
lean::inc(x_487);
lean::dec(x_474);
x_489 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_489, 0, x_487);
x_490 = 0;
x_491 = lean::box(x_490);
x_492 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_492, 0, x_491);
lean::cnstr_set(x_492, 1, x_489);
x_493 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_493, 0, x_492);
lean::cnstr_set(x_493, 1, x_488);
lean::cnstr_set(x_472, 2, x_471);
lean::cnstr_set(x_472, 0, x_493);
x_494 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_486, x_472);
x_495 = l_Lean_Parser_finishCommentBlock___closed__2;
x_496 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_495, x_494);
x_255 = x_496;
x_256 = x_466;
goto block_459;
}
}
else
{
obj* x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; uint8 x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; 
x_497 = lean::cnstr_get(x_472, 0);
x_498 = lean::cnstr_get(x_472, 1);
x_499 = lean::cnstr_get(x_472, 2);
lean::inc(x_499);
lean::inc(x_498);
lean::inc(x_497);
lean::dec(x_472);
x_500 = lean::cnstr_get(x_497, 0);
lean::inc(x_500);
x_501 = lean::cnstr_get(x_497, 1);
lean::inc(x_501);
if (lean::is_exclusive(x_497)) {
 lean::cnstr_release(x_497, 0);
 lean::cnstr_release(x_497, 1);
 x_502 = x_497;
} else {
 lean::dec_ref(x_497);
 x_502 = lean::box(0);
}
x_503 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_503, 0, x_500);
x_504 = 0;
x_505 = lean::box(x_504);
if (lean::is_scalar(x_502)) {
 x_506 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_506 = x_502;
}
lean::cnstr_set(x_506, 0, x_505);
lean::cnstr_set(x_506, 1, x_503);
x_507 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_507, 0, x_506);
lean::cnstr_set(x_507, 1, x_501);
x_508 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_508, 0, x_507);
lean::cnstr_set(x_508, 1, x_498);
lean::cnstr_set(x_508, 2, x_471);
x_509 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_499, x_508);
x_510 = l_Lean_Parser_finishCommentBlock___closed__2;
x_511 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_510, x_509);
x_255 = x_511;
x_256 = x_466;
goto block_459;
}
}
else
{
uint8 x_512; 
x_512 = !lean::is_exclusive(x_472);
if (x_512 == 0)
{
obj* x_513; obj* x_514; 
x_513 = l_Lean_Parser_finishCommentBlock___closed__2;
x_514 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_513, x_472);
x_255 = x_514;
x_256 = x_466;
goto block_459;
}
else
{
obj* x_515; uint8 x_516; obj* x_517; obj* x_518; obj* x_519; 
x_515 = lean::cnstr_get(x_472, 0);
x_516 = lean::cnstr_get_scalar<uint8>(x_472, sizeof(void*)*1);
lean::inc(x_515);
lean::dec(x_472);
x_517 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_517, 0, x_515);
lean::cnstr_set_scalar(x_517, sizeof(void*)*1, x_516);
x_518 = l_Lean_Parser_finishCommentBlock___closed__2;
x_519 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_518, x_517);
x_255 = x_519;
x_256 = x_466;
goto block_459;
}
}
}
else
{
obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; 
x_520 = lean::cnstr_get(x_464, 0);
x_521 = lean::cnstr_get(x_464, 1);
x_522 = lean::cnstr_get(x_464, 2);
lean::inc(x_522);
lean::inc(x_521);
lean::inc(x_520);
lean::dec(x_464);
lean::inc(x_3);
lean::cnstr_set(x_463, 1, x_3);
lean::cnstr_set(x_463, 0, x_520);
x_523 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_524 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_524, 0, x_463);
lean::cnstr_set(x_524, 1, x_521);
lean::cnstr_set(x_524, 2, x_523);
x_525 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_522, x_524);
if (lean::obj_tag(x_525) == 0)
{
obj* x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; obj* x_531; obj* x_532; obj* x_533; uint8 x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; 
x_526 = lean::cnstr_get(x_525, 0);
lean::inc(x_526);
x_527 = lean::cnstr_get(x_525, 1);
lean::inc(x_527);
x_528 = lean::cnstr_get(x_525, 2);
lean::inc(x_528);
if (lean::is_exclusive(x_525)) {
 lean::cnstr_release(x_525, 0);
 lean::cnstr_release(x_525, 1);
 lean::cnstr_release(x_525, 2);
 x_529 = x_525;
} else {
 lean::dec_ref(x_525);
 x_529 = lean::box(0);
}
x_530 = lean::cnstr_get(x_526, 0);
lean::inc(x_530);
x_531 = lean::cnstr_get(x_526, 1);
lean::inc(x_531);
if (lean::is_exclusive(x_526)) {
 lean::cnstr_release(x_526, 0);
 lean::cnstr_release(x_526, 1);
 x_532 = x_526;
} else {
 lean::dec_ref(x_526);
 x_532 = lean::box(0);
}
x_533 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_533, 0, x_530);
x_534 = 0;
x_535 = lean::box(x_534);
if (lean::is_scalar(x_532)) {
 x_536 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_536 = x_532;
}
lean::cnstr_set(x_536, 0, x_535);
lean::cnstr_set(x_536, 1, x_533);
x_537 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_537, 0, x_536);
lean::cnstr_set(x_537, 1, x_531);
if (lean::is_scalar(x_529)) {
 x_538 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_538 = x_529;
}
lean::cnstr_set(x_538, 0, x_537);
lean::cnstr_set(x_538, 1, x_527);
lean::cnstr_set(x_538, 2, x_523);
x_539 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_528, x_538);
x_540 = l_Lean_Parser_finishCommentBlock___closed__2;
x_541 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_540, x_539);
x_255 = x_541;
x_256 = x_466;
goto block_459;
}
else
{
obj* x_542; uint8 x_543; obj* x_544; obj* x_545; obj* x_546; obj* x_547; 
x_542 = lean::cnstr_get(x_525, 0);
lean::inc(x_542);
x_543 = lean::cnstr_get_scalar<uint8>(x_525, sizeof(void*)*1);
if (lean::is_exclusive(x_525)) {
 lean::cnstr_release(x_525, 0);
 x_544 = x_525;
} else {
 lean::dec_ref(x_525);
 x_544 = lean::box(0);
}
if (lean::is_scalar(x_544)) {
 x_545 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_545 = x_544;
}
lean::cnstr_set(x_545, 0, x_542);
lean::cnstr_set_scalar(x_545, sizeof(void*)*1, x_543);
x_546 = l_Lean_Parser_finishCommentBlock___closed__2;
x_547 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_546, x_545);
x_255 = x_547;
x_256 = x_466;
goto block_459;
}
}
}
else
{
obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; 
x_548 = lean::cnstr_get(x_463, 1);
lean::inc(x_548);
lean::dec(x_463);
x_549 = lean::cnstr_get(x_464, 0);
lean::inc(x_549);
x_550 = lean::cnstr_get(x_464, 1);
lean::inc(x_550);
x_551 = lean::cnstr_get(x_464, 2);
lean::inc(x_551);
if (lean::is_exclusive(x_464)) {
 lean::cnstr_release(x_464, 0);
 lean::cnstr_release(x_464, 1);
 lean::cnstr_release(x_464, 2);
 x_552 = x_464;
} else {
 lean::dec_ref(x_464);
 x_552 = lean::box(0);
}
lean::inc(x_3);
x_553 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_553, 0, x_549);
lean::cnstr_set(x_553, 1, x_3);
x_554 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_552)) {
 x_555 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_555 = x_552;
}
lean::cnstr_set(x_555, 0, x_553);
lean::cnstr_set(x_555, 1, x_550);
lean::cnstr_set(x_555, 2, x_554);
x_556 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_551, x_555);
if (lean::obj_tag(x_556) == 0)
{
obj* x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_564; uint8 x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; obj* x_571; obj* x_572; 
x_557 = lean::cnstr_get(x_556, 0);
lean::inc(x_557);
x_558 = lean::cnstr_get(x_556, 1);
lean::inc(x_558);
x_559 = lean::cnstr_get(x_556, 2);
lean::inc(x_559);
if (lean::is_exclusive(x_556)) {
 lean::cnstr_release(x_556, 0);
 lean::cnstr_release(x_556, 1);
 lean::cnstr_release(x_556, 2);
 x_560 = x_556;
} else {
 lean::dec_ref(x_556);
 x_560 = lean::box(0);
}
x_561 = lean::cnstr_get(x_557, 0);
lean::inc(x_561);
x_562 = lean::cnstr_get(x_557, 1);
lean::inc(x_562);
if (lean::is_exclusive(x_557)) {
 lean::cnstr_release(x_557, 0);
 lean::cnstr_release(x_557, 1);
 x_563 = x_557;
} else {
 lean::dec_ref(x_557);
 x_563 = lean::box(0);
}
x_564 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_564, 0, x_561);
x_565 = 0;
x_566 = lean::box(x_565);
if (lean::is_scalar(x_563)) {
 x_567 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_567 = x_563;
}
lean::cnstr_set(x_567, 0, x_566);
lean::cnstr_set(x_567, 1, x_564);
x_568 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_568, 0, x_567);
lean::cnstr_set(x_568, 1, x_562);
if (lean::is_scalar(x_560)) {
 x_569 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_569 = x_560;
}
lean::cnstr_set(x_569, 0, x_568);
lean::cnstr_set(x_569, 1, x_558);
lean::cnstr_set(x_569, 2, x_554);
x_570 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_559, x_569);
x_571 = l_Lean_Parser_finishCommentBlock___closed__2;
x_572 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_571, x_570);
x_255 = x_572;
x_256 = x_548;
goto block_459;
}
else
{
obj* x_573; uint8 x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; 
x_573 = lean::cnstr_get(x_556, 0);
lean::inc(x_573);
x_574 = lean::cnstr_get_scalar<uint8>(x_556, sizeof(void*)*1);
if (lean::is_exclusive(x_556)) {
 lean::cnstr_release(x_556, 0);
 x_575 = x_556;
} else {
 lean::dec_ref(x_556);
 x_575 = lean::box(0);
}
if (lean::is_scalar(x_575)) {
 x_576 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_576 = x_575;
}
lean::cnstr_set(x_576, 0, x_573);
lean::cnstr_set_scalar(x_576, sizeof(void*)*1, x_574);
x_577 = l_Lean_Parser_finishCommentBlock___closed__2;
x_578 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_577, x_576);
x_255 = x_578;
x_256 = x_548;
goto block_459;
}
}
}
else
{
obj* x_579; uint8 x_580; 
x_579 = lean::cnstr_get(x_463, 1);
lean::inc(x_579);
lean::dec(x_463);
x_580 = !lean::is_exclusive(x_464);
if (x_580 == 0)
{
obj* x_581; obj* x_582; 
x_581 = l_Lean_Parser_finishCommentBlock___closed__2;
x_582 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_581, x_464);
x_255 = x_582;
x_256 = x_579;
goto block_459;
}
else
{
obj* x_583; uint8 x_584; obj* x_585; obj* x_586; obj* x_587; 
x_583 = lean::cnstr_get(x_464, 0);
x_584 = lean::cnstr_get_scalar<uint8>(x_464, sizeof(void*)*1);
lean::inc(x_583);
lean::dec(x_464);
x_585 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_585, 0, x_583);
lean::cnstr_set_scalar(x_585, sizeof(void*)*1, x_584);
x_586 = l_Lean_Parser_finishCommentBlock___closed__2;
x_587 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_586, x_585);
x_255 = x_587;
x_256 = x_579;
goto block_459;
}
}
block_459:
{
if (lean::obj_tag(x_255) == 0)
{
lean::dec(x_5);
x_92 = x_255;
x_93 = x_256;
goto block_253;
}
else
{
obj* x_257; uint8 x_258; obj* x_259; obj* x_260; 
x_257 = lean::cnstr_get(x_255, 0);
lean::inc(x_257);
x_258 = lean::cnstr_get_scalar<uint8>(x_255, sizeof(void*)*1);
if (x_258 == 0)
{
lean::dec(x_255);
if (x_254 == 0)
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; 
x_446 = lean::box(0);
lean::inc(x_3);
x_447 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_447, 0, x_446);
lean::cnstr_set(x_447, 1, x_3);
x_448 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_449 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_449, 0, x_447);
lean::cnstr_set(x_449, 1, x_5);
lean::cnstr_set(x_449, 2, x_448);
x_259 = x_449;
x_260 = x_256;
goto block_445;
}
else
{
obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; 
x_450 = l_String_splitAux___main___closed__1;
x_451 = l_Lean_Parser_command_Parser___rarg___closed__1;
x_452 = l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
lean::inc(x_5);
x_453 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_453, 0, x_5);
lean::cnstr_set(x_453, 1, x_450);
lean::cnstr_set(x_453, 2, x_451);
lean::cnstr_set(x_453, 3, x_452);
lean::inc(x_3);
x_454 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_453, x_3, x_4, x_5, x_256);
x_455 = lean::cnstr_get(x_454, 0);
lean::inc(x_455);
x_456 = lean::cnstr_get(x_454, 1);
lean::inc(x_456);
lean::dec(x_454);
x_457 = l_Lean_Parser_finishCommentBlock___closed__2;
x_458 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_457, x_455);
x_259 = x_458;
x_260 = x_456;
goto block_445;
}
}
else
{
lean::dec(x_257);
lean::dec(x_5);
x_92 = x_255;
x_93 = x_256;
goto block_253;
}
block_445:
{
if (lean::obj_tag(x_259) == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_305; obj* x_306; obj* x_307; obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
x_261 = lean::cnstr_get(x_259, 0);
lean::inc(x_261);
x_262 = lean::cnstr_get(x_259, 1);
lean::inc(x_262);
x_263 = lean::cnstr_get(x_259, 2);
lean::inc(x_263);
lean::dec(x_259);
x_305 = lean::cnstr_get(x_261, 1);
lean::inc(x_305);
lean::dec(x_261);
x_347 = lean::cnstr_get(x_4, 0);
lean::inc(x_347);
x_348 = lean::cnstr_get(x_347, 0);
lean::inc(x_348);
lean::dec(x_347);
lean::inc(x_262);
x_349 = l_Lean_Parser_token(x_348, x_262, x_260);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
if (lean::obj_tag(x_350) == 0)
{
uint8 x_351; 
x_351 = !lean::is_exclusive(x_349);
if (x_351 == 0)
{
obj* x_352; obj* x_353; uint8 x_354; 
x_352 = lean::cnstr_get(x_349, 1);
x_353 = lean::cnstr_get(x_349, 0);
lean::dec(x_353);
x_354 = !lean::is_exclusive(x_350);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; 
x_355 = lean::cnstr_get(x_350, 0);
x_356 = lean::cnstr_get(x_350, 2);
lean::inc(x_305);
lean::cnstr_set(x_349, 1, x_305);
lean::cnstr_set(x_349, 0, x_355);
x_357 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_350, 2, x_357);
lean::cnstr_set(x_350, 0, x_349);
x_358 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_350);
if (lean::obj_tag(x_358) == 0)
{
uint8 x_359; 
x_359 = !lean::is_exclusive(x_358);
if (x_359 == 0)
{
obj* x_360; uint8 x_361; 
x_360 = lean::cnstr_get(x_358, 0);
x_361 = !lean::is_exclusive(x_360);
if (x_361 == 0)
{
obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; 
x_362 = lean::cnstr_get(x_358, 2);
x_363 = lean::cnstr_get(x_360, 0);
lean::dec(x_363);
x_364 = lean::box(0);
lean::cnstr_set(x_360, 0, x_364);
lean::cnstr_set(x_358, 2, x_357);
x_365 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_362, x_358);
x_366 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_365);
x_306 = x_366;
x_307 = x_352;
goto block_346;
}
else
{
obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
x_367 = lean::cnstr_get(x_358, 2);
x_368 = lean::cnstr_get(x_360, 1);
lean::inc(x_368);
lean::dec(x_360);
x_369 = lean::box(0);
x_370 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_370, 0, x_369);
lean::cnstr_set(x_370, 1, x_368);
lean::cnstr_set(x_358, 2, x_357);
lean::cnstr_set(x_358, 0, x_370);
x_371 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_367, x_358);
x_372 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_371);
x_306 = x_372;
x_307 = x_352;
goto block_346;
}
}
else
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; 
x_373 = lean::cnstr_get(x_358, 0);
x_374 = lean::cnstr_get(x_358, 1);
x_375 = lean::cnstr_get(x_358, 2);
lean::inc(x_375);
lean::inc(x_374);
lean::inc(x_373);
lean::dec(x_358);
x_376 = lean::cnstr_get(x_373, 1);
lean::inc(x_376);
if (lean::is_exclusive(x_373)) {
 lean::cnstr_release(x_373, 0);
 lean::cnstr_release(x_373, 1);
 x_377 = x_373;
} else {
 lean::dec_ref(x_373);
 x_377 = lean::box(0);
}
x_378 = lean::box(0);
if (lean::is_scalar(x_377)) {
 x_379 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_379 = x_377;
}
lean::cnstr_set(x_379, 0, x_378);
lean::cnstr_set(x_379, 1, x_376);
x_380 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_380, 0, x_379);
lean::cnstr_set(x_380, 1, x_374);
lean::cnstr_set(x_380, 2, x_357);
x_381 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_375, x_380);
x_382 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_381);
x_306 = x_382;
x_307 = x_352;
goto block_346;
}
}
else
{
uint8 x_383; 
x_383 = !lean::is_exclusive(x_358);
if (x_383 == 0)
{
uint8 x_384; 
x_384 = 0;
lean::cnstr_set_scalar(x_358, sizeof(void*)*1, x_384);
x_306 = x_358;
x_307 = x_352;
goto block_346;
}
else
{
obj* x_385; uint8 x_386; obj* x_387; 
x_385 = lean::cnstr_get(x_358, 0);
lean::inc(x_385);
lean::dec(x_358);
x_386 = 0;
x_387 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_387, 0, x_385);
lean::cnstr_set_scalar(x_387, sizeof(void*)*1, x_386);
x_306 = x_387;
x_307 = x_352;
goto block_346;
}
}
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; 
x_388 = lean::cnstr_get(x_350, 0);
x_389 = lean::cnstr_get(x_350, 1);
x_390 = lean::cnstr_get(x_350, 2);
lean::inc(x_390);
lean::inc(x_389);
lean::inc(x_388);
lean::dec(x_350);
lean::inc(x_305);
lean::cnstr_set(x_349, 1, x_305);
lean::cnstr_set(x_349, 0, x_388);
x_391 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_392 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_392, 0, x_349);
lean::cnstr_set(x_392, 1, x_389);
lean::cnstr_set(x_392, 2, x_391);
x_393 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_390, x_392);
if (lean::obj_tag(x_393) == 0)
{
obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; 
x_394 = lean::cnstr_get(x_393, 0);
lean::inc(x_394);
x_395 = lean::cnstr_get(x_393, 1);
lean::inc(x_395);
x_396 = lean::cnstr_get(x_393, 2);
lean::inc(x_396);
if (lean::is_exclusive(x_393)) {
 lean::cnstr_release(x_393, 0);
 lean::cnstr_release(x_393, 1);
 lean::cnstr_release(x_393, 2);
 x_397 = x_393;
} else {
 lean::dec_ref(x_393);
 x_397 = lean::box(0);
}
x_398 = lean::cnstr_get(x_394, 1);
lean::inc(x_398);
if (lean::is_exclusive(x_394)) {
 lean::cnstr_release(x_394, 0);
 lean::cnstr_release(x_394, 1);
 x_399 = x_394;
} else {
 lean::dec_ref(x_394);
 x_399 = lean::box(0);
}
x_400 = lean::box(0);
if (lean::is_scalar(x_399)) {
 x_401 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_401 = x_399;
}
lean::cnstr_set(x_401, 0, x_400);
lean::cnstr_set(x_401, 1, x_398);
if (lean::is_scalar(x_397)) {
 x_402 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_402 = x_397;
}
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_395);
lean::cnstr_set(x_402, 2, x_391);
x_403 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_396, x_402);
x_404 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_403);
x_306 = x_404;
x_307 = x_352;
goto block_346;
}
else
{
obj* x_405; obj* x_406; uint8 x_407; obj* x_408; 
x_405 = lean::cnstr_get(x_393, 0);
lean::inc(x_405);
if (lean::is_exclusive(x_393)) {
 lean::cnstr_release(x_393, 0);
 x_406 = x_393;
} else {
 lean::dec_ref(x_393);
 x_406 = lean::box(0);
}
x_407 = 0;
if (lean::is_scalar(x_406)) {
 x_408 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_408 = x_406;
}
lean::cnstr_set(x_408, 0, x_405);
lean::cnstr_set_scalar(x_408, sizeof(void*)*1, x_407);
x_306 = x_408;
x_307 = x_352;
goto block_346;
}
}
}
else
{
obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; 
x_409 = lean::cnstr_get(x_349, 1);
lean::inc(x_409);
lean::dec(x_349);
x_410 = lean::cnstr_get(x_350, 0);
lean::inc(x_410);
x_411 = lean::cnstr_get(x_350, 1);
lean::inc(x_411);
x_412 = lean::cnstr_get(x_350, 2);
lean::inc(x_412);
if (lean::is_exclusive(x_350)) {
 lean::cnstr_release(x_350, 0);
 lean::cnstr_release(x_350, 1);
 lean::cnstr_release(x_350, 2);
 x_413 = x_350;
} else {
 lean::dec_ref(x_350);
 x_413 = lean::box(0);
}
lean::inc(x_305);
x_414 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_414, 0, x_410);
lean::cnstr_set(x_414, 1, x_305);
x_415 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_413)) {
 x_416 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_416 = x_413;
}
lean::cnstr_set(x_416, 0, x_414);
lean::cnstr_set(x_416, 1, x_411);
lean::cnstr_set(x_416, 2, x_415);
x_417 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_412, x_416);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; 
x_418 = lean::cnstr_get(x_417, 0);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_417, 1);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_417, 2);
lean::inc(x_420);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 x_421 = x_417;
} else {
 lean::dec_ref(x_417);
 x_421 = lean::box(0);
}
x_422 = lean::cnstr_get(x_418, 1);
lean::inc(x_422);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 x_423 = x_418;
} else {
 lean::dec_ref(x_418);
 x_423 = lean::box(0);
}
x_424 = lean::box(0);
if (lean::is_scalar(x_423)) {
 x_425 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_425 = x_423;
}
lean::cnstr_set(x_425, 0, x_424);
lean::cnstr_set(x_425, 1, x_422);
if (lean::is_scalar(x_421)) {
 x_426 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_426 = x_421;
}
lean::cnstr_set(x_426, 0, x_425);
lean::cnstr_set(x_426, 1, x_419);
lean::cnstr_set(x_426, 2, x_415);
x_427 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_420, x_426);
x_428 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_427);
x_306 = x_428;
x_307 = x_409;
goto block_346;
}
else
{
obj* x_429; obj* x_430; uint8 x_431; obj* x_432; 
x_429 = lean::cnstr_get(x_417, 0);
lean::inc(x_429);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 x_430 = x_417;
} else {
 lean::dec_ref(x_417);
 x_430 = lean::box(0);
}
x_431 = 0;
if (lean::is_scalar(x_430)) {
 x_432 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_432 = x_430;
}
lean::cnstr_set(x_432, 0, x_429);
lean::cnstr_set_scalar(x_432, sizeof(void*)*1, x_431);
x_306 = x_432;
x_307 = x_409;
goto block_346;
}
}
}
else
{
obj* x_433; uint8 x_434; 
x_433 = lean::cnstr_get(x_349, 1);
lean::inc(x_433);
lean::dec(x_349);
x_434 = !lean::is_exclusive(x_350);
if (x_434 == 0)
{
uint8 x_435; 
x_435 = 0;
lean::cnstr_set_scalar(x_350, sizeof(void*)*1, x_435);
x_306 = x_350;
x_307 = x_433;
goto block_346;
}
else
{
obj* x_436; uint8 x_437; obj* x_438; 
x_436 = lean::cnstr_get(x_350, 0);
lean::inc(x_436);
lean::dec(x_350);
x_437 = 0;
x_438 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_438, 0, x_436);
lean::cnstr_set_scalar(x_438, sizeof(void*)*1, x_437);
x_306 = x_438;
x_307 = x_433;
goto block_346;
}
}
block_304:
{
if (lean::obj_tag(x_264) == 0)
{
uint8 x_266; 
x_266 = !lean::is_exclusive(x_264);
if (x_266 == 0)
{
obj* x_267; uint8 x_268; 
x_267 = lean::cnstr_get(x_264, 0);
x_268 = !lean::is_exclusive(x_267);
if (x_268 == 0)
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_269 = lean::cnstr_get(x_264, 2);
x_270 = lean::cnstr_get(x_267, 0);
lean::dec(x_270);
x_271 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
lean::cnstr_set(x_267, 0, x_271);
x_272 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_264, 2, x_272);
x_273 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_269, x_264);
x_274 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_273);
x_275 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_274);
x_92 = x_275;
x_93 = x_265;
goto block_253;
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; 
x_276 = lean::cnstr_get(x_264, 2);
x_277 = lean::cnstr_get(x_267, 1);
lean::inc(x_277);
lean::dec(x_267);
x_278 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
x_279 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_277);
x_280 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_264, 2, x_280);
lean::cnstr_set(x_264, 0, x_279);
x_281 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_276, x_264);
x_282 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_281);
x_283 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_282);
x_92 = x_283;
x_93 = x_265;
goto block_253;
}
}
else
{
obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
x_284 = lean::cnstr_get(x_264, 0);
x_285 = lean::cnstr_get(x_264, 1);
x_286 = lean::cnstr_get(x_264, 2);
lean::inc(x_286);
lean::inc(x_285);
lean::inc(x_284);
lean::dec(x_264);
x_287 = lean::cnstr_get(x_284, 1);
lean::inc(x_287);
if (lean::is_exclusive(x_284)) {
 lean::cnstr_release(x_284, 0);
 lean::cnstr_release(x_284, 1);
 x_288 = x_284;
} else {
 lean::dec_ref(x_284);
 x_288 = lean::box(0);
}
x_289 = l___private_init_lean_parser_module_1__commandWrecAux___main___closed__2;
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_287);
x_291 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_292 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_292, 0, x_290);
lean::cnstr_set(x_292, 1, x_285);
lean::cnstr_set(x_292, 2, x_291);
x_293 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_286, x_292);
x_294 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_293);
x_295 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_294);
x_92 = x_295;
x_93 = x_265;
goto block_253;
}
}
else
{
uint8 x_296; 
x_296 = !lean::is_exclusive(x_264);
if (x_296 == 0)
{
obj* x_297; obj* x_298; 
x_297 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_264);
x_298 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_297);
x_92 = x_298;
x_93 = x_265;
goto block_253;
}
else
{
obj* x_299; uint8 x_300; obj* x_301; obj* x_302; obj* x_303; 
x_299 = lean::cnstr_get(x_264, 0);
x_300 = lean::cnstr_get_scalar<uint8>(x_264, sizeof(void*)*1);
lean::inc(x_299);
lean::dec(x_264);
x_301 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_301, 0, x_299);
lean::cnstr_set_scalar(x_301, sizeof(void*)*1, x_300);
x_302 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_301);
x_303 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_302);
x_92 = x_303;
x_93 = x_265;
goto block_253;
}
}
}
block_346:
{
if (lean::obj_tag(x_306) == 0)
{
lean::dec(x_305);
lean::dec(x_262);
x_264 = x_306;
x_265 = x_307;
goto block_304;
}
else
{
uint8 x_308; 
x_308 = lean::cnstr_get_scalar<uint8>(x_306, sizeof(void*)*1);
if (x_308 == 0)
{
obj* x_309; obj* x_310; obj* x_311; 
x_309 = lean::cnstr_get(x_306, 0);
lean::inc(x_309);
lean::dec(x_306);
x_310 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(x_305, x_4, x_262, x_307);
x_311 = lean::cnstr_get(x_310, 0);
lean::inc(x_311);
if (lean::obj_tag(x_311) == 0)
{
obj* x_312; obj* x_313; uint8 x_314; 
x_312 = lean::cnstr_get(x_311, 0);
lean::inc(x_312);
x_313 = lean::cnstr_get(x_310, 1);
lean::inc(x_313);
lean::dec(x_310);
x_314 = !lean::is_exclusive(x_311);
if (x_314 == 0)
{
obj* x_315; obj* x_316; uint8 x_317; 
x_315 = lean::cnstr_get(x_311, 2);
x_316 = lean::cnstr_get(x_311, 0);
lean::dec(x_316);
x_317 = !lean::is_exclusive(x_312);
if (x_317 == 0)
{
obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
x_318 = lean::cnstr_get(x_312, 0);
lean::dec(x_318);
x_319 = lean::box(0);
lean::cnstr_set(x_312, 0, x_319);
x_320 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_311, 2, x_320);
x_321 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_315, x_311);
x_322 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_309, x_321);
x_264 = x_322;
x_265 = x_313;
goto block_304;
}
else
{
obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
x_323 = lean::cnstr_get(x_312, 1);
lean::inc(x_323);
lean::dec(x_312);
x_324 = lean::box(0);
x_325 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_325, 0, x_324);
lean::cnstr_set(x_325, 1, x_323);
x_326 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_311, 2, x_326);
lean::cnstr_set(x_311, 0, x_325);
x_327 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_315, x_311);
x_328 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_309, x_327);
x_264 = x_328;
x_265 = x_313;
goto block_304;
}
}
else
{
obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; 
x_329 = lean::cnstr_get(x_311, 1);
x_330 = lean::cnstr_get(x_311, 2);
lean::inc(x_330);
lean::inc(x_329);
lean::dec(x_311);
x_331 = lean::cnstr_get(x_312, 1);
lean::inc(x_331);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_332 = x_312;
} else {
 lean::dec_ref(x_312);
 x_332 = lean::box(0);
}
x_333 = lean::box(0);
if (lean::is_scalar(x_332)) {
 x_334 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_334 = x_332;
}
lean::cnstr_set(x_334, 0, x_333);
lean::cnstr_set(x_334, 1, x_331);
x_335 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_336 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_336, 0, x_334);
lean::cnstr_set(x_336, 1, x_329);
lean::cnstr_set(x_336, 2, x_335);
x_337 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_330, x_336);
x_338 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_309, x_337);
x_264 = x_338;
x_265 = x_313;
goto block_304;
}
}
else
{
obj* x_339; uint8 x_340; 
x_339 = lean::cnstr_get(x_310, 1);
lean::inc(x_339);
lean::dec(x_310);
x_340 = !lean::is_exclusive(x_311);
if (x_340 == 0)
{
obj* x_341; 
x_341 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_309, x_311);
x_264 = x_341;
x_265 = x_339;
goto block_304;
}
else
{
obj* x_342; uint8 x_343; obj* x_344; obj* x_345; 
x_342 = lean::cnstr_get(x_311, 0);
x_343 = lean::cnstr_get_scalar<uint8>(x_311, sizeof(void*)*1);
lean::inc(x_342);
lean::dec(x_311);
x_344 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_344, 0, x_342);
lean::cnstr_set_scalar(x_344, sizeof(void*)*1, x_343);
x_345 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_309, x_344);
x_264 = x_345;
x_265 = x_339;
goto block_304;
}
}
}
else
{
lean::dec(x_305);
lean::dec(x_262);
x_264 = x_306;
x_265 = x_307;
goto block_304;
}
}
}
}
else
{
uint8 x_439; 
x_439 = !lean::is_exclusive(x_259);
if (x_439 == 0)
{
obj* x_440; 
x_440 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_259);
x_92 = x_440;
x_93 = x_260;
goto block_253;
}
else
{
obj* x_441; uint8 x_442; obj* x_443; obj* x_444; 
x_441 = lean::cnstr_get(x_259, 0);
x_442 = lean::cnstr_get_scalar<uint8>(x_259, sizeof(void*)*1);
lean::inc(x_441);
lean::dec(x_259);
x_443 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_443, 0, x_441);
lean::cnstr_set_scalar(x_443, sizeof(void*)*1, x_442);
x_444 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_257, x_443);
x_92 = x_444;
x_93 = x_260;
goto block_253;
}
}
}
}
}
}
}
else
{
obj* x_670; obj* x_671; obj* x_672; obj* x_673; 
x_670 = lean::box(0);
x_671 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_672 = l_mjoin___rarg___closed__1;
x_673 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_Module_eoi_Parser___spec__2___rarg(x_671, x_672, x_670, x_670, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_673;
}
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_logMessage___at___private_init_lean_parser_module_1__commandWrecAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
lean::dec(x_1);
x_8 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_8;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_module_1__commandWrecAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
lean::dec(x_1);
x_8 = l___private_init_lean_parser_module_1__commandWrecAux(x_7, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_Module_parseCommandWithRecovery(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_6, x_7);
lean::dec(x_6);
x_9 = l___private_init_lean_parser_module_1__commandWrecAux___main(x_1, x_8, x_2, x_3, x_4, x_5);
lean::dec(x_8);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
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
x_16 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
obj* l_Lean_Parser_Module_parseCommandWithRecovery___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_Module_parseCommandWithRecovery(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_2(x_1, x_2, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_5, 0, x_10);
return x_5;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::dec(x_5);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_5);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_5, 0);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_5, 0, x_18);
return x_5;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_20 = lean::cnstr_get(x_6, 0);
lean::inc(x_20);
lean::dec(x_6);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
}
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_Parser_resumeModuleParser___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_MessageLog_empty;
x_6 = lean::apply_4(x_1, x_5, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_7);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_7, 2);
x_13 = lean::cnstr_get(x_7, 0);
lean::dec(x_13);
x_14 = !lean::is_exclusive(x_8);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_16, 0, x_15);
lean::cnstr_set(x_8, 0, x_16);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_17);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_7);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_18, 1);
x_23 = lean::cnstr_get(x_18, 2);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
x_25 = lean::apply_1(x_24, x_22);
lean::cnstr_set(x_20, 0, x_25);
x_26 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
lean::cnstr_set(x_18, 2, x_26);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_18);
lean::cnstr_set(x_6, 0, x_27);
return x_6;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_18, 1);
x_29 = lean::cnstr_get(x_18, 2);
x_30 = lean::cnstr_get(x_20, 0);
x_31 = lean::cnstr_get(x_20, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_20);
lean::inc(x_28);
x_32 = lean::apply_1(x_30, x_28);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
x_34 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
lean::cnstr_set(x_18, 2, x_34);
lean::cnstr_set(x_18, 0, x_33);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_18);
lean::cnstr_set(x_6, 0, x_35);
return x_6;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_18, 0);
x_37 = lean::cnstr_get(x_18, 1);
x_38 = lean::cnstr_get(x_18, 2);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_18);
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_41 = x_36;
} else {
 lean::dec_ref(x_36);
 x_41 = lean::box(0);
}
lean::inc(x_37);
x_42 = lean::apply_1(x_39, x_37);
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_40);
x_44 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_37);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_45);
lean::cnstr_set(x_6, 0, x_46);
return x_6;
}
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_18);
if (x_47 == 0)
{
lean::cnstr_set(x_6, 0, x_18);
return x_6;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_18, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
lean::inc(x_48);
lean::dec(x_18);
x_50 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_49);
lean::cnstr_set(x_6, 0, x_50);
return x_6;
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get(x_8, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_8);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_53, 0, x_51);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_55);
lean::cnstr_set(x_7, 0, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_7);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_56, 2);
lean::inc(x_59);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 lean::cnstr_release(x_56, 2);
 x_60 = x_56;
} else {
 lean::dec_ref(x_56);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_57, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_63 = x_57;
} else {
 lean::dec_ref(x_57);
 x_63 = lean::box(0);
}
lean::inc(x_58);
x_64 = lean::apply_1(x_61, x_58);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_62);
x_66 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_60)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_60;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_58);
lean::cnstr_set(x_67, 2, x_66);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_67);
lean::cnstr_set(x_6, 0, x_68);
return x_6;
}
else
{
obj* x_69; uint8 x_70; obj* x_71; obj* x_72; 
x_69 = lean::cnstr_get(x_56, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_71 = x_56;
} else {
 lean::dec_ref(x_56);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
lean::cnstr_set(x_6, 0, x_72);
return x_6;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_7, 1);
x_74 = lean::cnstr_get(x_7, 2);
lean::inc(x_74);
lean::inc(x_73);
lean::dec(x_7);
x_75 = lean::cnstr_get(x_8, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_8, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_77 = x_8;
} else {
 lean::dec_ref(x_8);
 x_77 = lean::box(0);
}
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_78, 0, x_75);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_82, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 lean::cnstr_release(x_82, 2);
 x_86 = x_82;
} else {
 lean::dec_ref(x_82);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_83, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_89 = x_83;
} else {
 lean::dec_ref(x_83);
 x_89 = lean::box(0);
}
lean::inc(x_84);
x_90 = lean::apply_1(x_87, x_84);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
x_92 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_86)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_86;
}
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_84);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_93);
lean::cnstr_set(x_6, 0, x_94);
return x_6;
}
else
{
obj* x_95; uint8 x_96; obj* x_97; obj* x_98; 
x_95 = lean::cnstr_get(x_82, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 x_97 = x_82;
} else {
 lean::dec_ref(x_82);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
lean::cnstr_set(x_6, 0, x_98);
return x_6;
}
}
}
else
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_6, 1);
lean::inc(x_99);
lean::dec(x_6);
x_100 = lean::cnstr_get(x_7, 1);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_7, 2);
lean::inc(x_101);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_102 = x_7;
} else {
 lean::dec_ref(x_7);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_8, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_8, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_105 = x_8;
} else {
 lean::dec_ref(x_8);
 x_105 = lean::box(0);
}
x_106 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_106, 0, x_103);
if (lean::is_scalar(x_105)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_105;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_104);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_102)) {
 x_109 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_109 = x_102;
}
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_100);
lean::cnstr_set(x_109, 2, x_108);
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_110, 1);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_110, 2);
lean::inc(x_113);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 lean::cnstr_release(x_110, 2);
 x_114 = x_110;
} else {
 lean::dec_ref(x_110);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_111, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_111, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_117 = x_111;
} else {
 lean::dec_ref(x_111);
 x_117 = lean::box(0);
}
lean::inc(x_112);
x_118 = lean::apply_1(x_115, x_112);
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_116);
x_120 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_Module_eoi_Parser___spec__1___closed__1;
if (lean::is_scalar(x_114)) {
 x_121 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_121 = x_114;
}
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_112);
lean::cnstr_set(x_121, 2, x_120);
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_121);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_99);
return x_123;
}
else
{
obj* x_124; uint8 x_125; obj* x_126; obj* x_127; obj* x_128; 
x_124 = lean::cnstr_get(x_110, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 x_126 = x_110;
} else {
 lean::dec_ref(x_110);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*1, x_125);
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_99);
return x_128;
}
}
}
else
{
uint8 x_129; 
x_129 = !lean::is_exclusive(x_6);
if (x_129 == 0)
{
obj* x_130; uint8 x_131; 
x_130 = lean::cnstr_get(x_6, 0);
lean::dec(x_130);
x_131 = !lean::is_exclusive(x_7);
if (x_131 == 0)
{
return x_6;
}
else
{
obj* x_132; uint8 x_133; obj* x_134; 
x_132 = lean::cnstr_get(x_7, 0);
x_133 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_132);
lean::dec(x_7);
x_134 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_134, 0, x_132);
lean::cnstr_set_scalar(x_134, sizeof(void*)*1, x_133);
lean::cnstr_set(x_6, 0, x_134);
return x_6;
}
}
else
{
obj* x_135; obj* x_136; uint8 x_137; obj* x_138; obj* x_139; obj* x_140; 
x_135 = lean::cnstr_get(x_6, 1);
lean::inc(x_135);
lean::dec(x_6);
x_136 = lean::cnstr_get(x_7, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_138 = x_7;
} else {
 lean::dec_ref(x_7);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set_scalar(x_139, sizeof(void*)*1, x_137);
x_140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_135);
return x_140;
}
}
}
}
obj* l_Lean_Parser_resumeModuleParser___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_resumeModuleParser___rarg___lambda__1), 4, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_Lean_Parser_run___rarg___closed__1;
x_9 = l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(x_5, x_6, x_7, x_8);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
lean::dec(x_12);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_13; 
lean::dec(x_3);
x_13 = !lean::is_exclusive(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
x_19 = l_Lean_Parser_messageOfParsecMessage___rarg(x_18, x_14);
lean::dec(x_18);
lean::cnstr_set(x_11, 0, x_19);
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; 
lean::dec(x_15);
x_20 = lean::box(3);
lean::cnstr_set(x_9, 1, x_11);
lean::cnstr_set(x_9, 0, x_20);
return x_9;
}
else
{
obj* x_21; 
x_21 = lean::cnstr_get(x_15, 0);
lean::inc(x_21);
lean::dec(x_15);
lean::cnstr_set(x_9, 1, x_11);
lean::cnstr_set(x_9, 0, x_21);
return x_9;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
lean::dec(x_11);
x_23 = lean::cnstr_get(x_22, 3);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = l_Lean_Parser_messageOfParsecMessage___rarg(x_26, x_22);
lean::dec(x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; 
lean::dec(x_23);
x_29 = lean::box(3);
lean::cnstr_set(x_9, 1, x_28);
lean::cnstr_set(x_9, 0, x_29);
return x_9;
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
lean::cnstr_set(x_9, 1, x_28);
lean::cnstr_set(x_9, 0, x_30);
return x_9;
}
}
}
else
{
uint8 x_31; 
lean::free_heap_obj(x_9);
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_11);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_32 = lean::cnstr_get(x_11, 0);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
x_35 = !lean::is_exclusive(x_33);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
x_36 = lean::cnstr_get(x_33, 0);
x_37 = lean::cnstr_get(x_33, 1);
x_38 = lean::apply_1(x_3, x_36);
x_39 = !lean::is_exclusive(x_38);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = lean::cnstr_get(x_38, 1);
x_41 = !lean::is_exclusive(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_40, 0);
lean::dec(x_43);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
lean::cnstr_set(x_38, 0, x_40);
lean::cnstr_set(x_11, 0, x_38);
lean::cnstr_set(x_33, 1, x_11);
lean::cnstr_set(x_33, 0, x_42);
return x_33;
}
else
{
obj* x_44; uint8 x_45; obj* x_46; 
x_44 = lean::cnstr_get(x_38, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_45);
lean::cnstr_set(x_38, 1, x_34);
lean::cnstr_set(x_38, 0, x_46);
lean::cnstr_set(x_11, 0, x_38);
lean::cnstr_set(x_33, 1, x_11);
lean::cnstr_set(x_33, 0, x_44);
return x_33;
}
}
else
{
obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_47 = lean::cnstr_get(x_38, 1);
x_48 = lean::cnstr_get(x_38, 0);
lean::inc(x_47);
lean::inc(x_48);
lean::dec(x_38);
x_49 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_50 = x_47;
} else {
 lean::dec_ref(x_47);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_37);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_34);
lean::cnstr_set(x_11, 0, x_52);
lean::cnstr_set(x_33, 1, x_11);
lean::cnstr_set(x_33, 0, x_48);
return x_33;
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_53 = lean::cnstr_get(x_33, 0);
x_54 = lean::cnstr_get(x_33, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_33);
x_55 = lean::apply_1(x_3, x_53);
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_55, 0);
lean::inc(x_57);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_58 = x_55;
} else {
 lean::dec_ref(x_55);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_60 = x_56;
} else {
 lean::dec_ref(x_56);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 1);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_54);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_59);
if (lean::is_scalar(x_58)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_58;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_34);
lean::cnstr_set(x_11, 0, x_62);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_57);
lean::cnstr_set(x_63, 1, x_11);
return x_63;
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_64 = lean::cnstr_get(x_11, 0);
lean::inc(x_64);
lean::dec(x_11);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
lean::dec(x_64);
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_69 = x_65;
} else {
 lean::dec_ref(x_65);
 x_69 = lean::box(0);
}
x_70 = lean::apply_1(x_3, x_67);
x_71 = lean::cnstr_get(x_70, 1);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_73 = x_70;
} else {
 lean::dec_ref(x_70);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_75 = x_71;
} else {
 lean::dec_ref(x_71);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 1);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_74);
if (lean::is_scalar(x_73)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_73;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_66);
x_78 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
if (lean::is_scalar(x_69)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_69;
}
lean::cnstr_set(x_79, 0, x_72);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
obj* x_80; 
x_80 = lean::cnstr_get(x_9, 0);
lean::inc(x_80);
lean::dec(x_9);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_3);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_82 = x_80;
} else {
 lean::dec_ref(x_80);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_81, 3);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_1, 0);
lean::inc(x_84);
lean::dec(x_1);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
lean::dec(x_84);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
lean::dec(x_85);
x_87 = l_Lean_Parser_messageOfParsecMessage___rarg(x_86, x_81);
lean::dec(x_86);
if (lean::is_scalar(x_82)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_82;
}
lean::cnstr_set(x_88, 0, x_87);
if (lean::obj_tag(x_83) == 0)
{
obj* x_89; obj* x_90; 
lean::dec(x_83);
x_89 = lean::box(3);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
return x_90;
}
else
{
obj* x_91; obj* x_92; 
x_91 = lean::cnstr_get(x_83, 0);
lean::inc(x_91);
lean::dec(x_83);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_88);
return x_92;
}
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_1);
x_93 = lean::cnstr_get(x_80, 0);
lean::inc(x_93);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_94 = x_80;
} else {
 lean::dec_ref(x_80);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_93, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_99 = x_95;
} else {
 lean::dec_ref(x_95);
 x_99 = lean::box(0);
}
x_100 = lean::apply_1(x_3, x_97);
x_101 = lean::cnstr_get(x_100, 1);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 x_103 = x_100;
} else {
 lean::dec_ref(x_100);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 x_105 = x_101;
} else {
 lean::dec_ref(x_101);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_98);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
if (lean::is_scalar(x_103)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_103;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_96);
if (lean::is_scalar(x_94)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_94;
}
lean::cnstr_set(x_108, 0, x_107);
if (lean::is_scalar(x_99)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_99;
}
lean::cnstr_set(x_109, 0, x_102);
lean::cnstr_set(x_109, 1, x_108);
return x_109;
}
}
}
}
obj* l_Lean_Parser_resumeModuleParser(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_resumeModuleParser___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_runFrom___at_Lean_Parser_resumeModuleParser___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_4);
x_7 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
x_15 = lean::apply_5(x_2, x_13, x_14, x_4, x_11, x_10);
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
lean::dec(x_4);
lean::dec(x_2);
x_23 = !lean::is_exclusive(x_7);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = lean::cnstr_get(x_7, 0);
lean::dec(x_24);
x_25 = !lean::is_exclusive(x_8);
if (x_25 == 0)
{
return x_7;
}
else
{
obj* x_26; uint8 x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_8, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_26);
lean::dec(x_8);
x_28 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_27);
lean::cnstr_set(x_7, 0, x_28);
return x_7;
}
}
else
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_7, 1);
lean::inc(x_29);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_8, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_32 = x_8;
} else {
 lean::dec_ref(x_8);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_29);
return x_34;
}
}
}
}
obj* l_StateT_bind___at_Lean_Parser_parseHeader___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg), 6, 0);
return x_3;
}
}
obj* l_Lean_Parser_parseHeader___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_Parser_parseHeader___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
x_7 = l_Lean_Parser_whitespace(x_6, x_3, x_4);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_8, 2);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 0, x_13);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_8, 2, x_15);
lean::cnstr_set(x_8, 0, x_7);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_8);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_8, 0);
x_19 = lean::cnstr_get(x_8, 1);
x_20 = lean::cnstr_get(x_8, 2);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_8);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 0, x_18);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_10);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_7, 1);
lean::inc(x_25);
lean::dec(x_7);
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_8, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_8, 2);
lean::inc(x_28);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_29 = x_8;
} else {
 lean::dec_ref(x_8);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_29)) {
 x_32 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_32 = x_29;
}
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_27);
lean::cnstr_set(x_32, 2, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8 x_35; 
lean::dec(x_1);
x_35 = !lean::is_exclusive(x_7);
if (x_35 == 0)
{
obj* x_36; uint8 x_37; 
x_36 = lean::cnstr_get(x_7, 0);
lean::dec(x_36);
x_37 = !lean::is_exclusive(x_8);
if (x_37 == 0)
{
return x_7;
}
else
{
obj* x_38; uint8 x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_8, 0);
x_39 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_38);
lean::dec(x_8);
x_40 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_39);
lean::cnstr_set(x_7, 0, x_40);
return x_7;
}
}
else
{
obj* x_41; obj* x_42; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_7, 1);
lean::inc(x_41);
lean::dec(x_7);
x_42 = lean::cnstr_get(x_8, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_44 = x_8;
} else {
 lean::dec_ref(x_8);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set_scalar(x_45, sizeof(void*)*1, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_41);
return x_46;
}
}
}
}
obj* l_Lean_Parser_parseHeader___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_Module_header_Parser(x_7, x_4, x_5);
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
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_9, 0);
x_15 = lean::cnstr_get(x_9, 2);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_14);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_9, 2, x_16);
lean::cnstr_set(x_9, 0, x_8);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_9);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_9, 0);
x_20 = lean::cnstr_get(x_9, 1);
x_21 = lean::cnstr_get(x_9, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_9);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_19);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_8);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = lean::cnstr_get(x_8, 1);
lean::inc(x_26);
lean::dec(x_8);
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_9, 1);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_9, 2);
lean::inc(x_29);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_30 = x_9;
} else {
 lean::dec_ref(x_9);
 x_30 = lean::box(0);
}
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_2);
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_30)) {
 x_33 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_33 = x_30;
}
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_28);
lean::cnstr_set(x_33, 2, x_32);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_2);
x_36 = !lean::is_exclusive(x_8);
if (x_36 == 0)
{
obj* x_37; uint8 x_38; 
x_37 = lean::cnstr_get(x_8, 0);
lean::dec(x_37);
x_38 = !lean::is_exclusive(x_9);
if (x_38 == 0)
{
return x_8;
}
else
{
obj* x_39; uint8 x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_9, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_39);
lean::dec(x_9);
x_41 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_40);
lean::cnstr_set(x_8, 0, x_41);
return x_8;
}
}
else
{
obj* x_42; obj* x_43; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_8, 1);
lean::inc(x_42);
lean::dec(x_8);
x_43 = lean::cnstr_get(x_9, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_45 = x_9;
} else {
 lean::dec_ref(x_9);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
return x_47;
}
}
}
}
obj* _init_l_Lean_Parser_parseHeader___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__2___boxed), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__3___boxed), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_StateT_bind___at_Lean_Parser_parseHeader___spec__1___rarg), 6, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_parseHeader(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_6);
x_8 = 0;
x_9 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseHeader___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = l_Lean_Parser_parseHeader___closed__1;
x_12 = l_Lean_Parser_resumeModuleParser___rarg(x_1, x_9, x_10, x_11);
return x_12;
}
}
obj* l_Lean_Parser_parseHeader___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_parseHeader___lambda__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_parseHeader___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseHeader___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_parseCommand___lambda__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::unbox(x_5);
lean::dec(x_5);
lean::cnstr_set_scalar(x_1, sizeof(void*)*1, x_7);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::unbox(x_8);
lean::dec(x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_12);
lean::cnstr_set(x_2, 1, x_11);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_16 = x_1;
} else {
 lean::dec_ref(x_1);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 1);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_15);
x_18 = lean::unbox(x_13);
lean::dec(x_13);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_18);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
}
obj* l_Lean_Parser_parseCommand(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseCommand___lambda__1), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_5 = lean::box(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Module_parseCommandWithRecovery___boxed), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_resumeModuleParser___rarg(x_1, x_2, x_3, x_6);
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
if (io_result_is_error(w)) return w;
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
l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_prelude_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_Module_prelude_HasView_x27 = _init_l_Lean_Parser_Module_prelude_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Module_prelude_HasView_x27);
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
l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_Module_importPath_HasView_x27 = _init_l_Lean_Parser_Module_importPath_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Module_importPath_HasView_x27);
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
l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_Module_import_HasView_x27 = _init_l_Lean_Parser_Module_import_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Module_import_HasView_x27);
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
l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6 = _init_l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27___lambda__1___closed__6);
l_Lean_Parser_Module_header_HasView_x27 = _init_l_Lean_Parser_Module_header_HasView_x27();
lean::mark_persistent(l_Lean_Parser_Module_header_HasView_x27);
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
