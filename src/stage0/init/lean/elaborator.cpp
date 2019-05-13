// Lean compiler output
// Module: init.lean.elaborator
// Imports: init.lean.parser.module init.lean.expander init.lean.expr init.lean.options init.lean.environment
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
obj* l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_currentScope___boxed(obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_Lean_Expander_getOptType___main(obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1(obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__2;
obj* l_Lean_Elaborator_notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_postprocessNotationSpec___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__2;
obj* l_Lean_Elaborator_include_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_precToNat(obj*);
obj* l_Lean_Parser_stringLit_View_value(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_zipWith___main___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Expander_getOptType___main___closed__1;
obj* l_Lean_Elaborator_dummy;
obj* l_Lean_Elaborator_toPexpr___main___closed__8;
extern obj* l_Lean_MessageLog_empty;
obj* l_Lean_Elaborator_toPexpr___main___closed__46;
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_Lean_KVMap_setBool(obj*, obj*, uint8);
uint8 l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(obj*, uint8, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
obj* l_Lean_Elaborator_mkState___closed__3;
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(obj*);
obj* l_Lean_Elaborator_processCommand(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__1;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_MonadExcept;
obj* l_Lean_Elaborator_attribute_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__6;
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__21;
obj* l_Lean_Elaborator_matchSpec(obj*, obj*);
obj* l_Lean_Elaborator_matchOpenSpec(obj*, obj*);
obj* l_Lean_Elaborator_declaration_elaborate___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_toList___at_Lean_Elaborator_oldElabCommand___spec__1(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___rarg(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__3;
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace;
extern obj* l_Lean_Parser_Level_trailing_HasView;
obj* l_List_lengthAux___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_identUnivParamsToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Module_header;
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__22;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadState;
obj* l_Lean_Elaborator_elaborators;
obj* l_StateT_Monad___rarg(obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___closed__1;
obj* l_Lean_Elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_variables_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__2;
obj* l_Lean_Elaborator_declaration_elaborate___closed__3;
obj* l_Lean_Elaborator_variables_elaborate(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace(obj*, obj*);
extern obj* l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__37;
extern "C" obj* level_mk_mvar(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg(obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1;
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__3;
obj* l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__9;
extern obj* l_Lean_Parser_command_attribute;
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__30;
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
extern obj* l_Lean_Parser_command_variables;
obj* l_Lean_Elaborator_elabDefLike(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__4;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_mangleIdent___spec__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__3;
obj* l_Lean_Elaborator_elabDefLike___lambda__1(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__28;
extern obj* l_Lean_Parser_Term_have_HasView;
obj* l_Lean_Expr_mkCapp(obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__19;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___boxed(obj*);
obj* l_Lean_Elaborator_declaration_elaborate___closed__1;
obj* l_Lean_Elaborator_OrderedRBMap_ofList___boxed(obj*, obj*);
obj* l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__31;
extern obj* l_Lean_Parser_Term_structInst_HasView;
obj* l_Lean_Elaborator_universe_elaborate___closed__1;
obj* l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(obj*);
obj* l_Lean_Elaborator_mkNotationKind(obj*, obj*);
obj* l_Lean_Elaborator_command_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__34;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__3(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__45;
obj* l_Lean_Elaborator_toLevel___main___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_Elaborator_section_elaborate___closed__2;
obj* l_Lean_Elaborator_universe_elaborate___closed__2;
obj* l_Lean_Elaborator_toPexpr___main___closed__1;
extern obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Elaborator_check_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___rarg___boxed(obj*);
obj* l_monadStateTrans___rarg(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namesToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___boxed(obj*, obj*);
obj* l_Lean_Name_quickLt___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Lean_Elaborator_mkState___closed__4;
obj* l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_Lean_Elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_section;
obj* l_Lean_Elaborator_toPexpr___main___closed__14;
obj* l_ExceptT_MonadExcept___rarg(obj*);
extern obj* l_Lean_Parser_command_attribute_HasView;
obj* l_Lean_Elaborator_toPexpr___main___closed__32;
extern obj* l_Lean_Parser_command_reserveNotation_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj*, obj*);
extern obj* l_Id_Monad;
extern obj* l_Lean_Parser_command_export_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__1;
extern obj* l_Lean_Parser_command_declaration_HasView;
obj* l_Lean_Elaborator_notation_elaborateAux(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderIdent_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__18;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__6;
obj* l_Lean_Elaborator_toPexpr___main___closed__10;
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__3(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__44;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___main(obj*, obj*);
extern obj* l_Lean_Parser_command_end_HasView;
obj* l_Lean_Elaborator_attribute_elaborate___closed__2;
obj* l_Lean_Elaborator_elaboratorInh___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4;
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj*, obj*);
obj* l_fix1___rarg___lambda__1___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_end;
extern obj* l_Lean_Parser_Term_sort_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__27;
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_command_export;
obj* l_Lean_Elaborator_end_elaborate___closed__4;
obj* l_Lean_Elaborator_mangleIdent(obj*);
obj* l_Lean_Elaborator_universe_elaborate___lambda__1(obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace___main(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__12;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Term_show_HasView;
obj* l_List_join___main___rarg(obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__29;
extern obj* l_Lean_Parser_Term_structInstItem_HasView;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1;
extern obj* l_Lean_Parser_command_setOption_HasView;
obj* l_Lean_Elaborator_Expr_mkAnnotation___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2;
obj* l_Lean_Elaborator_registerNotationMacro(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__20;
extern obj* l_Lean_Parser_command_initQuot;
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_open_HasView;
obj* l_Lean_Elaborator_inferModToPexpr___boxed(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_check;
extern obj* l_Lean_Parser_Term_explicit_HasView;
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__17;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(obj*, obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_Elaborator_noKind_elaborate___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
extern obj* l_Lean_Parser_command_include_HasView;
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
obj* l_Lean_Elaborator_end_elaborate___closed__3;
obj* l_Lean_Elaborator_toPexpr___main___closed__33;
obj* l_Lean_Elaborator_notation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Expander_builtinTransformers___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkEqns___closed__1;
obj* l_Lean_Parser_Syntax_getPos(obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___boxed(obj*, obj*);
extern obj* l_Lean_Expander_builtinTransformers;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___boxed(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__4;
extern obj* l_Char_HasRepr___closed__1;
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Elaborator_toPexpr___main___closed__39;
extern obj* l_Lean_Parser_Term_lambda_HasView;
obj* l_Lean_Elaborator_mkState(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__36;
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve___main___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3;
obj* l_Lean_Elaborator_isOpenNamespace___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Module_header_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj*, obj*);
extern obj* l_Lean_Parser_command_setOption;
obj* l_Lean_Elaborator_toPexpr___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Elaborator_matchPrecedence___main___boxed(obj*, obj*);
obj* l_Lean_Elaborator_declaration_elaborate___closed__2;
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__1(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Module_eoi;
obj* l_Lean_Elaborator_attrsToPexpr(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaborateCommand___boxed(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_identUnivParamsToPexpr___spec__1(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(uint8, obj*);
obj* l_Lean_Elaborator_inferModToPexpr(obj*);
obj* l_Lean_Elaborator_Expr_mkAnnotation(obj*, obj*);
obj* l_StateT_MonadExcept___rarg(obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate___closed__1;
obj* l_Lean_Elaborator_currentScope___closed__1;
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(obj*);
obj* l_Lean_Elaborator_setOption_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate___closed__1;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationTokens(obj*, obj*);
obj* l_Lean_Elaborator_updateParserConfig___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__11;
obj* l_Lean_Elaborator_toPexpr___main___closed__40;
obj* l_Lean_Elaborator_eoi_elaborate___closed__1;
obj* l_Lean_Elaborator_toLevel___main___closed__3;
obj* l_Lean_Elaborator_end_elaborate___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find___boxed(obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate___boxed(obj*, obj*, obj*, obj*);
uint8 l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(obj*, uint8, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(obj*, obj*);
extern obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find(obj*, obj*);
obj* l_Lean_Elaborator_preresolve(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Expander_expandBracketedBinder___main___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__13;
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__1;
obj* l_Lean_Elaborator_mkEqns___closed__2;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Elaborator_processCommand___closed__1;
obj* l_Lean_Elaborator_check_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_open;
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation_HasView;
extern obj* l_Lean_Parser_command_section_HasView;
obj* l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Term_app_HasView;
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate___lambda__1(obj*, obj*);
uint8 l_Lean_Elaborator_matchPrecedence(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_projection_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
extern obj* l_Lean_Parser_maxPrec;
extern "C" obj* lean_expr_mk_bvar(obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_Lean_Elaborator_setOption_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_sortApp_HasView;
obj* l_Lean_Elaborator_mkNotationKind___boxed(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty(obj*, obj*);
obj* l_Lean_Elaborator_mkEqns(obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_isOpenNamespace___boxed(obj*, obj*);
obj* l_String_trim(obj*);
extern obj* l_Lean_Parser_command_universe;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__7;
extern "C" obj* level_mk_succ(obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__43;
extern obj* l_Lean_Expander_bindingAnnotationUpdate;
obj* l_Lean_Elaborator_toPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace_HasView;
obj* l_Lean_Elaborator_setOption_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__1;
obj* l_Lean_Elaborator_levelGetAppArgs___main(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_declaration;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___closed__1;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___closed__1;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(obj*);
obj* l_Lean_Parser_Syntax_format___main(obj*);
obj* l_Lean_Elaborator_getNamespace___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_universe_HasView;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__5;
obj* l_Lean_Elaborator_levelGetAppArgs___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_anonymousConstructor_HasView;
obj* l_Lean_Elaborator_end_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__24;
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2;
uint8 l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_borrowed_HasView;
obj* l_Lean_Elaborator_declaration_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__26;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_List_zip___rarg___closed__1;
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_declaration_elaborate___closed__4;
obj* l_Lean_Elaborator_elabDefLike___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ExceptT_Monad___rarg(obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Elaborator_preresolve___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2(obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__38;
obj* l_RBNode_revFold___main___at_Lean_Elaborator_oldElabCommand___spec__2(obj*, obj*);
extern obj* l_Lean_Parser_command_check_HasView;
obj* l_Lean_Elaborator_variables_elaborate___closed__2;
obj* l_Lean_Elaborator_processCommand___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_insertCore___main(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__16;
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__35;
obj* l_Lean_Elaborator_toPexpr___main___closed__7;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Elaborator_Module_header_elaborate___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Elaborator_declModifiersToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_updateParserConfig(obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadReader;
obj* l_Lean_Elaborator_toPexpr___main___closed__41;
obj* l_Lean_Elaborator_toPexpr___main___closed__25;
uint8 l_Lean_Environment_contains(obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate___closed__1;
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3(obj*, obj*);
obj* l_Lean_Elaborator_matchPrecedence___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1;
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(obj*, obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_kind___main(obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5;
obj* l_Lean_Elaborator_variables_elaborate___closed__1;
obj* l_Lean_Elaborator_modifyCurrentScope(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(obj*, obj*, obj*);
obj* l_Lean_Elaborator_export_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__5;
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_Monad;
obj* l_Lean_Elaborator_levelAdd(obj*, obj*);
obj* l_Lean_Elaborator_eoi_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(obj*, obj*);
extern obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Elaborator_toLevel___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_currentScope(obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___boxed(obj*);
extern obj* l_Lean_Parser_Term_inaccessible_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_precToNat___main(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__1;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_match_HasView;
obj* l_Lean_Parser_Term_getLeading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig___boxed(obj*);
obj* l_Lean_Expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(obj*, obj*, obj*);
extern obj* l_Lean_Expander_noExpansion___closed__1;
extern obj* l_Lean_Parser_Term_sort_HasView;
obj* l_Lean_Elaborator_resolveContext(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__23;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declaration_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3___boxed(obj*, obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__2;
extern obj* l_Lean_Parser_command_reserveNotation;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___closed__1;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1___boxed(obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1(obj*, uint8, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_declaration_elaborate___spec__3(obj*);
uint8 l_Lean_Elaborator_matchPrecedence___main(obj*, obj*);
obj* l_Lean_Elaborator_attrsToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__2;
obj* l_Lean_Elaborator_initQuot_elaborate___closed__1;
obj* l_StateT_MonadState___rarg(obj*);
obj* l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1___boxed(obj*, obj*);
extern obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___closed__1;
obj* l_Lean_Elaborator_getNamespace(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_let_HasView;
obj* l_Lean_Parser_number_View_toNat___main(obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_Parser_Term_binders_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declaration_elaborate___closed__5;
extern obj* l_Lean_Parser_Term_pi_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__42;
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_paren_transform___spec__1(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__15;
obj* l_Lean_Elaborator_postprocessNotationSpec(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Elaborator_locally(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_include;
obj* l_Lean_Expr_local___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = lean_expr_local(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_Elaborator_elaborateCommand___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_elaborator_elaborate_command(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_empty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_empty(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_3);
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_add(x_12, x_17);
lean::dec(x_12);
x_20 = l_RBNode_insert___rarg(x_0, x_10, x_2, x_16);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_18);
return x_21;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_insert___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_6 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_3, x_2);
return x_6;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_find___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_OrderedRBMap_empty___rarg(x_0);
x_3 = l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_ofList___rarg), 2, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_ofList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
x_2 = l_StateT_Monad___rarg(x_1);
x_3 = l_ReaderT_Monad___rarg(x_2);
x_4 = l_ReaderT_Monad___rarg(x_3);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___rarg), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
x_2 = l_StateT_Monad___rarg(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___rarg___boxed), 2, 1);
lean::closure_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_MonadState() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
lean::inc(x_1);
x_3 = l_StateT_Monad___rarg(x_1);
lean::inc(x_3);
x_5 = l_ReaderT_Monad___rarg(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_7, 0, lean::box(0));
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, x_3);
x_8 = l_StateT_MonadState___rarg(x_1);
x_9 = l_monadStateTrans___rarg(x_7, x_8);
x_10 = l_monadStateTrans___rarg(x_6, x_9);
return x_10;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
x_2 = l_ExceptT_MonadExcept___rarg(x_0);
x_3 = l_StateT_MonadExcept___rarg(x_1, lean::box(0), x_2);
x_4 = l_ReaderT_MonadExcept___rarg(x_3);
x_5 = l_ReaderT_MonadExcept___rarg(x_4);
return x_5;
}
}
obj* _init_l_Lean_Elaborator_elaboratorInh___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string("");
x_5 = 2;
lean::inc(x_4);
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 4, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*5, x_5);
x_9 = x_8;
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
obj* l_Lean_Elaborator_elaboratorInh(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_elaboratorInh___closed__1;
return x_4;
}
}
obj* l_Lean_Elaborator_elaboratorInh___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_elaboratorInh(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_command_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_3(x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::mk_nat_obj(0ul);
x_15 = l_Lean_FileMap_toPosition(x_10, x_14);
x_16 = 2;
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_17);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_16);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_Lean_Parser_Syntax_getPos(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_23 = lean::mk_nat_obj(0ul);
x_24 = l_Lean_FileMap_toPosition(x_10, x_23);
x_25 = 2;
x_26 = l_String_splitAux___main___closed__1;
x_27 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_27, 0, x_8);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_13);
lean::cnstr_set(x_27, 3, x_26);
lean::cnstr_set(x_27, 4, x_1);
lean::cnstr_set_scalar(x_27, sizeof(void*)*5, x_25);
x_28 = x_27;
x_29 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_30; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
lean::dec(x_22);
x_33 = l_Lean_FileMap_toPosition(x_10, x_30);
x_34 = 2;
x_35 = l_String_splitAux___main___closed__1;
x_36 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_36, 0, x_8);
lean::cnstr_set(x_36, 1, x_33);
lean::cnstr_set(x_36, 2, x_13);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set(x_36, 4, x_1);
lean::cnstr_set_scalar(x_36, sizeof(void*)*5, x_34);
x_37 = x_36;
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_currentScope___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("currentScope: unreachable");
return x_0;
}
}
obj* l_Lean_Elaborator_currentScope(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 4);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = l_Lean_Elaborator_currentScope___closed__1;
x_7 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_5, x_6, x_0, x_1, x_2);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_2);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Elaborator_currentScope___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_currentScope(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_Elaborator_modifyCurrentScope___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("modifyCurrentScope: unreachable");
return x_0;
}
}
obj* l_Lean_Elaborator_modifyCurrentScope(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_Lean_Elaborator_modifyCurrentScope___closed__1;
x_9 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_7, x_8, x_1, x_2, x_3);
lean::dec(x_3);
return x_9;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_2);
x_12 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
x_16 = lean::cnstr_get(x_3, 2);
x_18 = lean::cnstr_get(x_3, 3);
x_20 = lean::cnstr_get(x_3, 5);
x_22 = lean::cnstr_get(x_3, 6);
x_24 = lean::cnstr_get(x_3, 7);
x_26 = lean::cnstr_get(x_3, 8);
x_28 = lean::cnstr_get(x_3, 9);
x_30 = lean::cnstr_get(x_3, 10);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 4);
 x_32 = x_3;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_3);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_4, 0);
x_35 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_37 = x_4;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_4);
 x_37 = lean::box(0);
}
x_38 = lean::apply_1(x_0, x_33);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_35);
if (lean::is_scalar(x_32)) {
 x_40 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_40 = x_32;
}
lean::cnstr_set(x_40, 0, x_12);
lean::cnstr_set(x_40, 1, x_14);
lean::cnstr_set(x_40, 2, x_16);
lean::cnstr_set(x_40, 3, x_18);
lean::cnstr_set(x_40, 4, x_39);
lean::cnstr_set(x_40, 5, x_20);
lean::cnstr_set(x_40, 6, x_22);
lean::cnstr_set(x_40, 7, x_24);
lean::cnstr_set(x_40, 8, x_26);
lean::cnstr_set(x_40, 9, x_28);
lean::cnstr_set(x_40, 10, x_30);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
}
obj* l_Lean_Elaborator_modifyCurrentScope___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_modifyCurrentScope(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_mangleIdent___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean_name_mk_numeral(x_0, x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Lean_Elaborator_mangleIdent(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 2);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 4);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_List_foldl___main___at_Lean_Elaborator_mangleIdent___spec__1(x_1, x_3);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_levelGetAppArgs___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("levelGetAppArgs: unexpected input: ");
return x_0;
}
}
obj* l_Lean_Elaborator_levelGetAppArgs___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_0);
x_5 = l_Lean_Parser_Syntax_kind___main(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_0);
x_8 = l_Lean_Parser_Syntax_format___main(x_0);
x_9 = l_Lean_Options_empty;
x_10 = l_Lean_Format_pretty(x_8, x_9);
x_11 = l_Lean_Elaborator_levelGetAppArgs___main___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_7, x_12, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_7);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; uint8 x_21; 
x_17 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_19 = x_5;
} else {
 lean::inc(x_17);
 lean::dec(x_5);
 x_19 = lean::box(0);
}
x_20 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
x_21 = lean_name_dec_eq(x_17, x_20);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
x_23 = lean_name_dec_eq(x_17, x_22);
lean::dec(x_17);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
lean::inc(x_0);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_0);
x_27 = l_Lean_Parser_Syntax_format___main(x_0);
x_28 = l_Lean_Options_empty;
x_29 = l_Lean_Format_pretty(x_27, x_28);
x_30 = l_Lean_Elaborator_levelGetAppArgs___main___closed__1;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_33 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_26, x_31, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_26);
return x_33;
}
else
{
obj* x_37; obj* x_38; obj* x_42; 
lean::dec(x_19);
x_37 = l_Lean_Parser_Level_trailing_HasView;
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
lean::dec(x_37);
lean::inc(x_0);
x_42 = lean::apply_1(x_38, x_0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_47; obj* x_49; 
lean::dec(x_0);
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = l_Lean_Elaborator_levelGetAppArgs___main(x_47, x_1, x_2, x_3);
if (lean::obj_tag(x_49) == 0)
{
obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_44);
x_51 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_53 = x_49;
} else {
 lean::inc(x_51);
 lean::dec(x_49);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_55 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_57 = x_49;
} else {
 lean::inc(x_55);
 lean::dec(x_49);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_55, 0);
x_60 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_62 = x_55;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_55);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_58, 0);
x_65 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 x_67 = x_58;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_58);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_44, 1);
lean::inc(x_68);
lean::dec(x_44);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_65);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_63);
lean::cnstr_set(x_72, 1, x_71);
if (lean::is_scalar(x_62)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_62;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_60);
if (lean::is_scalar(x_57)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_57;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_2);
lean::dec(x_42);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_0);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_3);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_19);
lean::dec(x_2);
lean::dec(x_17);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_0);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_3);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
}
}
}
obj* l_Lean_Elaborator_levelGetAppArgs___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_levelGetAppArgs___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_levelGetAppArgs(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_levelGetAppArgs___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_levelGetAppArgs___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_levelGetAppArgs(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_levelAdd___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_sub(x_1, x_4);
x_6 = l_Lean_Elaborator_levelAdd___main(x_0, x_5);
lean::dec(x_5);
x_8 = level_mk_succ(x_6);
return x_8;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_Lean_Elaborator_levelAdd___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_levelAdd___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_levelAdd(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_levelAdd___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_levelAdd___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_levelAdd(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_Lean_Elaborator_toLevel___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(x_0, x_5);
x_9 = level_mk_max(x_3, x_8);
return x_9;
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(x_0, x_5);
x_9 = level_mk_imax(x_3, x_8);
return x_9;
}
}
}
obj* _init_l_Lean_Elaborator_toLevel___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toLevel: unexpected input: ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toLevel___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed universe Level");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toLevel___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = level_mk_mvar(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toLevel___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown universe variable '");
return x_0;
}
}
obj* l_Lean_Elaborator_toLevel___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_Lean_Elaborator_levelGetAppArgs___main(x_0, x_1, x_2, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_27; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::dec(x_16);
lean::inc(x_2);
x_27 = l_Lean_Elaborator_currentScope(x_1, x_2, x_18);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_21);
lean::dec(x_23);
x_32 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_34 = x_27;
} else {
 lean::inc(x_32);
 lean::dec(x_27);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; 
x_36 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_38 = x_27;
} else {
 lean::inc(x_36);
 lean::dec(x_27);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 lean::cnstr_set(x_36, 1, lean::box(0));
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
lean::inc(x_21);
x_45 = l_Lean_Parser_Syntax_kind___main(x_21);
if (lean::obj_tag(x_45) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::inc(x_0);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_0);
x_53 = l_Lean_Parser_Syntax_format___main(x_0);
x_54 = l_Lean_Options_empty;
x_55 = l_Lean_Format_pretty(x_53, x_54);
x_56 = l_Lean_Elaborator_toLevel___main___closed__1;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_59 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_52, x_57, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_52);
return x_59;
}
else
{
obj* x_62; obj* x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_set(x_45, 0, lean::box(0));
 x_64 = x_45;
} else {
 lean::inc(x_62);
 lean::dec(x_45);
 x_64 = lean::box(0);
}
x_65 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
x_66 = lean_name_dec_eq(x_62, x_65);
if (x_66 == 0)
{
obj* x_70; uint8 x_71; 
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
x_70 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
x_71 = lean_name_dec_eq(x_62, x_70);
lean::dec(x_62);
if (x_71 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_83; 
lean::dec(x_21);
lean::dec(x_23);
lean::inc(x_0);
if (lean::is_scalar(x_64)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_64;
}
lean::cnstr_set(x_76, 0, x_0);
x_77 = l_Lean_Parser_Syntax_format___main(x_0);
x_78 = l_Lean_Options_empty;
x_79 = l_Lean_Format_pretty(x_77, x_78);
x_80 = l_Lean_Elaborator_toLevel___main___closed__1;
x_81 = lean::string_append(x_80, x_79);
lean::dec(x_79);
x_83 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_76, x_81, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_76);
return x_83;
}
else
{
obj* x_86; obj* x_87; obj* x_90; 
x_86 = l_Lean_Parser_Level_trailing_HasView;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_90 = lean::apply_1(x_87, x_21);
if (lean::obj_tag(x_90) == 0)
{
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_90);
lean::dec(x_23);
if (lean::is_scalar(x_64)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_64;
}
lean::cnstr_set(x_93, 0, x_0);
x_94 = l_Lean_Elaborator_toLevel___main___closed__2;
x_95 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_93, x_94, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_93);
return x_95;
}
else
{
if (lean::obj_tag(x_23) == 0)
{
obj* x_100; obj* x_103; obj* x_105; 
lean::dec(x_64);
lean::dec(x_0);
x_100 = lean::cnstr_get(x_90, 0);
lean::inc(x_100);
lean::dec(x_90);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = l_Lean_Elaborator_toLevel___main(x_103, x_1, x_2, x_41);
if (lean::obj_tag(x_105) == 0)
{
obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_100);
x_107 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_109 = x_105;
} else {
 lean::inc(x_107);
 lean::dec(x_105);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
return x_110;
}
else
{
obj* x_111; obj* x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_119; obj* x_122; obj* x_123; obj* x_126; obj* x_127; 
x_111 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_113 = x_105;
} else {
 lean::inc(x_111);
 lean::dec(x_105);
 x_113 = lean::box(0);
}
x_114 = lean::cnstr_get(x_111, 0);
x_116 = lean::cnstr_get(x_111, 1);
if (lean::is_exclusive(x_111)) {
 x_118 = x_111;
} else {
 lean::inc(x_114);
 lean::inc(x_116);
 lean::dec(x_111);
 x_118 = lean::box(0);
}
x_119 = lean::cnstr_get(x_100, 2);
lean::inc(x_119);
lean::dec(x_100);
x_122 = l_Lean_Parser_number_View_toNat___main(x_119);
x_123 = l_Lean_Elaborator_levelAdd___main(x_114, x_122);
lean::dec(x_122);
lean::dec(x_114);
if (lean::is_scalar(x_118)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_118;
}
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_116);
if (lean::is_scalar(x_113)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_113;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
}
else
{
obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_90);
lean::dec(x_23);
if (lean::is_scalar(x_64)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_64;
}
lean::cnstr_set(x_130, 0, x_0);
x_131 = l_Lean_Elaborator_toLevel___main___closed__2;
x_132 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_130, x_131, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_130);
return x_132;
}
}
}
}
else
{
obj* x_136; obj* x_137; obj* x_140; 
lean::dec(x_62);
x_136 = l_Lean_Parser_Level_leading_HasView;
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
lean::dec(x_136);
x_140 = lean::apply_1(x_137, x_21);
switch (lean::obj_tag(x_140)) {
case 0:
{
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_145; obj* x_146; obj* x_147; 
if (lean::is_scalar(x_64)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_64;
}
lean::cnstr_set(x_145, 0, x_0);
x_146 = l_Lean_Elaborator_toLevel___main___closed__2;
x_147 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_145, x_146, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_145);
return x_147;
}
else
{
obj* x_152; obj* x_154; obj* x_158; 
lean::dec(x_64);
lean::dec(x_0);
x_152 = lean::cnstr_get(x_23, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_23, 1);
lean::inc(x_154);
lean::dec(x_23);
lean::inc(x_2);
x_158 = l_Lean_Elaborator_toLevel___main(x_152, x_1, x_2, x_41);
if (lean::obj_tag(x_158) == 0)
{
obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_154);
lean::dec(x_2);
x_161 = lean::cnstr_get(x_158, 0);
if (lean::is_exclusive(x_158)) {
 x_163 = x_158;
} else {
 lean::inc(x_161);
 lean::dec(x_158);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
return x_164;
}
else
{
obj* x_165; obj* x_168; obj* x_170; obj* x_173; 
x_165 = lean::cnstr_get(x_158, 0);
lean::inc(x_165);
lean::dec(x_158);
x_168 = lean::cnstr_get(x_165, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_165, 1);
lean::inc(x_170);
lean::dec(x_165);
x_173 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(x_154, x_1, x_2, x_170);
if (lean::obj_tag(x_173) == 0)
{
obj* x_175; obj* x_177; obj* x_178; 
lean::dec(x_168);
x_175 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_177 = x_173;
} else {
 lean::inc(x_175);
 lean::dec(x_173);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_175);
return x_178;
}
else
{
obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_186; obj* x_187; obj* x_189; obj* x_190; 
x_179 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_181 = x_173;
} else {
 lean::inc(x_179);
 lean::dec(x_173);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_179, 0);
x_184 = lean::cnstr_get(x_179, 1);
if (lean::is_exclusive(x_179)) {
 x_186 = x_179;
} else {
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_179);
 x_186 = lean::box(0);
}
x_187 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(x_168, x_182);
lean::dec(x_168);
if (lean::is_scalar(x_186)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_186;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_184);
if (lean::is_scalar(x_181)) {
 x_190 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_190 = x_181;
}
lean::cnstr_set(x_190, 0, x_189);
return x_190;
}
}
}
}
case 1:
{
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_195; obj* x_196; obj* x_197; 
if (lean::is_scalar(x_64)) {
 x_195 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_195 = x_64;
}
lean::cnstr_set(x_195, 0, x_0);
x_196 = l_Lean_Elaborator_toLevel___main___closed__2;
x_197 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_195, x_196, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_195);
return x_197;
}
else
{
obj* x_202; obj* x_204; obj* x_208; 
lean::dec(x_64);
lean::dec(x_0);
x_202 = lean::cnstr_get(x_23, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_23, 1);
lean::inc(x_204);
lean::dec(x_23);
lean::inc(x_2);
x_208 = l_Lean_Elaborator_toLevel___main(x_202, x_1, x_2, x_41);
if (lean::obj_tag(x_208) == 0)
{
obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_204);
lean::dec(x_2);
x_211 = lean::cnstr_get(x_208, 0);
if (lean::is_exclusive(x_208)) {
 x_213 = x_208;
} else {
 lean::inc(x_211);
 lean::dec(x_208);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
return x_214;
}
else
{
obj* x_215; obj* x_218; obj* x_220; obj* x_223; 
x_215 = lean::cnstr_get(x_208, 0);
lean::inc(x_215);
lean::dec(x_208);
x_218 = lean::cnstr_get(x_215, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_215, 1);
lean::inc(x_220);
lean::dec(x_215);
x_223 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(x_204, x_1, x_2, x_220);
if (lean::obj_tag(x_223) == 0)
{
obj* x_225; obj* x_227; obj* x_228; 
lean::dec(x_218);
x_225 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_227 = x_223;
} else {
 lean::inc(x_225);
 lean::dec(x_223);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_225);
return x_228;
}
else
{
obj* x_229; obj* x_231; obj* x_232; obj* x_234; obj* x_236; obj* x_237; obj* x_239; obj* x_240; 
x_229 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_231 = x_223;
} else {
 lean::inc(x_229);
 lean::dec(x_223);
 x_231 = lean::box(0);
}
x_232 = lean::cnstr_get(x_229, 0);
x_234 = lean::cnstr_get(x_229, 1);
if (lean::is_exclusive(x_229)) {
 x_236 = x_229;
} else {
 lean::inc(x_232);
 lean::inc(x_234);
 lean::dec(x_229);
 x_236 = lean::box(0);
}
x_237 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(x_218, x_232);
lean::dec(x_218);
if (lean::is_scalar(x_236)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_236;
}
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set(x_239, 1, x_234);
if (lean::is_scalar(x_231)) {
 x_240 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_240 = x_231;
}
lean::cnstr_set(x_240, 0, x_239);
return x_240;
}
}
}
}
case 2:
{
lean::dec(x_39);
lean::dec(x_140);
if (lean::obj_tag(x_23) == 0)
{
obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
x_246 = l_Lean_Elaborator_toLevel___main___closed__3;
if (lean::is_scalar(x_43)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_43;
}
lean::cnstr_set(x_247, 0, x_246);
lean::cnstr_set(x_247, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_248 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_248 = x_38;
}
lean::cnstr_set(x_248, 0, x_247);
return x_248;
}
else
{
obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_43);
if (lean::is_scalar(x_64)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_64;
}
lean::cnstr_set(x_252, 0, x_0);
x_253 = l_Lean_Elaborator_toLevel___main___closed__2;
x_254 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_252, x_253, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_252);
return x_254;
}
}
case 3:
{
obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_262 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_262 = x_64;
}
lean::cnstr_set(x_262, 0, x_0);
x_263 = l_Lean_Elaborator_toLevel___main___closed__2;
x_264 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_262, x_263, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_262);
return x_264;
}
case 4:
{
lean::dec(x_39);
if (lean::obj_tag(x_23) == 0)
{
obj* x_271; obj* x_274; obj* x_275; obj* x_277; obj* x_278; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
x_271 = lean::cnstr_get(x_140, 0);
lean::inc(x_271);
lean::dec(x_140);
x_274 = l_Lean_Parser_number_View_toNat___main(x_271);
x_275 = l_Lean_Level_ofNat___main(x_274);
lean::dec(x_274);
if (lean::is_scalar(x_43)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_43;
}
lean::cnstr_set(x_277, 0, x_275);
lean::cnstr_set(x_277, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_278 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_278 = x_38;
}
lean::cnstr_set(x_278, 0, x_277);
return x_278;
}
else
{
obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_283 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_283 = x_64;
}
lean::cnstr_set(x_283, 0, x_0);
x_284 = l_Lean_Elaborator_toLevel___main___closed__2;
x_285 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_283, x_284, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_283);
return x_285;
}
}
default:
{
if (lean::obj_tag(x_23) == 0)
{
obj* x_288; obj* x_291; obj* x_292; obj* x_295; obj* x_297; 
x_288 = lean::cnstr_get(x_140, 0);
lean::inc(x_288);
lean::dec(x_140);
x_291 = l_Lean_Elaborator_mangleIdent(x_288);
x_292 = lean::cnstr_get(x_39, 3);
lean::inc(x_292);
lean::dec(x_39);
x_295 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
lean::inc(x_291);
x_297 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_295, x_292, x_291);
if (lean::obj_tag(x_297) == 0)
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_306; obj* x_307; obj* x_308; 
lean::dec(x_38);
lean::dec(x_43);
if (lean::is_scalar(x_64)) {
 x_300 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_300 = x_64;
}
lean::cnstr_set(x_300, 0, x_0);
x_301 = l_Lean_Name_toString___closed__1;
x_302 = l_Lean_Name_toStringWithSep___main(x_301, x_291);
x_303 = l_Lean_Elaborator_toLevel___main___closed__4;
x_304 = lean::string_append(x_303, x_302);
lean::dec(x_302);
x_306 = l_Char_HasRepr___closed__1;
x_307 = lean::string_append(x_304, x_306);
x_308 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_300, x_307, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_300);
return x_308;
}
else
{
obj* x_315; obj* x_316; obj* x_317; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_297);
x_315 = level_mk_param(x_291);
if (lean::is_scalar(x_43)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_43;
}
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_317 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_317 = x_38;
}
lean::cnstr_set(x_317, 0, x_316);
return x_317;
}
}
else
{
obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_323 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_323 = x_64;
}
lean::cnstr_set(x_323, 0, x_0);
x_324 = l_Lean_Elaborator_toLevel___main___closed__2;
x_325 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_323, x_324, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_323);
return x_325;
}
}
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Elaborator_toLevel___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toLevel___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_toLevel(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toLevel___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_toLevel___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toLevel(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_Expr_mkAnnotation___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_Expr_mkAnnotation(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = l_Lean_Elaborator_Expr_mkAnnotation___closed__1;
x_4 = l_Lean_KVMap_setName(x_2, x_3, x_0);
x_5 = lean_expr_mk_mdata(x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Elaborator_dummy() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prop");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_2, x_3);
return x_4;
}
}
obj* _init_l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_18; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(x_0, x_6);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
lean::dec(x_11);
x_21 = 4;
lean::inc(x_13);
x_23 = lean_expr_local(x_13, x_13, x_0, x_21);
x_24 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_25 = l_Lean_Elaborator_Expr_mkAnnotation(x_24, x_23);
x_26 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_25, x_16);
x_27 = lean_expr_mk_app(x_26, x_18);
if (lean::is_scalar(x_8)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_8;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
return x_28;
}
}
}
obj* _init_l_Lean_Elaborator_mkEqns___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_mkEqns___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("preEquations");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_mkEqns(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(x_0, x_1);
x_3 = l_Lean_Elaborator_mkEqns___closed__1;
x_4 = l_Lean_Expr_mkCapp(x_3, x_2);
x_5 = l_Lean_Elaborator_mkEqns___closed__2;
x_6 = l_Lean_Elaborator_Expr_mkAnnotation(x_5, x_4);
return x_6;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_2);
x_17 = l_Lean_Elaborator_toPexpr___main(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_23 = x_17;
} else {
 lean::inc(x_21);
 lean::dec(x_17);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_12);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
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
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
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
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(x_4);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_matchFn");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::inc(x_2);
x_16 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_37; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
lean::dec(x_16);
x_28 = lean::cnstr_get(x_25, 0);
x_30 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 lean::cnstr_set(x_25, 1, lean::box(0));
 x_32 = x_25;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_25);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_8, 2);
lean::inc(x_33);
lean::dec(x_8);
lean::inc(x_2);
x_37 = l_Lean_Elaborator_toPexpr___main(x_33, x_1, x_2, x_30);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_32);
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_47 = lean::cnstr_get(x_37, 0);
lean::inc(x_47);
lean::dec(x_37);
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_28);
lean::cnstr_set(x_55, 1, x_50);
x_56 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1;
if (lean::is_scalar(x_32)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_32;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_55);
x_58 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_10, x_1, x_2, x_52);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_12);
lean::dec(x_57);
x_61 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_63 = x_58;
} else {
 lean::inc(x_61);
 lean::dec(x_58);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
return x_64;
}
else
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_65 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_67 = x_58;
} else {
 lean::inc(x_65);
 lean::dec(x_58);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_65, 0);
x_70 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_12;
}
lean::cnstr_set(x_73, 0, x_57);
lean::cnstr_set(x_73, 1, x_68);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_70);
if (lean::is_scalar(x_67)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_67;
}
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
}
}
}
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_List_reverse___rarg(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_6);
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_11 = x_0;
} else {
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_1);
x_0 = x_9;
x_1 = x_12;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_4);
x_16 = l_List_reverse___rarg(x_1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_0);
return x_17;
}
}
}
}
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_List_reverse___rarg(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
lean::dec(x_4);
x_10 = l_List_reverse___rarg(x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_4);
x_19 = l_List_reverse___rarg(x_1);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_0);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_15);
x_22 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_24 = x_0;
} else {
 lean::inc(x_22);
 lean::dec(x_0);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
x_0 = x_22;
x_1 = x_25;
goto _start;
}
}
}
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toPexpr: unreachable");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_Lean_Elaborator_toPexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = lean::cnstr_get(x_18, 0);
lean::inc(x_42);
lean::dec(x_18);
x_45 = l_Lean_Elaborator_mangleIdent(x_42);
x_46 = lean::box(0);
x_47 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_48 = l_Lean_KVMap_setName(x_46, x_47, x_45);
x_49 = lean_expr_mk_mdata(x_48, x_37);
x_50 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_17);
lean::dec(x_49);
x_53 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 0);
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_17;
}
lean::cnstr_set(x_65, 0, x_49);
lean::cnstr_set(x_65, 1, x_60);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_62);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_12);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
lean::inc(x_0);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_0);
x_74 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_76 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_73, x_74, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
lean::dec(x_71);
x_83 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_85 = x_76;
} else {
 lean::inc(x_83);
 lean::dec(x_76);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; 
x_87 = lean::cnstr_get(x_76, 0);
lean::inc(x_87);
lean::dec(x_76);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_69, x_2, x_3, x_92);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_71);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_104 = x_95;
} else {
 lean::inc(x_102);
 lean::dec(x_95);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_102, 0);
x_107 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 x_109 = x_102;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_71;
}
lean::cnstr_set(x_110, 0, x_90);
lean::cnstr_set(x_110, 1, x_105);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_104)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_104;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_73 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
return x_98;
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_Lean_Elaborator_toPexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_Lean_Elaborator_toPexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = lean::cnstr_get(x_18, 0);
lean::inc(x_42);
lean::dec(x_18);
x_45 = l_Lean_Elaborator_mangleIdent(x_42);
x_46 = lean::box(0);
x_47 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_48 = l_Lean_KVMap_setName(x_46, x_47, x_45);
x_49 = lean_expr_mk_mdata(x_48, x_37);
x_50 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_17);
lean::dec(x_49);
x_53 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 0);
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_17;
}
lean::cnstr_set(x_65, 0, x_49);
lean::cnstr_set(x_65, 1, x_60);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_62);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_12);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
lean::inc(x_0);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_0);
x_74 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_76 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_73, x_74, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
lean::dec(x_71);
x_83 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_85 = x_76;
} else {
 lean::inc(x_83);
 lean::dec(x_76);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; 
x_87 = lean::cnstr_get(x_76, 0);
lean::inc(x_87);
lean::dec(x_76);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_69, x_2, x_3, x_92);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_71);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_104 = x_95;
} else {
 lean::inc(x_102);
 lean::dec(x_95);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_102, 0);
x_107 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 x_109 = x_102;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_71;
}
lean::cnstr_set(x_110, 0, x_90);
lean::cnstr_set(x_110, 1, x_105);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_104)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_104;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_73 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
return x_98;
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_Lean_Elaborator_toPexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_Lean_Elaborator_toPexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = lean::cnstr_get(x_18, 0);
lean::inc(x_42);
lean::dec(x_18);
x_45 = l_Lean_Elaborator_mangleIdent(x_42);
x_46 = lean::box(0);
x_47 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_48 = l_Lean_KVMap_setName(x_46, x_47, x_45);
x_49 = lean_expr_mk_mdata(x_48, x_37);
x_50 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_17);
lean::dec(x_49);
x_53 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 0);
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_17;
}
lean::cnstr_set(x_65, 0, x_49);
lean::cnstr_set(x_65, 1, x_60);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_62);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_12);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
lean::inc(x_0);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_0);
x_74 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_76 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_73, x_74, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
lean::dec(x_71);
x_83 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_85 = x_76;
} else {
 lean::inc(x_83);
 lean::dec(x_76);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; 
x_87 = lean::cnstr_get(x_76, 0);
lean::inc(x_87);
lean::dec(x_76);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_69, x_2, x_3, x_92);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_71);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_104 = x_95;
} else {
 lean::inc(x_102);
 lean::dec(x_95);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_102, 0);
x_107 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 x_109 = x_102;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_71;
}
lean::cnstr_set(x_110, 0, x_90);
lean::cnstr_set(x_110, 1, x_105);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_104)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_104;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_73 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
return x_98;
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_Lean_Elaborator_toPexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; 
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::inc(x_3);
x_24 = l_Lean_Elaborator_toPexpr___main(x_21, x_2, x_3, x_4);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = lean::cnstr_get(x_18, 0);
lean::inc(x_42);
lean::dec(x_18);
x_45 = l_Lean_Elaborator_mangleIdent(x_42);
x_46 = lean::box(0);
x_47 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_48 = l_Lean_KVMap_setName(x_46, x_47, x_45);
x_49 = lean_expr_mk_mdata(x_48, x_37);
x_50 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_17);
lean::dec(x_49);
x_53 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_55 = x_50;
} else {
 lean::inc(x_53);
 lean::dec(x_50);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 0);
x_62 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_17;
}
lean::cnstr_set(x_65, 0, x_49);
lean::cnstr_set(x_65, 1, x_60);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_62);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_12);
x_69 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_71 = x_1;
} else {
 lean::inc(x_69);
 lean::dec(x_1);
 x_71 = lean::box(0);
}
lean::inc(x_0);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_0);
x_74 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_76 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_73, x_74, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
lean::dec(x_71);
x_83 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_85 = x_76;
} else {
 lean::inc(x_83);
 lean::dec(x_76);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; 
x_87 = lean::cnstr_get(x_76, 0);
lean::inc(x_87);
lean::dec(x_76);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_87, 1);
lean::inc(x_92);
lean::dec(x_87);
x_95 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_69, x_2, x_3, x_92);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_71);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_104 = x_95;
} else {
 lean::inc(x_102);
 lean::dec(x_95);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_102, 0);
x_107 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 x_109 = x_102;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_71;
}
lean::cnstr_set(x_110, 0, x_90);
lean::cnstr_set(x_110, 1, x_105);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_104)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_104;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
lean::inc(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_0);
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_20, x_21, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_23, 0);
lean::inc(x_34);
lean::dec(x_23);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_16, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_37);
lean::dec(x_18);
x_45 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_45);
 lean::dec(x_42);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_52);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_12, 0);
lean::inc(x_60);
lean::dec(x_12);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_66 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_68 = x_1;
} else {
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_73 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_70, x_71, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_68);
lean::dec(x_66);
x_80 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_82 = x_73;
} else {
 lean::inc(x_80);
 lean::dec(x_73);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
lean::dec(x_84);
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_66, x_2, x_3, x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_68);
lean::dec(x_87);
x_95 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
return x_98;
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_101 = x_92;
} else {
 lean::inc(x_99);
 lean::dec(x_92);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
x_104 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_107 = x_68;
}
lean::cnstr_set(x_107, 0, x_87);
lean::cnstr_set(x_107, 1, x_102);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_117; 
x_110 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_112 = x_1;
} else {
 lean::inc(x_110);
 lean::dec(x_1);
 x_112 = lean::box(0);
}
x_113 = lean::cnstr_get(x_63, 0);
lean::inc(x_113);
lean::dec(x_63);
lean::inc(x_3);
x_117 = l_Lean_Elaborator_toPexpr___main(x_113, x_2, x_3, x_4);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_110);
lean::dec(x_112);
x_122 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_134; 
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
lean::dec(x_117);
x_129 = lean::cnstr_get(x_126, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 1);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_110, x_2, x_3, x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_112);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_139 = x_134;
} else {
 lean::inc(x_137);
 lean::dec(x_134);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
return x_140;
}
else
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_141 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_143 = x_134;
} else {
 lean::inc(x_141);
 lean::dec(x_134);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
if (lean::is_exclusive(x_141)) {
 x_148 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_141);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_112;
}
lean::cnstr_set(x_149, 0, x_129);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_143)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_143;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_Lean_Elaborator_toPexpr___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::box(0);
x_13 = lean_name_mk_numeral(x_12, x_7);
x_14 = l_Lean_KVMap_setName(x_0, x_13, x_9);
x_0 = x_14;
x_1 = x_4;
goto _start;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_Lean_Elaborator_toLevel___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toPexpr: unexpected: ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("app");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("column");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("row");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("identUnivs");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("lambda");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("pi");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("sortApp");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("anonymousConstructor");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("hole");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("have");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("show");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("let");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("projection");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("explicit");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inaccessible");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("borrowed");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("choice");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__19() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structInst");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__20() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("Term");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("match");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__21() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toPexpr: unexpected Node: ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__22() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__23() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure instance");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__24() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("catchall");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__25() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_expr_mk_sort(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("struct");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__27() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__28() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__29() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__30() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("NOTAString");
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__31() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrowed");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("fieldNotation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__35() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__36() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__37() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean_expr_mk_bvar(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__38() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__39() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_dummy;
x_2 = lean_expr_mk_mvar(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymousConstructor");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__43() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed pi");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__44() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed lambda");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__45() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("annotation");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("preresolved");
x_5 = lean_name_mk_string(x_1, x_4);
x_6 = l_Lean_KVMap_setName(x_0, x_3, x_5);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__46() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("annotation");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("preresolved");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* l_Lean_Elaborator_toPexpr___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; uint8 x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_17 = l_Lean_Elaborator_toPexpr___main___closed__5;
x_18 = lean_name_dec_eq(x_8, x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_20 = lean_name_dec_eq(x_8, x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = l_Lean_Elaborator_toPexpr___main___closed__6;
x_22 = lean_name_dec_eq(x_8, x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = l_Lean_Elaborator_toPexpr___main___closed__7;
x_24 = lean_name_dec_eq(x_8, x_23);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = l_Lean_Parser_Term_sort_HasView_x_27___lambda__1___closed__4;
x_26 = lean_name_dec_eq(x_8, x_25);
if (x_26 == 0)
{
obj* x_27; uint8 x_28; 
x_27 = l_Lean_Elaborator_toPexpr___main___closed__8;
x_28 = lean_name_dec_eq(x_8, x_27);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = l_Lean_Elaborator_toPexpr___main___closed__9;
x_30 = lean_name_dec_eq(x_8, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = l_Lean_Elaborator_toPexpr___main___closed__10;
x_32 = lean_name_dec_eq(x_8, x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = l_Lean_Elaborator_toPexpr___main___closed__11;
x_34 = lean_name_dec_eq(x_8, x_33);
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
x_35 = l_Lean_Elaborator_toPexpr___main___closed__12;
x_36 = lean_name_dec_eq(x_8, x_35);
if (x_36 == 0)
{
obj* x_37; uint8 x_38; 
x_37 = l_Lean_Elaborator_toPexpr___main___closed__13;
x_38 = lean_name_dec_eq(x_8, x_37);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
x_39 = l_Lean_Elaborator_toPexpr___main___closed__14;
x_40 = lean_name_dec_eq(x_8, x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_Lean_Elaborator_toPexpr___main___closed__15;
x_42 = lean_name_dec_eq(x_8, x_41);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = l_Lean_Elaborator_toPexpr___main___closed__16;
x_44 = lean_name_dec_eq(x_8, x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_Lean_Elaborator_toPexpr___main___closed__17;
x_46 = lean_name_dec_eq(x_8, x_45);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
x_48 = lean_name_dec_eq(x_8, x_47);
if (x_48 == 0)
{
obj* x_49; uint8 x_50; 
x_49 = l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
x_50 = lean_name_dec_eq(x_8, x_49);
if (x_50 == 0)
{
obj* x_51; uint8 x_52; 
x_51 = l_Lean_Elaborator_toPexpr___main___closed__18;
x_52 = lean_name_dec_eq(x_8, x_51);
if (x_52 == 0)
{
obj* x_54; uint8 x_55; 
lean::dec(x_10);
x_54 = l_Lean_Elaborator_toPexpr___main___closed__19;
x_55 = lean_name_dec_eq(x_8, x_54);
if (x_55 == 0)
{
obj* x_56; uint8 x_57; 
x_56 = l_Lean_Elaborator_toPexpr___main___closed__20;
x_57 = lean_name_dec_eq(x_8, x_56);
if (x_57 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_66; 
lean::inc(x_0);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_0);
x_60 = l_Lean_Name_toString___closed__1;
x_61 = l_Lean_Name_toStringWithSep___main(x_60, x_8);
x_62 = l_Lean_Elaborator_toPexpr___main___closed__21;
x_63 = lean::string_append(x_62, x_61);
lean::dec(x_61);
lean::inc(x_2);
x_66 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_59, x_63, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_59);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_0);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_73 = x_66;
} else {
 lean::inc(x_71);
 lean::dec(x_66);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
return x_74;
}
else
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
x_80 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; obj* x_87; 
lean::dec(x_2);
if (lean::is_scalar(x_82)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_82;
}
lean::cnstr_set(x_86, 0, x_78);
lean::cnstr_set(x_86, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_77;
}
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_94; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_88 = lean::cnstr_get(x_83, 0);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::cnstr_get(x_2, 0);
lean::inc(x_91);
lean::dec(x_2);
x_94 = lean::cnstr_get(x_91, 2);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_Lean_FileMap_toPosition(x_94, x_88);
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
x_100 = lean::box(0);
x_101 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_102 = l_Lean_KVMap_setNat(x_100, x_101, x_98);
x_103 = lean::cnstr_get(x_97, 0);
lean::inc(x_103);
lean::dec(x_97);
x_106 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_107 = l_Lean_KVMap_setNat(x_102, x_106, x_103);
x_108 = lean_expr_mk_mdata(x_107, x_78);
if (lean::is_scalar(x_82)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_82;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_80);
if (lean::is_scalar(x_77)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_77;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
obj* x_111; obj* x_112; obj* x_116; obj* x_117; obj* x_119; obj* x_121; 
x_111 = l_Lean_Parser_Term_match_HasView;
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
lean::dec(x_111);
lean::inc(x_0);
x_116 = lean::apply_1(x_112, x_0);
x_117 = lean::cnstr_get(x_116, 5);
lean::inc(x_117);
x_119 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(x_117);
lean::inc(x_2);
x_121 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_119, x_1, x_2, x_3);
if (lean::obj_tag(x_121) == 0)
{
obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_116);
x_123 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_125 = x_121;
} else {
 lean::inc(x_123);
 lean::dec(x_121);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
x_13 = x_126;
goto lbl_14;
}
else
{
obj* x_127; obj* x_130; obj* x_132; obj* x_135; obj* x_137; obj* x_140; 
x_127 = lean::cnstr_get(x_121, 0);
lean::inc(x_127);
lean::dec(x_121);
x_130 = lean::cnstr_get(x_127, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_127, 1);
lean::inc(x_132);
lean::dec(x_127);
x_135 = lean::cnstr_get(x_116, 2);
lean::inc(x_135);
x_137 = l_Lean_Expander_getOptType___main(x_135);
lean::dec(x_135);
lean::inc(x_2);
x_140 = l_Lean_Elaborator_toPexpr___main(x_137, x_1, x_2, x_132);
if (lean::obj_tag(x_140) == 0)
{
obj* x_143; obj* x_145; obj* x_146; 
lean::dec(x_116);
lean::dec(x_130);
x_143 = lean::cnstr_get(x_140, 0);
if (lean::is_exclusive(x_140)) {
 x_145 = x_140;
} else {
 lean::inc(x_143);
 lean::dec(x_140);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
x_13 = x_146;
goto lbl_14;
}
else
{
obj* x_147; obj* x_150; obj* x_152; obj* x_155; 
x_147 = lean::cnstr_get(x_140, 0);
lean::inc(x_147);
lean::dec(x_140);
x_150 = lean::cnstr_get(x_147, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_147, 1);
lean::inc(x_152);
lean::dec(x_147);
x_155 = l_Lean_Elaborator_mkEqns(x_150, x_130);
switch (lean::obj_tag(x_155)) {
case 10:
{
obj* x_156; obj* x_158; obj* x_161; uint8 x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_169; 
x_156 = lean::cnstr_get(x_155, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_155, 1);
lean::inc(x_158);
lean::dec(x_155);
x_161 = l_Lean_Elaborator_toPexpr___main___closed__22;
x_162 = 1;
x_163 = l_Lean_KVMap_setBool(x_156, x_161, x_162);
x_164 = lean_expr_mk_mdata(x_163, x_158);
x_165 = lean::cnstr_get(x_116, 1);
lean::inc(x_165);
lean::dec(x_116);
lean::inc(x_2);
x_169 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_165, x_1, x_2, x_152);
if (lean::obj_tag(x_169) == 0)
{
obj* x_171; obj* x_173; obj* x_174; 
lean::dec(x_164);
x_171 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_173 = x_169;
} else {
 lean::inc(x_171);
 lean::dec(x_169);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
x_13 = x_174;
goto lbl_14;
}
else
{
obj* x_175; obj* x_177; obj* x_178; obj* x_180; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_175 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_177 = x_169;
} else {
 lean::inc(x_175);
 lean::dec(x_169);
 x_177 = lean::box(0);
}
x_178 = lean::cnstr_get(x_175, 0);
x_180 = lean::cnstr_get(x_175, 1);
if (lean::is_exclusive(x_175)) {
 x_182 = x_175;
} else {
 lean::inc(x_178);
 lean::inc(x_180);
 lean::dec(x_175);
 x_182 = lean::box(0);
}
x_183 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_164, x_178);
if (lean::is_scalar(x_182)) {
 x_184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_184 = x_182;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_180);
if (lean::is_scalar(x_177)) {
 x_185 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_185 = x_177;
}
lean::cnstr_set(x_185, 0, x_184);
x_13 = x_185;
goto lbl_14;
}
}
default:
{
obj* x_189; obj* x_190; obj* x_192; 
lean::dec(x_155);
lean::dec(x_116);
lean::inc(x_0);
x_189 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_189, 0, x_0);
x_190 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_2);
x_192 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_189, x_190, x_1, x_2, x_152);
lean::dec(x_152);
lean::dec(x_189);
x_13 = x_192;
goto lbl_14;
}
}
}
}
}
}
else
{
obj* x_195; obj* x_196; obj* x_200; obj* x_201; obj* x_203; obj* x_204; obj* x_205; obj* x_207; obj* x_210; obj* x_211; 
x_195 = l_Lean_Parser_Term_structInst_HasView;
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
lean::dec(x_195);
lean::inc(x_0);
x_200 = lean::apply_1(x_196, x_0);
x_201 = lean::cnstr_get(x_200, 3);
lean::inc(x_201);
x_203 = lean::box(0);
x_204 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_201, x_203);
x_205 = lean::cnstr_get(x_204, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_204, 1);
lean::inc(x_207);
lean::dec(x_204);
x_210 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_207, x_203);
x_211 = lean::cnstr_get(x_210, 1);
lean::inc(x_211);
if (lean::obj_tag(x_211) == 0)
{
obj* x_213; obj* x_218; 
x_213 = lean::cnstr_get(x_210, 0);
lean::inc(x_213);
lean::dec(x_210);
lean::inc(x_2);
lean::inc(x_0);
x_218 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_205, x_1, x_2, x_3);
if (lean::obj_tag(x_218) == 0)
{
obj* x_224; obj* x_226; obj* x_227; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_213);
lean::dec(x_200);
x_224 = lean::cnstr_get(x_218, 0);
if (lean::is_exclusive(x_218)) {
 x_226 = x_218;
} else {
 lean::inc(x_224);
 lean::dec(x_218);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_224);
return x_227;
}
else
{
obj* x_228; obj* x_231; obj* x_233; obj* x_236; obj* x_240; 
x_228 = lean::cnstr_get(x_218, 0);
lean::inc(x_228);
lean::dec(x_218);
x_231 = lean::cnstr_get(x_228, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_228, 1);
lean::inc(x_233);
lean::dec(x_228);
lean::inc(x_2);
lean::inc(x_0);
x_240 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_213, x_1, x_2, x_233);
if (lean::obj_tag(x_240) == 0)
{
obj* x_246; obj* x_248; obj* x_249; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_231);
lean::dec(x_200);
x_246 = lean::cnstr_get(x_240, 0);
if (lean::is_exclusive(x_240)) {
 x_248 = x_240;
} else {
 lean::inc(x_246);
 lean::dec(x_240);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_246);
return x_249;
}
else
{
obj* x_250; obj* x_253; 
x_250 = lean::cnstr_get(x_240, 0);
lean::inc(x_250);
lean::dec(x_240);
x_253 = lean::cnstr_get(x_200, 2);
lean::inc(x_253);
if (lean::obj_tag(x_253) == 0)
{
obj* x_255; obj* x_257; obj* x_259; obj* x_260; 
x_255 = lean::cnstr_get(x_250, 0);
x_257 = lean::cnstr_get(x_250, 1);
if (lean::is_exclusive(x_250)) {
 x_259 = x_250;
} else {
 lean::inc(x_255);
 lean::inc(x_257);
 lean::dec(x_250);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_255);
lean::cnstr_set(x_260, 1, x_257);
x_236 = x_260;
goto lbl_237;
}
else
{
obj* x_261; obj* x_263; obj* x_266; obj* x_269; obj* x_273; 
x_261 = lean::cnstr_get(x_250, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_250, 1);
lean::inc(x_263);
lean::dec(x_250);
x_266 = lean::cnstr_get(x_253, 0);
lean::inc(x_266);
lean::dec(x_253);
x_269 = lean::cnstr_get(x_266, 0);
lean::inc(x_269);
lean::dec(x_266);
lean::inc(x_2);
x_273 = l_Lean_Elaborator_toPexpr___main(x_269, x_1, x_2, x_263);
if (lean::obj_tag(x_273) == 0)
{
obj* x_280; obj* x_282; obj* x_283; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_231);
lean::dec(x_261);
lean::dec(x_200);
x_280 = lean::cnstr_get(x_273, 0);
if (lean::is_exclusive(x_273)) {
 x_282 = x_273;
} else {
 lean::inc(x_280);
 lean::dec(x_273);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
return x_283;
}
else
{
obj* x_284; obj* x_287; obj* x_289; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
x_284 = lean::cnstr_get(x_273, 0);
lean::inc(x_284);
lean::dec(x_273);
x_287 = lean::cnstr_get(x_284, 0);
x_289 = lean::cnstr_get(x_284, 1);
if (lean::is_exclusive(x_284)) {
 x_291 = x_284;
} else {
 lean::inc(x_287);
 lean::inc(x_289);
 lean::dec(x_284);
 x_291 = lean::box(0);
}
x_292 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_292, 0, x_287);
lean::cnstr_set(x_292, 1, x_203);
x_293 = l_List_append___rarg(x_261, x_292);
if (lean::is_scalar(x_291)) {
 x_294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_294 = x_291;
}
lean::cnstr_set(x_294, 0, x_293);
lean::cnstr_set(x_294, 1, x_289);
x_236 = x_294;
goto lbl_237;
}
}
}
lbl_237:
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; uint8 x_305; obj* x_306; obj* x_307; obj* x_310; obj* x_311; obj* x_312; 
x_295 = lean::cnstr_get(x_236, 0);
x_297 = lean::cnstr_get(x_236, 1);
if (lean::is_exclusive(x_236)) {
 lean::cnstr_set(x_236, 0, lean::box(0));
 lean::cnstr_set(x_236, 1, lean::box(0));
 x_299 = x_236;
} else {
 lean::inc(x_295);
 lean::inc(x_297);
 lean::dec(x_236);
 x_299 = lean::box(0);
}
x_300 = lean::mk_nat_obj(0ul);
x_301 = l_List_lengthAux___main___rarg(x_231, x_300);
x_302 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_303 = l_Lean_KVMap_setNat(x_203, x_302, x_301);
x_304 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_305 = 0;
x_306 = l_Lean_KVMap_setBool(x_303, x_304, x_305);
x_307 = lean::cnstr_get(x_200, 1);
lean::inc(x_307);
lean::dec(x_200);
x_310 = l_List_append___rarg(x_231, x_295);
x_311 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_312 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_311, x_310);
if (lean::obj_tag(x_307) == 0)
{
obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_313 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_314 = lean::box(0);
x_315 = l_Lean_KVMap_setName(x_306, x_313, x_314);
x_316 = lean_expr_mk_mdata(x_315, x_312);
if (lean::is_scalar(x_299)) {
 x_317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_317 = x_299;
}
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_297);
x_15 = x_317;
goto lbl_16;
}
else
{
obj* x_318; obj* x_321; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
x_318 = lean::cnstr_get(x_307, 0);
lean::inc(x_318);
lean::dec(x_307);
x_321 = lean::cnstr_get(x_318, 0);
lean::inc(x_321);
lean::dec(x_318);
x_324 = l_Lean_Elaborator_mangleIdent(x_321);
x_325 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_326 = l_Lean_KVMap_setName(x_306, x_325, x_324);
x_327 = lean_expr_mk_mdata(x_326, x_312);
if (lean::is_scalar(x_299)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_299;
}
lean::cnstr_set(x_328, 0, x_327);
lean::cnstr_set(x_328, 1, x_297);
x_15 = x_328;
goto lbl_16;
}
}
}
}
else
{
obj* x_329; obj* x_331; 
x_329 = lean::cnstr_get(x_211, 0);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_329, 0);
lean::inc(x_331);
lean::dec(x_329);
if (lean::obj_tag(x_331) == 0)
{
obj* x_334; obj* x_335; obj* x_338; obj* x_339; obj* x_342; obj* x_343; obj* x_344; obj* x_346; 
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 lean::cnstr_release(x_211, 1);
 x_334 = x_211;
} else {
 lean::dec(x_211);
 x_334 = lean::box(0);
}
x_335 = lean::cnstr_get(x_210, 0);
lean::inc(x_335);
lean::dec(x_210);
x_338 = l_Lean_Parser_Term_structInstItem_HasView;
x_339 = lean::cnstr_get(x_338, 1);
lean::inc(x_339);
lean::dec(x_338);
x_342 = lean::apply_1(x_339, x_331);
x_343 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_343, 0, x_342);
x_344 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_346 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_343, x_344, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_343);
if (lean::obj_tag(x_346) == 0)
{
obj* x_356; obj* x_358; obj* x_359; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_334);
lean::dec(x_335);
lean::dec(x_205);
lean::dec(x_200);
x_356 = lean::cnstr_get(x_346, 0);
if (lean::is_exclusive(x_346)) {
 x_358 = x_346;
} else {
 lean::inc(x_356);
 lean::dec(x_346);
 x_358 = lean::box(0);
}
if (lean::is_scalar(x_358)) {
 x_359 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_359 = x_358;
}
lean::cnstr_set(x_359, 0, x_356);
return x_359;
}
else
{
obj* x_360; obj* x_363; obj* x_365; obj* x_370; 
x_360 = lean::cnstr_get(x_346, 0);
lean::inc(x_360);
lean::dec(x_346);
x_363 = lean::cnstr_get(x_360, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_360, 1);
lean::inc(x_365);
lean::dec(x_360);
lean::inc(x_2);
lean::inc(x_0);
x_370 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_205, x_1, x_2, x_365);
if (lean::obj_tag(x_370) == 0)
{
obj* x_378; obj* x_380; obj* x_381; 
lean::dec(x_363);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_334);
lean::dec(x_335);
lean::dec(x_200);
x_378 = lean::cnstr_get(x_370, 0);
if (lean::is_exclusive(x_370)) {
 x_380 = x_370;
} else {
 lean::inc(x_378);
 lean::dec(x_370);
 x_380 = lean::box(0);
}
if (lean::is_scalar(x_380)) {
 x_381 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_381 = x_380;
}
lean::cnstr_set(x_381, 0, x_378);
return x_381;
}
else
{
obj* x_382; obj* x_385; obj* x_387; obj* x_390; obj* x_394; 
x_382 = lean::cnstr_get(x_370, 0);
lean::inc(x_382);
lean::dec(x_370);
x_385 = lean::cnstr_get(x_382, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_382, 1);
lean::inc(x_387);
lean::dec(x_382);
lean::inc(x_2);
lean::inc(x_0);
x_394 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_335, x_1, x_2, x_387);
if (lean::obj_tag(x_394) == 0)
{
obj* x_402; obj* x_404; obj* x_405; 
lean::dec(x_363);
lean::dec(x_8);
lean::dec(x_385);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_334);
lean::dec(x_200);
x_402 = lean::cnstr_get(x_394, 0);
if (lean::is_exclusive(x_394)) {
 x_404 = x_394;
} else {
 lean::inc(x_402);
 lean::dec(x_394);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_402);
return x_405;
}
else
{
obj* x_406; obj* x_409; 
x_406 = lean::cnstr_get(x_394, 0);
lean::inc(x_406);
lean::dec(x_394);
x_409 = lean::cnstr_get(x_200, 2);
lean::inc(x_409);
if (lean::obj_tag(x_409) == 0)
{
obj* x_412; obj* x_414; obj* x_416; obj* x_417; 
lean::dec(x_334);
x_412 = lean::cnstr_get(x_406, 0);
x_414 = lean::cnstr_get(x_406, 1);
if (lean::is_exclusive(x_406)) {
 x_416 = x_406;
} else {
 lean::inc(x_412);
 lean::inc(x_414);
 lean::dec(x_406);
 x_416 = lean::box(0);
}
if (lean::is_scalar(x_416)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_416;
}
lean::cnstr_set(x_417, 0, x_412);
lean::cnstr_set(x_417, 1, x_414);
x_390 = x_417;
goto lbl_391;
}
else
{
obj* x_418; obj* x_420; obj* x_423; obj* x_426; obj* x_430; 
x_418 = lean::cnstr_get(x_406, 0);
lean::inc(x_418);
x_420 = lean::cnstr_get(x_406, 1);
lean::inc(x_420);
lean::dec(x_406);
x_423 = lean::cnstr_get(x_409, 0);
lean::inc(x_423);
lean::dec(x_409);
x_426 = lean::cnstr_get(x_423, 0);
lean::inc(x_426);
lean::dec(x_423);
lean::inc(x_2);
x_430 = l_Lean_Elaborator_toPexpr___main(x_426, x_1, x_2, x_420);
if (lean::obj_tag(x_430) == 0)
{
obj* x_439; obj* x_441; obj* x_442; 
lean::dec(x_363);
lean::dec(x_8);
lean::dec(x_385);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_334);
lean::dec(x_418);
lean::dec(x_200);
x_439 = lean::cnstr_get(x_430, 0);
if (lean::is_exclusive(x_430)) {
 x_441 = x_430;
} else {
 lean::inc(x_439);
 lean::dec(x_430);
 x_441 = lean::box(0);
}
if (lean::is_scalar(x_441)) {
 x_442 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_442 = x_441;
}
lean::cnstr_set(x_442, 0, x_439);
return x_442;
}
else
{
obj* x_443; obj* x_446; obj* x_448; obj* x_450; obj* x_451; obj* x_452; obj* x_453; 
x_443 = lean::cnstr_get(x_430, 0);
lean::inc(x_443);
lean::dec(x_430);
x_446 = lean::cnstr_get(x_443, 0);
x_448 = lean::cnstr_get(x_443, 1);
if (lean::is_exclusive(x_443)) {
 x_450 = x_443;
} else {
 lean::inc(x_446);
 lean::inc(x_448);
 lean::dec(x_443);
 x_450 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_451 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_451 = x_334;
}
lean::cnstr_set(x_451, 0, x_446);
lean::cnstr_set(x_451, 1, x_203);
x_452 = l_List_append___rarg(x_418, x_451);
if (lean::is_scalar(x_450)) {
 x_453 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_453 = x_450;
}
lean::cnstr_set(x_453, 0, x_452);
lean::cnstr_set(x_453, 1, x_448);
x_390 = x_453;
goto lbl_391;
}
}
}
lbl_391:
{
obj* x_454; obj* x_456; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; uint8 x_464; obj* x_465; obj* x_466; obj* x_469; obj* x_470; obj* x_471; 
x_454 = lean::cnstr_get(x_390, 0);
x_456 = lean::cnstr_get(x_390, 1);
if (lean::is_exclusive(x_390)) {
 lean::cnstr_set(x_390, 0, lean::box(0));
 lean::cnstr_set(x_390, 1, lean::box(0));
 x_458 = x_390;
} else {
 lean::inc(x_454);
 lean::inc(x_456);
 lean::dec(x_390);
 x_458 = lean::box(0);
}
x_459 = lean::mk_nat_obj(0ul);
x_460 = l_List_lengthAux___main___rarg(x_385, x_459);
x_461 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_462 = l_Lean_KVMap_setNat(x_203, x_461, x_460);
x_463 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_464 = lean::unbox(x_363);
x_465 = l_Lean_KVMap_setBool(x_462, x_463, x_464);
x_466 = lean::cnstr_get(x_200, 1);
lean::inc(x_466);
lean::dec(x_200);
x_469 = l_List_append___rarg(x_385, x_454);
x_470 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_471 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_470, x_469);
if (lean::obj_tag(x_466) == 0)
{
obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; 
x_472 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_473 = lean::box(0);
x_474 = l_Lean_KVMap_setName(x_465, x_472, x_473);
x_475 = lean_expr_mk_mdata(x_474, x_471);
if (lean::is_scalar(x_458)) {
 x_476 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_476 = x_458;
}
lean::cnstr_set(x_476, 0, x_475);
lean::cnstr_set(x_476, 1, x_456);
x_15 = x_476;
goto lbl_16;
}
else
{
obj* x_477; obj* x_480; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_477 = lean::cnstr_get(x_466, 0);
lean::inc(x_477);
lean::dec(x_466);
x_480 = lean::cnstr_get(x_477, 0);
lean::inc(x_480);
lean::dec(x_477);
x_483 = l_Lean_Elaborator_mangleIdent(x_480);
x_484 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_485 = l_Lean_KVMap_setName(x_465, x_484, x_483);
x_486 = lean_expr_mk_mdata(x_485, x_471);
if (lean::is_scalar(x_458)) {
 x_487 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_487 = x_458;
}
lean::cnstr_set(x_487, 0, x_486);
lean::cnstr_set(x_487, 1, x_456);
x_15 = x_487;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_488; obj* x_490; 
x_488 = lean::cnstr_get(x_211, 1);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 lean::cnstr_set(x_211, 1, lean::box(0));
 x_490 = x_211;
} else {
 lean::inc(x_488);
 lean::dec(x_211);
 x_490 = lean::box(0);
}
if (lean::obj_tag(x_488) == 0)
{
obj* x_492; obj* x_497; 
lean::dec(x_331);
x_492 = lean::cnstr_get(x_210, 0);
lean::inc(x_492);
lean::dec(x_210);
lean::inc(x_2);
lean::inc(x_0);
x_497 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_205, x_1, x_2, x_3);
if (lean::obj_tag(x_497) == 0)
{
obj* x_504; obj* x_506; obj* x_507; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_492);
lean::dec(x_490);
lean::dec(x_200);
x_504 = lean::cnstr_get(x_497, 0);
if (lean::is_exclusive(x_497)) {
 x_506 = x_497;
} else {
 lean::inc(x_504);
 lean::dec(x_497);
 x_506 = lean::box(0);
}
if (lean::is_scalar(x_506)) {
 x_507 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_507 = x_506;
}
lean::cnstr_set(x_507, 0, x_504);
return x_507;
}
else
{
obj* x_508; obj* x_511; obj* x_513; obj* x_516; obj* x_520; 
x_508 = lean::cnstr_get(x_497, 0);
lean::inc(x_508);
lean::dec(x_497);
x_511 = lean::cnstr_get(x_508, 0);
lean::inc(x_511);
x_513 = lean::cnstr_get(x_508, 1);
lean::inc(x_513);
lean::dec(x_508);
lean::inc(x_2);
lean::inc(x_0);
x_520 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_492, x_1, x_2, x_513);
if (lean::obj_tag(x_520) == 0)
{
obj* x_527; obj* x_529; obj* x_530; 
lean::dec(x_511);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_490);
lean::dec(x_200);
x_527 = lean::cnstr_get(x_520, 0);
if (lean::is_exclusive(x_520)) {
 x_529 = x_520;
} else {
 lean::inc(x_527);
 lean::dec(x_520);
 x_529 = lean::box(0);
}
if (lean::is_scalar(x_529)) {
 x_530 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_530 = x_529;
}
lean::cnstr_set(x_530, 0, x_527);
return x_530;
}
else
{
obj* x_531; obj* x_534; 
x_531 = lean::cnstr_get(x_520, 0);
lean::inc(x_531);
lean::dec(x_520);
x_534 = lean::cnstr_get(x_200, 2);
lean::inc(x_534);
if (lean::obj_tag(x_534) == 0)
{
obj* x_537; obj* x_539; obj* x_541; obj* x_542; 
lean::dec(x_490);
x_537 = lean::cnstr_get(x_531, 0);
x_539 = lean::cnstr_get(x_531, 1);
if (lean::is_exclusive(x_531)) {
 x_541 = x_531;
} else {
 lean::inc(x_537);
 lean::inc(x_539);
 lean::dec(x_531);
 x_541 = lean::box(0);
}
if (lean::is_scalar(x_541)) {
 x_542 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_542 = x_541;
}
lean::cnstr_set(x_542, 0, x_537);
lean::cnstr_set(x_542, 1, x_539);
x_516 = x_542;
goto lbl_517;
}
else
{
obj* x_543; obj* x_545; obj* x_548; obj* x_551; obj* x_555; 
x_543 = lean::cnstr_get(x_531, 0);
lean::inc(x_543);
x_545 = lean::cnstr_get(x_531, 1);
lean::inc(x_545);
lean::dec(x_531);
x_548 = lean::cnstr_get(x_534, 0);
lean::inc(x_548);
lean::dec(x_534);
x_551 = lean::cnstr_get(x_548, 0);
lean::inc(x_551);
lean::dec(x_548);
lean::inc(x_2);
x_555 = l_Lean_Elaborator_toPexpr___main(x_551, x_1, x_2, x_545);
if (lean::obj_tag(x_555) == 0)
{
obj* x_563; obj* x_565; obj* x_566; 
lean::dec(x_511);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_490);
lean::dec(x_543);
lean::dec(x_200);
x_563 = lean::cnstr_get(x_555, 0);
if (lean::is_exclusive(x_555)) {
 x_565 = x_555;
} else {
 lean::inc(x_563);
 lean::dec(x_555);
 x_565 = lean::box(0);
}
if (lean::is_scalar(x_565)) {
 x_566 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_566 = x_565;
}
lean::cnstr_set(x_566, 0, x_563);
return x_566;
}
else
{
obj* x_567; obj* x_570; obj* x_572; obj* x_574; obj* x_575; obj* x_576; obj* x_577; 
x_567 = lean::cnstr_get(x_555, 0);
lean::inc(x_567);
lean::dec(x_555);
x_570 = lean::cnstr_get(x_567, 0);
x_572 = lean::cnstr_get(x_567, 1);
if (lean::is_exclusive(x_567)) {
 x_574 = x_567;
} else {
 lean::inc(x_570);
 lean::inc(x_572);
 lean::dec(x_567);
 x_574 = lean::box(0);
}
if (lean::is_scalar(x_490)) {
 x_575 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_575 = x_490;
}
lean::cnstr_set(x_575, 0, x_570);
lean::cnstr_set(x_575, 1, x_203);
x_576 = l_List_append___rarg(x_543, x_575);
if (lean::is_scalar(x_574)) {
 x_577 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_577 = x_574;
}
lean::cnstr_set(x_577, 0, x_576);
lean::cnstr_set(x_577, 1, x_572);
x_516 = x_577;
goto lbl_517;
}
}
}
lbl_517:
{
obj* x_578; obj* x_580; obj* x_582; obj* x_583; obj* x_584; obj* x_585; obj* x_586; obj* x_587; uint8 x_588; obj* x_589; obj* x_590; obj* x_593; obj* x_594; obj* x_595; 
x_578 = lean::cnstr_get(x_516, 0);
x_580 = lean::cnstr_get(x_516, 1);
if (lean::is_exclusive(x_516)) {
 lean::cnstr_set(x_516, 0, lean::box(0));
 lean::cnstr_set(x_516, 1, lean::box(0));
 x_582 = x_516;
} else {
 lean::inc(x_578);
 lean::inc(x_580);
 lean::dec(x_516);
 x_582 = lean::box(0);
}
x_583 = lean::mk_nat_obj(0ul);
x_584 = l_List_lengthAux___main___rarg(x_511, x_583);
x_585 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_586 = l_Lean_KVMap_setNat(x_203, x_585, x_584);
x_587 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_588 = 1;
x_589 = l_Lean_KVMap_setBool(x_586, x_587, x_588);
x_590 = lean::cnstr_get(x_200, 1);
lean::inc(x_590);
lean::dec(x_200);
x_593 = l_List_append___rarg(x_511, x_578);
x_594 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_595 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_594, x_593);
if (lean::obj_tag(x_590) == 0)
{
obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
x_596 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_597 = lean::box(0);
x_598 = l_Lean_KVMap_setName(x_589, x_596, x_597);
x_599 = lean_expr_mk_mdata(x_598, x_595);
if (lean::is_scalar(x_582)) {
 x_600 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_600 = x_582;
}
lean::cnstr_set(x_600, 0, x_599);
lean::cnstr_set(x_600, 1, x_580);
x_15 = x_600;
goto lbl_16;
}
else
{
obj* x_601; obj* x_604; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; 
x_601 = lean::cnstr_get(x_590, 0);
lean::inc(x_601);
lean::dec(x_590);
x_604 = lean::cnstr_get(x_601, 0);
lean::inc(x_604);
lean::dec(x_601);
x_607 = l_Lean_Elaborator_mangleIdent(x_604);
x_608 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_609 = l_Lean_KVMap_setName(x_589, x_608, x_607);
x_610 = lean_expr_mk_mdata(x_609, x_595);
if (lean::is_scalar(x_582)) {
 x_611 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_611 = x_582;
}
lean::cnstr_set(x_611, 0, x_610);
lean::cnstr_set(x_611, 1, x_580);
x_15 = x_611;
goto lbl_16;
}
}
}
}
else
{
obj* x_613; obj* x_614; obj* x_617; obj* x_618; obj* x_621; obj* x_622; obj* x_623; obj* x_625; 
lean::dec(x_490);
if (lean::is_exclusive(x_488)) {
 lean::cnstr_release(x_488, 0);
 lean::cnstr_release(x_488, 1);
 x_613 = x_488;
} else {
 lean::dec(x_488);
 x_613 = lean::box(0);
}
x_614 = lean::cnstr_get(x_210, 0);
lean::inc(x_614);
lean::dec(x_210);
x_617 = l_Lean_Parser_Term_structInstItem_HasView;
x_618 = lean::cnstr_get(x_617, 1);
lean::inc(x_618);
lean::dec(x_617);
x_621 = lean::apply_1(x_618, x_331);
x_622 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_622, 0, x_621);
x_623 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_625 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_622, x_623, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_622);
if (lean::obj_tag(x_625) == 0)
{
obj* x_635; obj* x_637; obj* x_638; 
lean::dec(x_8);
lean::dec(x_613);
lean::dec(x_0);
lean::dec(x_614);
lean::dec(x_2);
lean::dec(x_205);
lean::dec(x_200);
x_635 = lean::cnstr_get(x_625, 0);
if (lean::is_exclusive(x_625)) {
 x_637 = x_625;
} else {
 lean::inc(x_635);
 lean::dec(x_625);
 x_637 = lean::box(0);
}
if (lean::is_scalar(x_637)) {
 x_638 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_638 = x_637;
}
lean::cnstr_set(x_638, 0, x_635);
return x_638;
}
else
{
obj* x_639; obj* x_642; obj* x_644; obj* x_649; 
x_639 = lean::cnstr_get(x_625, 0);
lean::inc(x_639);
lean::dec(x_625);
x_642 = lean::cnstr_get(x_639, 0);
lean::inc(x_642);
x_644 = lean::cnstr_get(x_639, 1);
lean::inc(x_644);
lean::dec(x_639);
lean::inc(x_2);
lean::inc(x_0);
x_649 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_205, x_1, x_2, x_644);
if (lean::obj_tag(x_649) == 0)
{
obj* x_657; obj* x_659; obj* x_660; 
lean::dec(x_8);
lean::dec(x_613);
lean::dec(x_0);
lean::dec(x_614);
lean::dec(x_2);
lean::dec(x_642);
lean::dec(x_200);
x_657 = lean::cnstr_get(x_649, 0);
if (lean::is_exclusive(x_649)) {
 x_659 = x_649;
} else {
 lean::inc(x_657);
 lean::dec(x_649);
 x_659 = lean::box(0);
}
if (lean::is_scalar(x_659)) {
 x_660 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_660 = x_659;
}
lean::cnstr_set(x_660, 0, x_657);
return x_660;
}
else
{
obj* x_661; obj* x_664; obj* x_666; obj* x_669; obj* x_673; 
x_661 = lean::cnstr_get(x_649, 0);
lean::inc(x_661);
lean::dec(x_649);
x_664 = lean::cnstr_get(x_661, 0);
lean::inc(x_664);
x_666 = lean::cnstr_get(x_661, 1);
lean::inc(x_666);
lean::dec(x_661);
lean::inc(x_2);
lean::inc(x_0);
x_673 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_614, x_1, x_2, x_666);
if (lean::obj_tag(x_673) == 0)
{
obj* x_681; obj* x_683; obj* x_684; 
lean::dec(x_8);
lean::dec(x_613);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_642);
lean::dec(x_664);
lean::dec(x_200);
x_681 = lean::cnstr_get(x_673, 0);
if (lean::is_exclusive(x_673)) {
 x_683 = x_673;
} else {
 lean::inc(x_681);
 lean::dec(x_673);
 x_683 = lean::box(0);
}
if (lean::is_scalar(x_683)) {
 x_684 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_684 = x_683;
}
lean::cnstr_set(x_684, 0, x_681);
return x_684;
}
else
{
obj* x_685; obj* x_688; 
x_685 = lean::cnstr_get(x_673, 0);
lean::inc(x_685);
lean::dec(x_673);
x_688 = lean::cnstr_get(x_200, 2);
lean::inc(x_688);
if (lean::obj_tag(x_688) == 0)
{
obj* x_691; obj* x_693; obj* x_695; obj* x_696; 
lean::dec(x_613);
x_691 = lean::cnstr_get(x_685, 0);
x_693 = lean::cnstr_get(x_685, 1);
if (lean::is_exclusive(x_685)) {
 x_695 = x_685;
} else {
 lean::inc(x_691);
 lean::inc(x_693);
 lean::dec(x_685);
 x_695 = lean::box(0);
}
if (lean::is_scalar(x_695)) {
 x_696 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_696 = x_695;
}
lean::cnstr_set(x_696, 0, x_691);
lean::cnstr_set(x_696, 1, x_693);
x_669 = x_696;
goto lbl_670;
}
else
{
obj* x_697; obj* x_699; obj* x_702; obj* x_705; obj* x_709; 
x_697 = lean::cnstr_get(x_685, 0);
lean::inc(x_697);
x_699 = lean::cnstr_get(x_685, 1);
lean::inc(x_699);
lean::dec(x_685);
x_702 = lean::cnstr_get(x_688, 0);
lean::inc(x_702);
lean::dec(x_688);
x_705 = lean::cnstr_get(x_702, 0);
lean::inc(x_705);
lean::dec(x_702);
lean::inc(x_2);
x_709 = l_Lean_Elaborator_toPexpr___main(x_705, x_1, x_2, x_699);
if (lean::obj_tag(x_709) == 0)
{
obj* x_718; obj* x_720; obj* x_721; 
lean::dec(x_8);
lean::dec(x_613);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_642);
lean::dec(x_664);
lean::dec(x_697);
lean::dec(x_200);
x_718 = lean::cnstr_get(x_709, 0);
if (lean::is_exclusive(x_709)) {
 x_720 = x_709;
} else {
 lean::inc(x_718);
 lean::dec(x_709);
 x_720 = lean::box(0);
}
if (lean::is_scalar(x_720)) {
 x_721 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_721 = x_720;
}
lean::cnstr_set(x_721, 0, x_718);
return x_721;
}
else
{
obj* x_722; obj* x_725; obj* x_727; obj* x_729; obj* x_730; obj* x_731; obj* x_732; 
x_722 = lean::cnstr_get(x_709, 0);
lean::inc(x_722);
lean::dec(x_709);
x_725 = lean::cnstr_get(x_722, 0);
x_727 = lean::cnstr_get(x_722, 1);
if (lean::is_exclusive(x_722)) {
 x_729 = x_722;
} else {
 lean::inc(x_725);
 lean::inc(x_727);
 lean::dec(x_722);
 x_729 = lean::box(0);
}
if (lean::is_scalar(x_613)) {
 x_730 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_730 = x_613;
}
lean::cnstr_set(x_730, 0, x_725);
lean::cnstr_set(x_730, 1, x_203);
x_731 = l_List_append___rarg(x_697, x_730);
if (lean::is_scalar(x_729)) {
 x_732 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_732 = x_729;
}
lean::cnstr_set(x_732, 0, x_731);
lean::cnstr_set(x_732, 1, x_727);
x_669 = x_732;
goto lbl_670;
}
}
}
lbl_670:
{
obj* x_733; obj* x_735; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; uint8 x_743; obj* x_744; obj* x_745; obj* x_748; obj* x_749; obj* x_750; 
x_733 = lean::cnstr_get(x_669, 0);
x_735 = lean::cnstr_get(x_669, 1);
if (lean::is_exclusive(x_669)) {
 lean::cnstr_set(x_669, 0, lean::box(0));
 lean::cnstr_set(x_669, 1, lean::box(0));
 x_737 = x_669;
} else {
 lean::inc(x_733);
 lean::inc(x_735);
 lean::dec(x_669);
 x_737 = lean::box(0);
}
x_738 = lean::mk_nat_obj(0ul);
x_739 = l_List_lengthAux___main___rarg(x_664, x_738);
x_740 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_741 = l_Lean_KVMap_setNat(x_203, x_740, x_739);
x_742 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_743 = lean::unbox(x_642);
x_744 = l_Lean_KVMap_setBool(x_741, x_742, x_743);
x_745 = lean::cnstr_get(x_200, 1);
lean::inc(x_745);
lean::dec(x_200);
x_748 = l_List_append___rarg(x_664, x_733);
x_749 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_750 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_749, x_748);
if (lean::obj_tag(x_745) == 0)
{
obj* x_751; obj* x_752; obj* x_753; obj* x_754; obj* x_755; 
x_751 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_752 = lean::box(0);
x_753 = l_Lean_KVMap_setName(x_744, x_751, x_752);
x_754 = lean_expr_mk_mdata(x_753, x_750);
if (lean::is_scalar(x_737)) {
 x_755 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_755 = x_737;
}
lean::cnstr_set(x_755, 0, x_754);
lean::cnstr_set(x_755, 1, x_735);
x_15 = x_755;
goto lbl_16;
}
else
{
obj* x_756; obj* x_759; obj* x_762; obj* x_763; obj* x_764; obj* x_765; obj* x_766; 
x_756 = lean::cnstr_get(x_745, 0);
lean::inc(x_756);
lean::dec(x_745);
x_759 = lean::cnstr_get(x_756, 0);
lean::inc(x_759);
lean::dec(x_756);
x_762 = l_Lean_Elaborator_mangleIdent(x_759);
x_763 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_764 = l_Lean_KVMap_setName(x_744, x_763, x_762);
x_765 = lean_expr_mk_mdata(x_764, x_750);
if (lean::is_scalar(x_737)) {
 x_766 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_766 = x_737;
}
lean::cnstr_set(x_766, 0, x_765);
lean::cnstr_set(x_766, 1, x_735);
x_15 = x_766;
goto lbl_16;
}
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
obj* x_769; 
lean::inc(x_2);
lean::inc(x_10);
x_769 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_769) == 0)
{
obj* x_774; obj* x_776; obj* x_777; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_774 = lean::cnstr_get(x_769, 0);
if (lean::is_exclusive(x_769)) {
 x_776 = x_769;
} else {
 lean::inc(x_774);
 lean::dec(x_769);
 x_776 = lean::box(0);
}
if (lean::is_scalar(x_776)) {
 x_777 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_777 = x_776;
}
lean::cnstr_set(x_777, 0, x_774);
return x_777;
}
else
{
obj* x_778; obj* x_781; obj* x_783; obj* x_785; obj* x_786; 
x_778 = lean::cnstr_get(x_769, 0);
lean::inc(x_778);
lean::dec(x_769);
x_781 = lean::cnstr_get(x_778, 0);
x_783 = lean::cnstr_get(x_778, 1);
if (lean::is_exclusive(x_778)) {
 lean::cnstr_set(x_778, 0, lean::box(0));
 lean::cnstr_set(x_778, 1, lean::box(0));
 x_785 = x_778;
} else {
 lean::inc(x_781);
 lean::inc(x_783);
 lean::dec(x_778);
 x_785 = lean::box(0);
}
x_786 = l_List_reverse___rarg(x_781);
if (lean::obj_tag(x_786) == 0)
{
obj* x_790; obj* x_791; obj* x_793; 
lean::dec(x_785);
lean::dec(x_10);
lean::inc(x_0);
x_790 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_790, 0, x_0);
x_791 = l_Lean_Elaborator_toPexpr___main___closed__28;
lean::inc(x_2);
x_793 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_790, x_791, x_1, x_2, x_783);
lean::dec(x_783);
lean::dec(x_790);
if (lean::obj_tag(x_793) == 0)
{
obj* x_799; obj* x_801; obj* x_802; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_799 = lean::cnstr_get(x_793, 0);
if (lean::is_exclusive(x_793)) {
 x_801 = x_793;
} else {
 lean::inc(x_799);
 lean::dec(x_793);
 x_801 = lean::box(0);
}
if (lean::is_scalar(x_801)) {
 x_802 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_802 = x_801;
}
lean::cnstr_set(x_802, 0, x_799);
return x_802;
}
else
{
obj* x_803; 
x_803 = lean::cnstr_get(x_793, 0);
lean::inc(x_803);
lean::dec(x_793);
x_15 = x_803;
goto lbl_16;
}
}
else
{
obj* x_806; obj* x_808; obj* x_811; obj* x_812; obj* x_814; obj* x_815; obj* x_816; obj* x_817; obj* x_818; obj* x_820; obj* x_821; 
x_806 = lean::cnstr_get(x_786, 0);
lean::inc(x_806);
x_808 = lean::cnstr_get(x_786, 1);
lean::inc(x_808);
lean::dec(x_786);
x_811 = lean::mk_nat_obj(0ul);
x_812 = l_List_lengthAux___main___rarg(x_10, x_811);
lean::dec(x_10);
x_814 = lean::box(0);
x_815 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_816 = l_Lean_KVMap_setNat(x_814, x_815, x_812);
x_817 = l_List_reverse___rarg(x_808);
x_818 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_806, x_817);
lean::dec(x_806);
x_820 = lean_expr_mk_mdata(x_816, x_818);
if (lean::is_scalar(x_785)) {
 x_821 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_821 = x_785;
}
lean::cnstr_set(x_821, 0, x_820);
lean::cnstr_set(x_821, 1, x_783);
x_15 = x_821;
goto lbl_16;
}
}
}
}
else
{
obj* x_824; obj* x_825; obj* x_829; obj* x_830; 
lean::dec(x_8);
lean::dec(x_10);
x_824 = l_Lean_Parser_stringLit_HasView;
x_825 = lean::cnstr_get(x_824, 0);
lean::inc(x_825);
lean::dec(x_824);
lean::inc(x_0);
x_829 = lean::apply_1(x_825, x_0);
x_830 = l_Lean_Parser_stringLit_View_value(x_829);
if (lean::obj_tag(x_830) == 0)
{
obj* x_831; 
x_831 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_831) == 0)
{
obj* x_834; obj* x_835; obj* x_836; 
lean::dec(x_2);
x_834 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_835 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_835, 0, x_834);
lean::cnstr_set(x_835, 1, x_3);
x_836 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_836, 0, x_835);
return x_836;
}
else
{
obj* x_837; obj* x_840; obj* x_843; obj* x_846; obj* x_847; obj* x_849; obj* x_850; obj* x_851; obj* x_852; obj* x_855; obj* x_856; obj* x_857; obj* x_858; obj* x_859; obj* x_860; 
x_837 = lean::cnstr_get(x_831, 0);
lean::inc(x_837);
lean::dec(x_831);
x_840 = lean::cnstr_get(x_2, 0);
lean::inc(x_840);
lean::dec(x_2);
x_843 = lean::cnstr_get(x_840, 2);
lean::inc(x_843);
lean::dec(x_840);
x_846 = l_Lean_FileMap_toPosition(x_843, x_837);
x_847 = lean::cnstr_get(x_846, 1);
lean::inc(x_847);
x_849 = lean::box(0);
x_850 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_851 = l_Lean_KVMap_setNat(x_849, x_850, x_847);
x_852 = lean::cnstr_get(x_846, 0);
lean::inc(x_852);
lean::dec(x_846);
x_855 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_856 = l_Lean_KVMap_setNat(x_851, x_855, x_852);
x_857 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_858 = lean_expr_mk_mdata(x_856, x_857);
x_859 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_859, 0, x_858);
lean::cnstr_set(x_859, 1, x_3);
x_860 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_860, 0, x_859);
return x_860;
}
}
else
{
obj* x_861; obj* x_864; obj* x_865; obj* x_866; 
x_861 = lean::cnstr_get(x_830, 0);
lean::inc(x_861);
lean::dec(x_830);
x_864 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_864, 0, x_861);
x_865 = lean_expr_mk_lit(x_864);
x_866 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_866) == 0)
{
obj* x_869; obj* x_870; 
lean::dec(x_2);
x_869 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_869, 0, x_865);
lean::cnstr_set(x_869, 1, x_3);
x_870 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_870, 0, x_869);
return x_870;
}
else
{
obj* x_871; obj* x_874; obj* x_877; obj* x_880; obj* x_881; obj* x_883; obj* x_884; obj* x_885; obj* x_886; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; 
x_871 = lean::cnstr_get(x_866, 0);
lean::inc(x_871);
lean::dec(x_866);
x_874 = lean::cnstr_get(x_2, 0);
lean::inc(x_874);
lean::dec(x_2);
x_877 = lean::cnstr_get(x_874, 2);
lean::inc(x_877);
lean::dec(x_874);
x_880 = l_Lean_FileMap_toPosition(x_877, x_871);
x_881 = lean::cnstr_get(x_880, 1);
lean::inc(x_881);
x_883 = lean::box(0);
x_884 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_885 = l_Lean_KVMap_setNat(x_883, x_884, x_881);
x_886 = lean::cnstr_get(x_880, 0);
lean::inc(x_886);
lean::dec(x_880);
x_889 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_890 = l_Lean_KVMap_setNat(x_885, x_889, x_886);
x_891 = lean_expr_mk_mdata(x_890, x_865);
x_892 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_892, 0, x_891);
lean::cnstr_set(x_892, 1, x_3);
x_893 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_893, 0, x_892);
return x_893;
}
}
}
}
else
{
obj* x_896; obj* x_897; obj* x_901; obj* x_902; obj* x_903; obj* x_904; obj* x_905; 
lean::dec(x_8);
lean::dec(x_10);
x_896 = l_Lean_Parser_number_HasView;
x_897 = lean::cnstr_get(x_896, 0);
lean::inc(x_897);
lean::dec(x_896);
lean::inc(x_0);
x_901 = lean::apply_1(x_897, x_0);
x_902 = l_Lean_Parser_number_View_toNat___main(x_901);
x_903 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_903, 0, x_902);
x_904 = lean_expr_mk_lit(x_903);
x_905 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_905) == 0)
{
obj* x_908; obj* x_909; 
lean::dec(x_2);
x_908 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_908, 0, x_904);
lean::cnstr_set(x_908, 1, x_3);
x_909 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_909, 0, x_908);
return x_909;
}
else
{
obj* x_910; obj* x_913; obj* x_916; obj* x_919; obj* x_920; obj* x_922; obj* x_923; obj* x_924; obj* x_925; obj* x_928; obj* x_929; obj* x_930; obj* x_931; obj* x_932; 
x_910 = lean::cnstr_get(x_905, 0);
lean::inc(x_910);
lean::dec(x_905);
x_913 = lean::cnstr_get(x_2, 0);
lean::inc(x_913);
lean::dec(x_2);
x_916 = lean::cnstr_get(x_913, 2);
lean::inc(x_916);
lean::dec(x_913);
x_919 = l_Lean_FileMap_toPosition(x_916, x_910);
x_920 = lean::cnstr_get(x_919, 1);
lean::inc(x_920);
x_922 = lean::box(0);
x_923 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_924 = l_Lean_KVMap_setNat(x_922, x_923, x_920);
x_925 = lean::cnstr_get(x_919, 0);
lean::inc(x_925);
lean::dec(x_919);
x_928 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_929 = l_Lean_KVMap_setNat(x_924, x_928, x_925);
x_930 = lean_expr_mk_mdata(x_929, x_904);
x_931 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_931, 0, x_930);
lean::cnstr_set(x_931, 1, x_3);
x_932 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_932, 0, x_931);
return x_932;
}
}
}
else
{
obj* x_935; obj* x_936; obj* x_940; obj* x_941; obj* x_945; 
lean::dec(x_8);
lean::dec(x_10);
x_935 = l_Lean_Parser_Term_borrowed_HasView;
x_936 = lean::cnstr_get(x_935, 0);
lean::inc(x_936);
lean::dec(x_935);
lean::inc(x_0);
x_940 = lean::apply_1(x_936, x_0);
x_941 = lean::cnstr_get(x_940, 1);
lean::inc(x_941);
lean::dec(x_940);
lean::inc(x_2);
x_945 = l_Lean_Elaborator_toPexpr___main(x_941, x_1, x_2, x_3);
if (lean::obj_tag(x_945) == 0)
{
obj* x_948; obj* x_950; obj* x_951; 
lean::dec(x_0);
lean::dec(x_2);
x_948 = lean::cnstr_get(x_945, 0);
if (lean::is_exclusive(x_945)) {
 x_950 = x_945;
} else {
 lean::inc(x_948);
 lean::dec(x_945);
 x_950 = lean::box(0);
}
if (lean::is_scalar(x_950)) {
 x_951 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_951 = x_950;
}
lean::cnstr_set(x_951, 0, x_948);
return x_951;
}
else
{
obj* x_952; obj* x_954; obj* x_955; obj* x_957; obj* x_959; obj* x_960; obj* x_961; obj* x_962; 
x_952 = lean::cnstr_get(x_945, 0);
if (lean::is_exclusive(x_945)) {
 lean::cnstr_set(x_945, 0, lean::box(0));
 x_954 = x_945;
} else {
 lean::inc(x_952);
 lean::dec(x_945);
 x_954 = lean::box(0);
}
x_955 = lean::cnstr_get(x_952, 0);
x_957 = lean::cnstr_get(x_952, 1);
if (lean::is_exclusive(x_952)) {
 lean::cnstr_set(x_952, 0, lean::box(0));
 lean::cnstr_set(x_952, 1, lean::box(0));
 x_959 = x_952;
} else {
 lean::inc(x_955);
 lean::inc(x_957);
 lean::dec(x_952);
 x_959 = lean::box(0);
}
x_960 = l_Lean_Elaborator_toPexpr___main___closed__31;
x_961 = l_Lean_Elaborator_Expr_mkAnnotation(x_960, x_955);
x_962 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_962) == 0)
{
obj* x_965; obj* x_966; 
lean::dec(x_2);
if (lean::is_scalar(x_959)) {
 x_965 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_965 = x_959;
}
lean::cnstr_set(x_965, 0, x_961);
lean::cnstr_set(x_965, 1, x_957);
if (lean::is_scalar(x_954)) {
 x_966 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_966 = x_954;
}
lean::cnstr_set(x_966, 0, x_965);
return x_966;
}
else
{
obj* x_967; obj* x_970; obj* x_973; obj* x_976; obj* x_977; obj* x_979; obj* x_980; obj* x_981; obj* x_982; obj* x_985; obj* x_986; obj* x_987; obj* x_988; obj* x_989; 
x_967 = lean::cnstr_get(x_962, 0);
lean::inc(x_967);
lean::dec(x_962);
x_970 = lean::cnstr_get(x_2, 0);
lean::inc(x_970);
lean::dec(x_2);
x_973 = lean::cnstr_get(x_970, 2);
lean::inc(x_973);
lean::dec(x_970);
x_976 = l_Lean_FileMap_toPosition(x_973, x_967);
x_977 = lean::cnstr_get(x_976, 1);
lean::inc(x_977);
x_979 = lean::box(0);
x_980 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_981 = l_Lean_KVMap_setNat(x_979, x_980, x_977);
x_982 = lean::cnstr_get(x_976, 0);
lean::inc(x_982);
lean::dec(x_976);
x_985 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_986 = l_Lean_KVMap_setNat(x_981, x_985, x_982);
x_987 = lean_expr_mk_mdata(x_986, x_961);
if (lean::is_scalar(x_959)) {
 x_988 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_988 = x_959;
}
lean::cnstr_set(x_988, 0, x_987);
lean::cnstr_set(x_988, 1, x_957);
if (lean::is_scalar(x_954)) {
 x_989 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_989 = x_954;
}
lean::cnstr_set(x_989, 0, x_988);
return x_989;
}
}
}
}
else
{
obj* x_992; obj* x_993; obj* x_997; obj* x_998; obj* x_1002; 
lean::dec(x_8);
lean::dec(x_10);
x_992 = l_Lean_Parser_Term_inaccessible_HasView;
x_993 = lean::cnstr_get(x_992, 0);
lean::inc(x_993);
lean::dec(x_992);
lean::inc(x_0);
x_997 = lean::apply_1(x_993, x_0);
x_998 = lean::cnstr_get(x_997, 1);
lean::inc(x_998);
lean::dec(x_997);
lean::inc(x_2);
x_1002 = l_Lean_Elaborator_toPexpr___main(x_998, x_1, x_2, x_3);
if (lean::obj_tag(x_1002) == 0)
{
obj* x_1005; obj* x_1007; obj* x_1008; 
lean::dec(x_0);
lean::dec(x_2);
x_1005 = lean::cnstr_get(x_1002, 0);
if (lean::is_exclusive(x_1002)) {
 x_1007 = x_1002;
} else {
 lean::inc(x_1005);
 lean::dec(x_1002);
 x_1007 = lean::box(0);
}
if (lean::is_scalar(x_1007)) {
 x_1008 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1008 = x_1007;
}
lean::cnstr_set(x_1008, 0, x_1005);
return x_1008;
}
else
{
obj* x_1009; obj* x_1011; obj* x_1012; obj* x_1014; obj* x_1016; obj* x_1017; obj* x_1018; obj* x_1019; 
x_1009 = lean::cnstr_get(x_1002, 0);
if (lean::is_exclusive(x_1002)) {
 lean::cnstr_set(x_1002, 0, lean::box(0));
 x_1011 = x_1002;
} else {
 lean::inc(x_1009);
 lean::dec(x_1002);
 x_1011 = lean::box(0);
}
x_1012 = lean::cnstr_get(x_1009, 0);
x_1014 = lean::cnstr_get(x_1009, 1);
if (lean::is_exclusive(x_1009)) {
 lean::cnstr_set(x_1009, 0, lean::box(0));
 lean::cnstr_set(x_1009, 1, lean::box(0));
 x_1016 = x_1009;
} else {
 lean::inc(x_1012);
 lean::inc(x_1014);
 lean::dec(x_1009);
 x_1016 = lean::box(0);
}
x_1017 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_1018 = l_Lean_Elaborator_Expr_mkAnnotation(x_1017, x_1012);
x_1019 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1019) == 0)
{
obj* x_1022; obj* x_1023; 
lean::dec(x_2);
if (lean::is_scalar(x_1016)) {
 x_1022 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1022 = x_1016;
}
lean::cnstr_set(x_1022, 0, x_1018);
lean::cnstr_set(x_1022, 1, x_1014);
if (lean::is_scalar(x_1011)) {
 x_1023 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1023 = x_1011;
}
lean::cnstr_set(x_1023, 0, x_1022);
return x_1023;
}
else
{
obj* x_1024; obj* x_1027; obj* x_1030; obj* x_1033; obj* x_1034; obj* x_1036; obj* x_1037; obj* x_1038; obj* x_1039; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; obj* x_1046; 
x_1024 = lean::cnstr_get(x_1019, 0);
lean::inc(x_1024);
lean::dec(x_1019);
x_1027 = lean::cnstr_get(x_2, 0);
lean::inc(x_1027);
lean::dec(x_2);
x_1030 = lean::cnstr_get(x_1027, 2);
lean::inc(x_1030);
lean::dec(x_1027);
x_1033 = l_Lean_FileMap_toPosition(x_1030, x_1024);
x_1034 = lean::cnstr_get(x_1033, 1);
lean::inc(x_1034);
x_1036 = lean::box(0);
x_1037 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1038 = l_Lean_KVMap_setNat(x_1036, x_1037, x_1034);
x_1039 = lean::cnstr_get(x_1033, 0);
lean::inc(x_1039);
lean::dec(x_1033);
x_1042 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1043 = l_Lean_KVMap_setNat(x_1038, x_1042, x_1039);
x_1044 = lean_expr_mk_mdata(x_1043, x_1018);
if (lean::is_scalar(x_1016)) {
 x_1045 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1045 = x_1016;
}
lean::cnstr_set(x_1045, 0, x_1044);
lean::cnstr_set(x_1045, 1, x_1014);
if (lean::is_scalar(x_1011)) {
 x_1046 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1046 = x_1011;
}
lean::cnstr_set(x_1046, 0, x_1045);
return x_1046;
}
}
}
}
else
{
obj* x_1049; obj* x_1050; obj* x_1054; obj* x_1055; obj* x_1057; obj* x_1058; obj* x_1061; obj* x_1064; 
lean::dec(x_8);
lean::dec(x_10);
x_1049 = l_Lean_Parser_Term_explicit_HasView;
x_1050 = lean::cnstr_get(x_1049, 0);
lean::inc(x_1050);
lean::dec(x_1049);
lean::inc(x_0);
x_1054 = lean::apply_1(x_1050, x_0);
x_1055 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1055);
x_1057 = l_Lean_Parser_identUnivs_HasView;
x_1058 = lean::cnstr_get(x_1057, 1);
lean::inc(x_1058);
lean::dec(x_1057);
x_1061 = lean::cnstr_get(x_1054, 1);
lean::inc(x_1061);
lean::dec(x_1054);
x_1064 = lean::apply_1(x_1058, x_1061);
if (lean::obj_tag(x_1055) == 0)
{
obj* x_1067; 
lean::dec(x_1055);
lean::inc(x_2);
x_1067 = l_Lean_Elaborator_toPexpr___main(x_1064, x_1, x_2, x_3);
if (lean::obj_tag(x_1067) == 0)
{
obj* x_1070; obj* x_1072; obj* x_1073; 
lean::dec(x_0);
lean::dec(x_2);
x_1070 = lean::cnstr_get(x_1067, 0);
if (lean::is_exclusive(x_1067)) {
 x_1072 = x_1067;
} else {
 lean::inc(x_1070);
 lean::dec(x_1067);
 x_1072 = lean::box(0);
}
if (lean::is_scalar(x_1072)) {
 x_1073 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1073 = x_1072;
}
lean::cnstr_set(x_1073, 0, x_1070);
return x_1073;
}
else
{
obj* x_1074; obj* x_1076; obj* x_1077; obj* x_1079; obj* x_1081; obj* x_1082; obj* x_1083; obj* x_1084; 
x_1074 = lean::cnstr_get(x_1067, 0);
if (lean::is_exclusive(x_1067)) {
 lean::cnstr_set(x_1067, 0, lean::box(0));
 x_1076 = x_1067;
} else {
 lean::inc(x_1074);
 lean::dec(x_1067);
 x_1076 = lean::box(0);
}
x_1077 = lean::cnstr_get(x_1074, 0);
x_1079 = lean::cnstr_get(x_1074, 1);
if (lean::is_exclusive(x_1074)) {
 lean::cnstr_set(x_1074, 0, lean::box(0));
 lean::cnstr_set(x_1074, 1, lean::box(0));
 x_1081 = x_1074;
} else {
 lean::inc(x_1077);
 lean::inc(x_1079);
 lean::dec(x_1074);
 x_1081 = lean::box(0);
}
x_1082 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_1083 = l_Lean_Elaborator_Expr_mkAnnotation(x_1082, x_1077);
x_1084 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1084) == 0)
{
obj* x_1087; obj* x_1088; 
lean::dec(x_2);
if (lean::is_scalar(x_1081)) {
 x_1087 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1087 = x_1081;
}
lean::cnstr_set(x_1087, 0, x_1083);
lean::cnstr_set(x_1087, 1, x_1079);
if (lean::is_scalar(x_1076)) {
 x_1088 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1088 = x_1076;
}
lean::cnstr_set(x_1088, 0, x_1087);
return x_1088;
}
else
{
obj* x_1089; obj* x_1092; obj* x_1095; obj* x_1098; obj* x_1099; obj* x_1101; obj* x_1102; obj* x_1103; obj* x_1104; obj* x_1107; obj* x_1108; obj* x_1109; obj* x_1110; obj* x_1111; 
x_1089 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1089);
lean::dec(x_1084);
x_1092 = lean::cnstr_get(x_2, 0);
lean::inc(x_1092);
lean::dec(x_2);
x_1095 = lean::cnstr_get(x_1092, 2);
lean::inc(x_1095);
lean::dec(x_1092);
x_1098 = l_Lean_FileMap_toPosition(x_1095, x_1089);
x_1099 = lean::cnstr_get(x_1098, 1);
lean::inc(x_1099);
x_1101 = lean::box(0);
x_1102 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1103 = l_Lean_KVMap_setNat(x_1101, x_1102, x_1099);
x_1104 = lean::cnstr_get(x_1098, 0);
lean::inc(x_1104);
lean::dec(x_1098);
x_1107 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1108 = l_Lean_KVMap_setNat(x_1103, x_1107, x_1104);
x_1109 = lean_expr_mk_mdata(x_1108, x_1083);
if (lean::is_scalar(x_1081)) {
 x_1110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1110 = x_1081;
}
lean::cnstr_set(x_1110, 0, x_1109);
lean::cnstr_set(x_1110, 1, x_1079);
if (lean::is_scalar(x_1076)) {
 x_1111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1111 = x_1076;
}
lean::cnstr_set(x_1111, 0, x_1110);
return x_1111;
}
}
}
else
{
obj* x_1114; 
lean::dec(x_1055);
lean::inc(x_2);
x_1114 = l_Lean_Elaborator_toPexpr___main(x_1064, x_1, x_2, x_3);
if (lean::obj_tag(x_1114) == 0)
{
obj* x_1117; obj* x_1119; obj* x_1120; 
lean::dec(x_0);
lean::dec(x_2);
x_1117 = lean::cnstr_get(x_1114, 0);
if (lean::is_exclusive(x_1114)) {
 x_1119 = x_1114;
} else {
 lean::inc(x_1117);
 lean::dec(x_1114);
 x_1119 = lean::box(0);
}
if (lean::is_scalar(x_1119)) {
 x_1120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1120 = x_1119;
}
lean::cnstr_set(x_1120, 0, x_1117);
return x_1120;
}
else
{
obj* x_1121; obj* x_1123; obj* x_1124; obj* x_1126; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; 
x_1121 = lean::cnstr_get(x_1114, 0);
if (lean::is_exclusive(x_1114)) {
 lean::cnstr_set(x_1114, 0, lean::box(0));
 x_1123 = x_1114;
} else {
 lean::inc(x_1121);
 lean::dec(x_1114);
 x_1123 = lean::box(0);
}
x_1124 = lean::cnstr_get(x_1121, 0);
x_1126 = lean::cnstr_get(x_1121, 1);
if (lean::is_exclusive(x_1121)) {
 lean::cnstr_set(x_1121, 0, lean::box(0));
 lean::cnstr_set(x_1121, 1, lean::box(0));
 x_1128 = x_1121;
} else {
 lean::inc(x_1124);
 lean::inc(x_1126);
 lean::dec(x_1121);
 x_1128 = lean::box(0);
}
x_1129 = l_Lean_Elaborator_toPexpr___main___closed__33;
x_1130 = l_Lean_Elaborator_Expr_mkAnnotation(x_1129, x_1124);
x_1131 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1131) == 0)
{
obj* x_1134; obj* x_1135; 
lean::dec(x_2);
if (lean::is_scalar(x_1128)) {
 x_1134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1134 = x_1128;
}
lean::cnstr_set(x_1134, 0, x_1130);
lean::cnstr_set(x_1134, 1, x_1126);
if (lean::is_scalar(x_1123)) {
 x_1135 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1135 = x_1123;
}
lean::cnstr_set(x_1135, 0, x_1134);
return x_1135;
}
else
{
obj* x_1136; obj* x_1139; obj* x_1142; obj* x_1145; obj* x_1146; obj* x_1148; obj* x_1149; obj* x_1150; obj* x_1151; obj* x_1154; obj* x_1155; obj* x_1156; obj* x_1157; obj* x_1158; 
x_1136 = lean::cnstr_get(x_1131, 0);
lean::inc(x_1136);
lean::dec(x_1131);
x_1139 = lean::cnstr_get(x_2, 0);
lean::inc(x_1139);
lean::dec(x_2);
x_1142 = lean::cnstr_get(x_1139, 2);
lean::inc(x_1142);
lean::dec(x_1139);
x_1145 = l_Lean_FileMap_toPosition(x_1142, x_1136);
x_1146 = lean::cnstr_get(x_1145, 1);
lean::inc(x_1146);
x_1148 = lean::box(0);
x_1149 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1150 = l_Lean_KVMap_setNat(x_1148, x_1149, x_1146);
x_1151 = lean::cnstr_get(x_1145, 0);
lean::inc(x_1151);
lean::dec(x_1145);
x_1154 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1155 = l_Lean_KVMap_setNat(x_1150, x_1154, x_1151);
x_1156 = lean_expr_mk_mdata(x_1155, x_1130);
if (lean::is_scalar(x_1128)) {
 x_1157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1157 = x_1128;
}
lean::cnstr_set(x_1157, 0, x_1156);
lean::cnstr_set(x_1157, 1, x_1126);
if (lean::is_scalar(x_1123)) {
 x_1158 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1158 = x_1123;
}
lean::cnstr_set(x_1158, 0, x_1157);
return x_1158;
}
}
}
}
}
else
{
obj* x_1161; obj* x_1162; obj* x_1166; obj* x_1167; 
lean::dec(x_8);
lean::dec(x_10);
x_1161 = l_Lean_Parser_Term_projection_HasView;
x_1162 = lean::cnstr_get(x_1161, 0);
lean::inc(x_1162);
lean::dec(x_1161);
lean::inc(x_0);
x_1166 = lean::apply_1(x_1162, x_0);
x_1167 = lean::cnstr_get(x_1166, 2);
lean::inc(x_1167);
if (lean::obj_tag(x_1167) == 0)
{
obj* x_1169; obj* x_1172; obj* x_1175; obj* x_1178; obj* x_1180; 
x_1169 = lean::cnstr_get(x_1166, 0);
lean::inc(x_1169);
lean::dec(x_1166);
x_1172 = lean::cnstr_get(x_1167, 0);
lean::inc(x_1172);
lean::dec(x_1167);
x_1175 = lean::cnstr_get(x_1172, 2);
lean::inc(x_1175);
lean::dec(x_1172);
x_1178 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1178, 0, x_1175);
lean::inc(x_2);
x_1180 = l_Lean_Elaborator_toPexpr___main(x_1169, x_1, x_2, x_3);
if (lean::obj_tag(x_1180) == 0)
{
obj* x_1184; obj* x_1186; obj* x_1187; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1178);
x_1184 = lean::cnstr_get(x_1180, 0);
if (lean::is_exclusive(x_1180)) {
 x_1186 = x_1180;
} else {
 lean::inc(x_1184);
 lean::dec(x_1180);
 x_1186 = lean::box(0);
}
if (lean::is_scalar(x_1186)) {
 x_1187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1187 = x_1186;
}
lean::cnstr_set(x_1187, 0, x_1184);
return x_1187;
}
else
{
obj* x_1188; obj* x_1190; obj* x_1191; obj* x_1193; obj* x_1195; obj* x_1196; obj* x_1197; obj* x_1198; obj* x_1199; obj* x_1200; 
x_1188 = lean::cnstr_get(x_1180, 0);
if (lean::is_exclusive(x_1180)) {
 lean::cnstr_set(x_1180, 0, lean::box(0));
 x_1190 = x_1180;
} else {
 lean::inc(x_1188);
 lean::dec(x_1180);
 x_1190 = lean::box(0);
}
x_1191 = lean::cnstr_get(x_1188, 0);
x_1193 = lean::cnstr_get(x_1188, 1);
if (lean::is_exclusive(x_1188)) {
 lean::cnstr_set(x_1188, 0, lean::box(0));
 lean::cnstr_set(x_1188, 1, lean::box(0));
 x_1195 = x_1188;
} else {
 lean::inc(x_1191);
 lean::inc(x_1193);
 lean::dec(x_1188);
 x_1195 = lean::box(0);
}
x_1196 = lean::box(0);
x_1197 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1198 = l_Lean_KVMap_insertCore___main(x_1196, x_1197, x_1178);
x_1199 = lean_expr_mk_mdata(x_1198, x_1191);
x_1200 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1200) == 0)
{
obj* x_1203; obj* x_1204; 
lean::dec(x_2);
if (lean::is_scalar(x_1195)) {
 x_1203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1203 = x_1195;
}
lean::cnstr_set(x_1203, 0, x_1199);
lean::cnstr_set(x_1203, 1, x_1193);
if (lean::is_scalar(x_1190)) {
 x_1204 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1204 = x_1190;
}
lean::cnstr_set(x_1204, 0, x_1203);
return x_1204;
}
else
{
obj* x_1205; obj* x_1208; obj* x_1211; obj* x_1214; obj* x_1215; obj* x_1217; obj* x_1218; obj* x_1219; obj* x_1222; obj* x_1223; obj* x_1224; obj* x_1225; obj* x_1226; 
x_1205 = lean::cnstr_get(x_1200, 0);
lean::inc(x_1205);
lean::dec(x_1200);
x_1208 = lean::cnstr_get(x_2, 0);
lean::inc(x_1208);
lean::dec(x_2);
x_1211 = lean::cnstr_get(x_1208, 2);
lean::inc(x_1211);
lean::dec(x_1208);
x_1214 = l_Lean_FileMap_toPosition(x_1211, x_1205);
x_1215 = lean::cnstr_get(x_1214, 1);
lean::inc(x_1215);
x_1217 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1218 = l_Lean_KVMap_setNat(x_1196, x_1217, x_1215);
x_1219 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1219);
lean::dec(x_1214);
x_1222 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1223 = l_Lean_KVMap_setNat(x_1218, x_1222, x_1219);
x_1224 = lean_expr_mk_mdata(x_1223, x_1199);
if (lean::is_scalar(x_1195)) {
 x_1225 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1225 = x_1195;
}
lean::cnstr_set(x_1225, 0, x_1224);
lean::cnstr_set(x_1225, 1, x_1193);
if (lean::is_scalar(x_1190)) {
 x_1226 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1226 = x_1190;
}
lean::cnstr_set(x_1226, 0, x_1225);
return x_1226;
}
}
}
else
{
obj* x_1227; obj* x_1230; obj* x_1233; obj* x_1234; obj* x_1236; 
x_1227 = lean::cnstr_get(x_1166, 0);
lean::inc(x_1227);
lean::dec(x_1166);
x_1230 = lean::cnstr_get(x_1167, 0);
lean::inc(x_1230);
lean::dec(x_1167);
x_1233 = l_Lean_Parser_number_View_toNat___main(x_1230);
x_1234 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1234, 0, x_1233);
lean::inc(x_2);
x_1236 = l_Lean_Elaborator_toPexpr___main(x_1227, x_1, x_2, x_3);
if (lean::obj_tag(x_1236) == 0)
{
obj* x_1240; obj* x_1242; obj* x_1243; 
lean::dec(x_1234);
lean::dec(x_0);
lean::dec(x_2);
x_1240 = lean::cnstr_get(x_1236, 0);
if (lean::is_exclusive(x_1236)) {
 x_1242 = x_1236;
} else {
 lean::inc(x_1240);
 lean::dec(x_1236);
 x_1242 = lean::box(0);
}
if (lean::is_scalar(x_1242)) {
 x_1243 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1243 = x_1242;
}
lean::cnstr_set(x_1243, 0, x_1240);
return x_1243;
}
else
{
obj* x_1244; obj* x_1246; obj* x_1247; obj* x_1249; obj* x_1251; obj* x_1252; obj* x_1253; obj* x_1254; obj* x_1255; obj* x_1256; 
x_1244 = lean::cnstr_get(x_1236, 0);
if (lean::is_exclusive(x_1236)) {
 lean::cnstr_set(x_1236, 0, lean::box(0));
 x_1246 = x_1236;
} else {
 lean::inc(x_1244);
 lean::dec(x_1236);
 x_1246 = lean::box(0);
}
x_1247 = lean::cnstr_get(x_1244, 0);
x_1249 = lean::cnstr_get(x_1244, 1);
if (lean::is_exclusive(x_1244)) {
 lean::cnstr_set(x_1244, 0, lean::box(0));
 lean::cnstr_set(x_1244, 1, lean::box(0));
 x_1251 = x_1244;
} else {
 lean::inc(x_1247);
 lean::inc(x_1249);
 lean::dec(x_1244);
 x_1251 = lean::box(0);
}
x_1252 = lean::box(0);
x_1253 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1254 = l_Lean_KVMap_insertCore___main(x_1252, x_1253, x_1234);
x_1255 = lean_expr_mk_mdata(x_1254, x_1247);
x_1256 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1256) == 0)
{
obj* x_1259; obj* x_1260; 
lean::dec(x_2);
if (lean::is_scalar(x_1251)) {
 x_1259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1259 = x_1251;
}
lean::cnstr_set(x_1259, 0, x_1255);
lean::cnstr_set(x_1259, 1, x_1249);
if (lean::is_scalar(x_1246)) {
 x_1260 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1260 = x_1246;
}
lean::cnstr_set(x_1260, 0, x_1259);
return x_1260;
}
else
{
obj* x_1261; obj* x_1264; obj* x_1267; obj* x_1270; obj* x_1271; obj* x_1273; obj* x_1274; obj* x_1275; obj* x_1278; obj* x_1279; obj* x_1280; obj* x_1281; obj* x_1282; 
x_1261 = lean::cnstr_get(x_1256, 0);
lean::inc(x_1261);
lean::dec(x_1256);
x_1264 = lean::cnstr_get(x_2, 0);
lean::inc(x_1264);
lean::dec(x_2);
x_1267 = lean::cnstr_get(x_1264, 2);
lean::inc(x_1267);
lean::dec(x_1264);
x_1270 = l_Lean_FileMap_toPosition(x_1267, x_1261);
x_1271 = lean::cnstr_get(x_1270, 1);
lean::inc(x_1271);
x_1273 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1274 = l_Lean_KVMap_setNat(x_1252, x_1273, x_1271);
x_1275 = lean::cnstr_get(x_1270, 0);
lean::inc(x_1275);
lean::dec(x_1270);
x_1278 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1279 = l_Lean_KVMap_setNat(x_1274, x_1278, x_1275);
x_1280 = lean_expr_mk_mdata(x_1279, x_1255);
if (lean::is_scalar(x_1251)) {
 x_1281 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1281 = x_1251;
}
lean::cnstr_set(x_1281, 0, x_1280);
lean::cnstr_set(x_1281, 1, x_1249);
if (lean::is_scalar(x_1246)) {
 x_1282 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1282 = x_1246;
}
lean::cnstr_set(x_1282, 0, x_1281);
return x_1282;
}
}
}
}
}
else
{
obj* x_1284; obj* x_1285; obj* x_1289; obj* x_1290; 
lean::dec(x_10);
x_1284 = l_Lean_Parser_Term_let_HasView;
x_1285 = lean::cnstr_get(x_1284, 0);
lean::inc(x_1285);
lean::dec(x_1284);
lean::inc(x_0);
x_1289 = lean::apply_1(x_1285, x_0);
x_1290 = lean::cnstr_get(x_1289, 1);
lean::inc(x_1290);
if (lean::obj_tag(x_1290) == 0)
{
obj* x_1292; obj* x_1295; 
x_1292 = lean::cnstr_get(x_1290, 0);
lean::inc(x_1292);
lean::dec(x_1290);
x_1295 = lean::cnstr_get(x_1292, 1);
lean::inc(x_1295);
if (lean::obj_tag(x_1295) == 0)
{
obj* x_1297; 
x_1297 = lean::cnstr_get(x_1292, 2);
lean::inc(x_1297);
if (lean::obj_tag(x_1297) == 0)
{
obj* x_1302; obj* x_1303; obj* x_1305; 
lean::dec(x_1289);
lean::dec(x_1292);
lean::inc(x_0);
x_1302 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1302, 0, x_0);
x_1303 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1305 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1302, x_1303, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1302);
if (lean::obj_tag(x_1305) == 0)
{
obj* x_1311; obj* x_1313; obj* x_1314; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1311 = lean::cnstr_get(x_1305, 0);
if (lean::is_exclusive(x_1305)) {
 x_1313 = x_1305;
} else {
 lean::inc(x_1311);
 lean::dec(x_1305);
 x_1313 = lean::box(0);
}
if (lean::is_scalar(x_1313)) {
 x_1314 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1314 = x_1313;
}
lean::cnstr_set(x_1314, 0, x_1311);
return x_1314;
}
else
{
obj* x_1315; 
x_1315 = lean::cnstr_get(x_1305, 0);
lean::inc(x_1315);
lean::dec(x_1305);
x_15 = x_1315;
goto lbl_16;
}
}
else
{
obj* x_1318; obj* x_1321; obj* x_1324; obj* x_1327; obj* x_1329; obj* x_1333; 
x_1318 = lean::cnstr_get(x_1292, 0);
lean::inc(x_1318);
lean::dec(x_1292);
x_1321 = lean::cnstr_get(x_1297, 0);
lean::inc(x_1321);
lean::dec(x_1297);
x_1324 = lean::cnstr_get(x_1321, 1);
lean::inc(x_1324);
lean::dec(x_1321);
x_1327 = lean::cnstr_get(x_1289, 3);
lean::inc(x_1327);
x_1329 = lean::cnstr_get(x_1289, 5);
lean::inc(x_1329);
lean::dec(x_1289);
lean::inc(x_2);
x_1333 = l_Lean_Elaborator_toPexpr___main(x_1324, x_1, x_2, x_3);
if (lean::obj_tag(x_1333) == 0)
{
obj* x_1340; obj* x_1342; obj* x_1343; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1329);
lean::dec(x_1327);
lean::dec(x_1318);
x_1340 = lean::cnstr_get(x_1333, 0);
if (lean::is_exclusive(x_1333)) {
 x_1342 = x_1333;
} else {
 lean::inc(x_1340);
 lean::dec(x_1333);
 x_1342 = lean::box(0);
}
if (lean::is_scalar(x_1342)) {
 x_1343 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1343 = x_1342;
}
lean::cnstr_set(x_1343, 0, x_1340);
return x_1343;
}
else
{
obj* x_1344; obj* x_1347; obj* x_1349; obj* x_1353; 
x_1344 = lean::cnstr_get(x_1333, 0);
lean::inc(x_1344);
lean::dec(x_1333);
x_1347 = lean::cnstr_get(x_1344, 0);
lean::inc(x_1347);
x_1349 = lean::cnstr_get(x_1344, 1);
lean::inc(x_1349);
lean::dec(x_1344);
lean::inc(x_2);
x_1353 = l_Lean_Elaborator_toPexpr___main(x_1327, x_1, x_2, x_1349);
if (lean::obj_tag(x_1353) == 0)
{
obj* x_1360; obj* x_1362; obj* x_1363; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1329);
lean::dec(x_1318);
lean::dec(x_1347);
x_1360 = lean::cnstr_get(x_1353, 0);
if (lean::is_exclusive(x_1353)) {
 x_1362 = x_1353;
} else {
 lean::inc(x_1360);
 lean::dec(x_1353);
 x_1362 = lean::box(0);
}
if (lean::is_scalar(x_1362)) {
 x_1363 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1363 = x_1362;
}
lean::cnstr_set(x_1363, 0, x_1360);
return x_1363;
}
else
{
obj* x_1364; obj* x_1367; obj* x_1369; obj* x_1373; 
x_1364 = lean::cnstr_get(x_1353, 0);
lean::inc(x_1364);
lean::dec(x_1353);
x_1367 = lean::cnstr_get(x_1364, 0);
lean::inc(x_1367);
x_1369 = lean::cnstr_get(x_1364, 1);
lean::inc(x_1369);
lean::dec(x_1364);
lean::inc(x_2);
x_1373 = l_Lean_Elaborator_toPexpr___main(x_1329, x_1, x_2, x_1369);
if (lean::obj_tag(x_1373) == 0)
{
obj* x_1380; obj* x_1382; obj* x_1383; 
lean::dec(x_1367);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1318);
lean::dec(x_1347);
x_1380 = lean::cnstr_get(x_1373, 0);
if (lean::is_exclusive(x_1373)) {
 x_1382 = x_1373;
} else {
 lean::inc(x_1380);
 lean::dec(x_1373);
 x_1382 = lean::box(0);
}
if (lean::is_scalar(x_1382)) {
 x_1383 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1383 = x_1382;
}
lean::cnstr_set(x_1383, 0, x_1380);
return x_1383;
}
else
{
obj* x_1384; obj* x_1387; obj* x_1389; obj* x_1391; obj* x_1392; obj* x_1393; obj* x_1394; 
x_1384 = lean::cnstr_get(x_1373, 0);
lean::inc(x_1384);
lean::dec(x_1373);
x_1387 = lean::cnstr_get(x_1384, 0);
x_1389 = lean::cnstr_get(x_1384, 1);
if (lean::is_exclusive(x_1384)) {
 x_1391 = x_1384;
} else {
 lean::inc(x_1387);
 lean::inc(x_1389);
 lean::dec(x_1384);
 x_1391 = lean::box(0);
}
x_1392 = l_Lean_Elaborator_mangleIdent(x_1318);
x_1393 = lean_expr_mk_let(x_1392, x_1347, x_1367, x_1387);
if (lean::is_scalar(x_1391)) {
 x_1394 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1394 = x_1391;
}
lean::cnstr_set(x_1394, 0, x_1393);
lean::cnstr_set(x_1394, 1, x_1389);
x_15 = x_1394;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1399; obj* x_1400; obj* x_1402; 
lean::dec(x_1289);
lean::dec(x_1292);
lean::dec(x_1295);
lean::inc(x_0);
x_1399 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1399, 0, x_0);
x_1400 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1402 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1399, x_1400, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1399);
if (lean::obj_tag(x_1402) == 0)
{
obj* x_1408; obj* x_1410; obj* x_1411; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1408 = lean::cnstr_get(x_1402, 0);
if (lean::is_exclusive(x_1402)) {
 x_1410 = x_1402;
} else {
 lean::inc(x_1408);
 lean::dec(x_1402);
 x_1410 = lean::box(0);
}
if (lean::is_scalar(x_1410)) {
 x_1411 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1411 = x_1410;
}
lean::cnstr_set(x_1411, 0, x_1408);
return x_1411;
}
else
{
obj* x_1412; 
x_1412 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1412);
lean::dec(x_1402);
x_15 = x_1412;
goto lbl_16;
}
}
}
else
{
obj* x_1418; obj* x_1419; obj* x_1421; 
lean::dec(x_1290);
lean::dec(x_1289);
lean::inc(x_0);
x_1418 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1418, 0, x_0);
x_1419 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1421 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1418, x_1419, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1418);
if (lean::obj_tag(x_1421) == 0)
{
obj* x_1427; obj* x_1429; obj* x_1430; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1427 = lean::cnstr_get(x_1421, 0);
if (lean::is_exclusive(x_1421)) {
 x_1429 = x_1421;
} else {
 lean::inc(x_1427);
 lean::dec(x_1421);
 x_1429 = lean::box(0);
}
if (lean::is_scalar(x_1429)) {
 x_1430 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1430 = x_1429;
}
lean::cnstr_set(x_1430, 0, x_1427);
return x_1430;
}
else
{
obj* x_1431; 
x_1431 = lean::cnstr_get(x_1421, 0);
lean::inc(x_1431);
lean::dec(x_1421);
x_15 = x_1431;
goto lbl_16;
}
}
}
}
else
{
obj* x_1436; obj* x_1437; obj* x_1441; obj* x_1442; obj* x_1445; 
lean::dec(x_8);
lean::dec(x_10);
x_1436 = l_Lean_Parser_Term_show_HasView;
x_1437 = lean::cnstr_get(x_1436, 0);
lean::inc(x_1437);
lean::dec(x_1436);
lean::inc(x_0);
x_1441 = lean::apply_1(x_1437, x_0);
x_1442 = lean::cnstr_get(x_1441, 1);
lean::inc(x_1442);
lean::inc(x_2);
x_1445 = l_Lean_Elaborator_toPexpr___main(x_1442, x_1, x_2, x_3);
if (lean::obj_tag(x_1445) == 0)
{
obj* x_1449; obj* x_1451; obj* x_1452; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1441);
x_1449 = lean::cnstr_get(x_1445, 0);
if (lean::is_exclusive(x_1445)) {
 x_1451 = x_1445;
} else {
 lean::inc(x_1449);
 lean::dec(x_1445);
 x_1451 = lean::box(0);
}
if (lean::is_scalar(x_1451)) {
 x_1452 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1452 = x_1451;
}
lean::cnstr_set(x_1452, 0, x_1449);
return x_1452;
}
else
{
obj* x_1453; obj* x_1456; obj* x_1458; obj* x_1461; obj* x_1464; obj* x_1468; 
x_1453 = lean::cnstr_get(x_1445, 0);
lean::inc(x_1453);
lean::dec(x_1445);
x_1456 = lean::cnstr_get(x_1453, 0);
lean::inc(x_1456);
x_1458 = lean::cnstr_get(x_1453, 1);
lean::inc(x_1458);
lean::dec(x_1453);
x_1461 = lean::cnstr_get(x_1441, 3);
lean::inc(x_1461);
lean::dec(x_1441);
x_1464 = lean::cnstr_get(x_1461, 1);
lean::inc(x_1464);
lean::dec(x_1461);
lean::inc(x_2);
x_1468 = l_Lean_Elaborator_toPexpr___main(x_1464, x_1, x_2, x_1458);
if (lean::obj_tag(x_1468) == 0)
{
obj* x_1472; obj* x_1474; obj* x_1475; 
lean::dec(x_1456);
lean::dec(x_0);
lean::dec(x_2);
x_1472 = lean::cnstr_get(x_1468, 0);
if (lean::is_exclusive(x_1468)) {
 x_1474 = x_1468;
} else {
 lean::inc(x_1472);
 lean::dec(x_1468);
 x_1474 = lean::box(0);
}
if (lean::is_scalar(x_1474)) {
 x_1475 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1475 = x_1474;
}
lean::cnstr_set(x_1475, 0, x_1472);
return x_1475;
}
else
{
obj* x_1476; obj* x_1478; obj* x_1479; obj* x_1481; obj* x_1483; obj* x_1484; uint8 x_1485; obj* x_1486; obj* x_1487; obj* x_1488; obj* x_1489; obj* x_1490; obj* x_1491; 
x_1476 = lean::cnstr_get(x_1468, 0);
if (lean::is_exclusive(x_1468)) {
 lean::cnstr_set(x_1468, 0, lean::box(0));
 x_1478 = x_1468;
} else {
 lean::inc(x_1476);
 lean::dec(x_1468);
 x_1478 = lean::box(0);
}
x_1479 = lean::cnstr_get(x_1476, 0);
x_1481 = lean::cnstr_get(x_1476, 1);
if (lean::is_exclusive(x_1476)) {
 lean::cnstr_set(x_1476, 0, lean::box(0));
 lean::cnstr_set(x_1476, 1, lean::box(0));
 x_1483 = x_1476;
} else {
 lean::inc(x_1479);
 lean::inc(x_1481);
 lean::dec(x_1476);
 x_1483 = lean::box(0);
}
x_1484 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1485 = 0;
x_1486 = l_Lean_Elaborator_toPexpr___main___closed__37;
x_1487 = lean_expr_mk_lambda(x_1484, x_1485, x_1456, x_1486);
x_1488 = lean_expr_mk_app(x_1487, x_1479);
x_1489 = l_Lean_Elaborator_toPexpr___main___closed__38;
x_1490 = l_Lean_Elaborator_Expr_mkAnnotation(x_1489, x_1488);
x_1491 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1491) == 0)
{
obj* x_1494; obj* x_1495; 
lean::dec(x_2);
if (lean::is_scalar(x_1483)) {
 x_1494 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1494 = x_1483;
}
lean::cnstr_set(x_1494, 0, x_1490);
lean::cnstr_set(x_1494, 1, x_1481);
if (lean::is_scalar(x_1478)) {
 x_1495 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1495 = x_1478;
}
lean::cnstr_set(x_1495, 0, x_1494);
return x_1495;
}
else
{
obj* x_1496; obj* x_1499; obj* x_1502; obj* x_1505; obj* x_1506; obj* x_1508; obj* x_1509; obj* x_1510; obj* x_1511; obj* x_1514; obj* x_1515; obj* x_1516; obj* x_1517; obj* x_1518; 
x_1496 = lean::cnstr_get(x_1491, 0);
lean::inc(x_1496);
lean::dec(x_1491);
x_1499 = lean::cnstr_get(x_2, 0);
lean::inc(x_1499);
lean::dec(x_2);
x_1502 = lean::cnstr_get(x_1499, 2);
lean::inc(x_1502);
lean::dec(x_1499);
x_1505 = l_Lean_FileMap_toPosition(x_1502, x_1496);
x_1506 = lean::cnstr_get(x_1505, 1);
lean::inc(x_1506);
x_1508 = lean::box(0);
x_1509 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1510 = l_Lean_KVMap_setNat(x_1508, x_1509, x_1506);
x_1511 = lean::cnstr_get(x_1505, 0);
lean::inc(x_1511);
lean::dec(x_1505);
x_1514 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1515 = l_Lean_KVMap_setNat(x_1510, x_1514, x_1511);
x_1516 = lean_expr_mk_mdata(x_1515, x_1490);
if (lean::is_scalar(x_1483)) {
 x_1517 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1517 = x_1483;
}
lean::cnstr_set(x_1517, 0, x_1516);
lean::cnstr_set(x_1517, 1, x_1481);
if (lean::is_scalar(x_1478)) {
 x_1518 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1518 = x_1478;
}
lean::cnstr_set(x_1518, 0, x_1517);
return x_1518;
}
}
}
}
}
else
{
obj* x_1520; obj* x_1521; obj* x_1525; obj* x_1526; 
lean::dec(x_10);
x_1520 = l_Lean_Parser_Term_have_HasView;
x_1521 = lean::cnstr_get(x_1520, 0);
lean::inc(x_1521);
lean::dec(x_1520);
lean::inc(x_0);
x_1525 = lean::apply_1(x_1521, x_0);
x_1526 = lean::cnstr_get(x_1525, 1);
lean::inc(x_1526);
if (lean::obj_tag(x_1526) == 0)
{
obj* x_1528; obj* x_1530; obj* x_1533; 
x_1528 = lean::cnstr_get(x_1525, 2);
lean::inc(x_1528);
x_1530 = lean::cnstr_get(x_1525, 5);
lean::inc(x_1530);
lean::inc(x_2);
x_1533 = l_Lean_Elaborator_toPexpr___main(x_1528, x_1, x_2, x_3);
if (lean::obj_tag(x_1533) == 0)
{
obj* x_1539; obj* x_1541; obj* x_1542; 
lean::dec(x_1525);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1530);
x_1539 = lean::cnstr_get(x_1533, 0);
if (lean::is_exclusive(x_1533)) {
 x_1541 = x_1533;
} else {
 lean::inc(x_1539);
 lean::dec(x_1533);
 x_1541 = lean::box(0);
}
if (lean::is_scalar(x_1541)) {
 x_1542 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1542 = x_1541;
}
lean::cnstr_set(x_1542, 0, x_1539);
return x_1542;
}
else
{
obj* x_1543; obj* x_1546; obj* x_1548; obj* x_1552; 
x_1543 = lean::cnstr_get(x_1533, 0);
lean::inc(x_1543);
lean::dec(x_1533);
x_1546 = lean::cnstr_get(x_1543, 0);
lean::inc(x_1546);
x_1548 = lean::cnstr_get(x_1543, 1);
lean::inc(x_1548);
lean::dec(x_1543);
lean::inc(x_2);
x_1552 = l_Lean_Elaborator_toPexpr___main(x_1530, x_1, x_2, x_1548);
if (lean::obj_tag(x_1552) == 0)
{
obj* x_1558; obj* x_1560; obj* x_1561; 
lean::dec(x_1525);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_1546);
lean::dec(x_2);
x_1558 = lean::cnstr_get(x_1552, 0);
if (lean::is_exclusive(x_1552)) {
 x_1560 = x_1552;
} else {
 lean::inc(x_1558);
 lean::dec(x_1552);
 x_1560 = lean::box(0);
}
if (lean::is_scalar(x_1560)) {
 x_1561 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1561 = x_1560;
}
lean::cnstr_set(x_1561, 0, x_1558);
return x_1561;
}
else
{
obj* x_1562; obj* x_1565; obj* x_1567; obj* x_1570; uint8 x_1571; obj* x_1572; obj* x_1573; 
x_1562 = lean::cnstr_get(x_1552, 0);
lean::inc(x_1562);
lean::dec(x_1552);
x_1565 = lean::cnstr_get(x_1562, 0);
lean::inc(x_1565);
x_1567 = lean::cnstr_get(x_1562, 1);
lean::inc(x_1567);
lean::dec(x_1562);
x_1570 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1571 = 0;
x_1572 = lean_expr_mk_lambda(x_1570, x_1571, x_1546, x_1565);
x_1573 = lean::cnstr_get(x_1525, 3);
lean::inc(x_1573);
lean::dec(x_1525);
if (lean::obj_tag(x_1573) == 0)
{
obj* x_1576; obj* x_1579; obj* x_1583; 
x_1576 = lean::cnstr_get(x_1573, 0);
lean::inc(x_1576);
lean::dec(x_1573);
x_1579 = lean::cnstr_get(x_1576, 1);
lean::inc(x_1579);
lean::dec(x_1576);
lean::inc(x_2);
x_1583 = l_Lean_Elaborator_toPexpr___main(x_1579, x_1, x_2, x_1567);
if (lean::obj_tag(x_1583) == 0)
{
obj* x_1588; obj* x_1590; obj* x_1591; 
lean::dec(x_1572);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1588 = lean::cnstr_get(x_1583, 0);
if (lean::is_exclusive(x_1583)) {
 x_1590 = x_1583;
} else {
 lean::inc(x_1588);
 lean::dec(x_1583);
 x_1590 = lean::box(0);
}
if (lean::is_scalar(x_1590)) {
 x_1591 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1591 = x_1590;
}
lean::cnstr_set(x_1591, 0, x_1588);
return x_1591;
}
else
{
obj* x_1592; obj* x_1595; obj* x_1597; obj* x_1599; obj* x_1600; obj* x_1601; obj* x_1602; obj* x_1603; 
x_1592 = lean::cnstr_get(x_1583, 0);
lean::inc(x_1592);
lean::dec(x_1583);
x_1595 = lean::cnstr_get(x_1592, 0);
x_1597 = lean::cnstr_get(x_1592, 1);
if (lean::is_exclusive(x_1592)) {
 x_1599 = x_1592;
} else {
 lean::inc(x_1595);
 lean::inc(x_1597);
 lean::dec(x_1592);
 x_1599 = lean::box(0);
}
x_1600 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1601 = l_Lean_Elaborator_Expr_mkAnnotation(x_1600, x_1572);
x_1602 = lean_expr_mk_app(x_1601, x_1595);
if (lean::is_scalar(x_1599)) {
 x_1603 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1603 = x_1599;
}
lean::cnstr_set(x_1603, 0, x_1602);
lean::cnstr_set(x_1603, 1, x_1597);
x_15 = x_1603;
goto lbl_16;
}
}
else
{
obj* x_1604; obj* x_1607; obj* x_1610; obj* x_1614; 
x_1604 = lean::cnstr_get(x_1573, 0);
lean::inc(x_1604);
lean::dec(x_1573);
x_1607 = lean::cnstr_get(x_1604, 1);
lean::inc(x_1607);
lean::dec(x_1604);
x_1610 = lean::cnstr_get(x_1607, 1);
lean::inc(x_1610);
lean::dec(x_1607);
lean::inc(x_2);
x_1614 = l_Lean_Elaborator_toPexpr___main(x_1610, x_1, x_2, x_1567);
if (lean::obj_tag(x_1614) == 0)
{
obj* x_1619; obj* x_1621; obj* x_1622; 
lean::dec(x_1572);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1619 = lean::cnstr_get(x_1614, 0);
if (lean::is_exclusive(x_1614)) {
 x_1621 = x_1614;
} else {
 lean::inc(x_1619);
 lean::dec(x_1614);
 x_1621 = lean::box(0);
}
if (lean::is_scalar(x_1621)) {
 x_1622 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1622 = x_1621;
}
lean::cnstr_set(x_1622, 0, x_1619);
return x_1622;
}
else
{
obj* x_1623; obj* x_1626; obj* x_1628; obj* x_1630; obj* x_1631; obj* x_1632; obj* x_1633; obj* x_1634; 
x_1623 = lean::cnstr_get(x_1614, 0);
lean::inc(x_1623);
lean::dec(x_1614);
x_1626 = lean::cnstr_get(x_1623, 0);
x_1628 = lean::cnstr_get(x_1623, 1);
if (lean::is_exclusive(x_1623)) {
 x_1630 = x_1623;
} else {
 lean::inc(x_1626);
 lean::inc(x_1628);
 lean::dec(x_1623);
 x_1630 = lean::box(0);
}
x_1631 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1632 = l_Lean_Elaborator_Expr_mkAnnotation(x_1631, x_1572);
x_1633 = lean_expr_mk_app(x_1632, x_1626);
if (lean::is_scalar(x_1630)) {
 x_1634 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1634 = x_1630;
}
lean::cnstr_set(x_1634, 0, x_1633);
lean::cnstr_set(x_1634, 1, x_1628);
x_15 = x_1634;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1635; obj* x_1637; obj* x_1639; obj* x_1642; obj* x_1645; obj* x_1647; 
x_1635 = lean::cnstr_get(x_1525, 2);
lean::inc(x_1635);
x_1637 = lean::cnstr_get(x_1525, 5);
lean::inc(x_1637);
x_1639 = lean::cnstr_get(x_1526, 0);
lean::inc(x_1639);
lean::dec(x_1526);
x_1642 = lean::cnstr_get(x_1639, 0);
lean::inc(x_1642);
lean::dec(x_1639);
x_1645 = l_Lean_Elaborator_mangleIdent(x_1642);
lean::inc(x_2);
x_1647 = l_Lean_Elaborator_toPexpr___main(x_1635, x_1, x_2, x_3);
if (lean::obj_tag(x_1647) == 0)
{
obj* x_1654; obj* x_1656; obj* x_1657; 
lean::dec(x_1525);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1645);
lean::dec(x_1637);
x_1654 = lean::cnstr_get(x_1647, 0);
if (lean::is_exclusive(x_1647)) {
 x_1656 = x_1647;
} else {
 lean::inc(x_1654);
 lean::dec(x_1647);
 x_1656 = lean::box(0);
}
if (lean::is_scalar(x_1656)) {
 x_1657 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1657 = x_1656;
}
lean::cnstr_set(x_1657, 0, x_1654);
return x_1657;
}
else
{
obj* x_1658; obj* x_1661; obj* x_1663; obj* x_1667; 
x_1658 = lean::cnstr_get(x_1647, 0);
lean::inc(x_1658);
lean::dec(x_1647);
x_1661 = lean::cnstr_get(x_1658, 0);
lean::inc(x_1661);
x_1663 = lean::cnstr_get(x_1658, 1);
lean::inc(x_1663);
lean::dec(x_1658);
lean::inc(x_2);
x_1667 = l_Lean_Elaborator_toPexpr___main(x_1637, x_1, x_2, x_1663);
if (lean::obj_tag(x_1667) == 0)
{
obj* x_1674; obj* x_1676; obj* x_1677; 
lean::dec(x_1525);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1645);
lean::dec(x_1661);
x_1674 = lean::cnstr_get(x_1667, 0);
if (lean::is_exclusive(x_1667)) {
 x_1676 = x_1667;
} else {
 lean::inc(x_1674);
 lean::dec(x_1667);
 x_1676 = lean::box(0);
}
if (lean::is_scalar(x_1676)) {
 x_1677 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1677 = x_1676;
}
lean::cnstr_set(x_1677, 0, x_1674);
return x_1677;
}
else
{
obj* x_1678; obj* x_1681; obj* x_1683; uint8 x_1686; obj* x_1687; obj* x_1688; 
x_1678 = lean::cnstr_get(x_1667, 0);
lean::inc(x_1678);
lean::dec(x_1667);
x_1681 = lean::cnstr_get(x_1678, 0);
lean::inc(x_1681);
x_1683 = lean::cnstr_get(x_1678, 1);
lean::inc(x_1683);
lean::dec(x_1678);
x_1686 = 0;
x_1687 = lean_expr_mk_lambda(x_1645, x_1686, x_1661, x_1681);
x_1688 = lean::cnstr_get(x_1525, 3);
lean::inc(x_1688);
lean::dec(x_1525);
if (lean::obj_tag(x_1688) == 0)
{
obj* x_1691; obj* x_1694; obj* x_1698; 
x_1691 = lean::cnstr_get(x_1688, 0);
lean::inc(x_1691);
lean::dec(x_1688);
x_1694 = lean::cnstr_get(x_1691, 1);
lean::inc(x_1694);
lean::dec(x_1691);
lean::inc(x_2);
x_1698 = l_Lean_Elaborator_toPexpr___main(x_1694, x_1, x_2, x_1683);
if (lean::obj_tag(x_1698) == 0)
{
obj* x_1703; obj* x_1705; obj* x_1706; 
lean::dec(x_1687);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1703 = lean::cnstr_get(x_1698, 0);
if (lean::is_exclusive(x_1698)) {
 x_1705 = x_1698;
} else {
 lean::inc(x_1703);
 lean::dec(x_1698);
 x_1705 = lean::box(0);
}
if (lean::is_scalar(x_1705)) {
 x_1706 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1706 = x_1705;
}
lean::cnstr_set(x_1706, 0, x_1703);
return x_1706;
}
else
{
obj* x_1707; obj* x_1710; obj* x_1712; obj* x_1714; obj* x_1715; obj* x_1716; obj* x_1717; obj* x_1718; 
x_1707 = lean::cnstr_get(x_1698, 0);
lean::inc(x_1707);
lean::dec(x_1698);
x_1710 = lean::cnstr_get(x_1707, 0);
x_1712 = lean::cnstr_get(x_1707, 1);
if (lean::is_exclusive(x_1707)) {
 x_1714 = x_1707;
} else {
 lean::inc(x_1710);
 lean::inc(x_1712);
 lean::dec(x_1707);
 x_1714 = lean::box(0);
}
x_1715 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1716 = l_Lean_Elaborator_Expr_mkAnnotation(x_1715, x_1687);
x_1717 = lean_expr_mk_app(x_1716, x_1710);
if (lean::is_scalar(x_1714)) {
 x_1718 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1718 = x_1714;
}
lean::cnstr_set(x_1718, 0, x_1717);
lean::cnstr_set(x_1718, 1, x_1712);
x_15 = x_1718;
goto lbl_16;
}
}
else
{
obj* x_1719; obj* x_1722; obj* x_1725; obj* x_1729; 
x_1719 = lean::cnstr_get(x_1688, 0);
lean::inc(x_1719);
lean::dec(x_1688);
x_1722 = lean::cnstr_get(x_1719, 1);
lean::inc(x_1722);
lean::dec(x_1719);
x_1725 = lean::cnstr_get(x_1722, 1);
lean::inc(x_1725);
lean::dec(x_1722);
lean::inc(x_2);
x_1729 = l_Lean_Elaborator_toPexpr___main(x_1725, x_1, x_2, x_1683);
if (lean::obj_tag(x_1729) == 0)
{
obj* x_1734; obj* x_1736; obj* x_1737; 
lean::dec(x_1687);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1734 = lean::cnstr_get(x_1729, 0);
if (lean::is_exclusive(x_1729)) {
 x_1736 = x_1729;
} else {
 lean::inc(x_1734);
 lean::dec(x_1729);
 x_1736 = lean::box(0);
}
if (lean::is_scalar(x_1736)) {
 x_1737 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1737 = x_1736;
}
lean::cnstr_set(x_1737, 0, x_1734);
return x_1737;
}
else
{
obj* x_1738; obj* x_1741; obj* x_1743; obj* x_1745; obj* x_1746; obj* x_1747; obj* x_1748; obj* x_1749; 
x_1738 = lean::cnstr_get(x_1729, 0);
lean::inc(x_1738);
lean::dec(x_1729);
x_1741 = lean::cnstr_get(x_1738, 0);
x_1743 = lean::cnstr_get(x_1738, 1);
if (lean::is_exclusive(x_1738)) {
 x_1745 = x_1738;
} else {
 lean::inc(x_1741);
 lean::inc(x_1743);
 lean::dec(x_1738);
 x_1745 = lean::box(0);
}
x_1746 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1747 = l_Lean_Elaborator_Expr_mkAnnotation(x_1746, x_1687);
x_1748 = lean_expr_mk_app(x_1747, x_1741);
if (lean::is_scalar(x_1745)) {
 x_1749 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1749 = x_1745;
}
lean::cnstr_set(x_1749, 0, x_1748);
lean::cnstr_set(x_1749, 1, x_1743);
x_15 = x_1749;
goto lbl_16;
}
}
}
}
}
}
}
else
{
obj* x_1752; 
lean::dec(x_8);
lean::dec(x_10);
x_1752 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1752) == 0)
{
obj* x_1755; obj* x_1756; obj* x_1757; 
lean::dec(x_2);
x_1755 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1756 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1756, 0, x_1755);
lean::cnstr_set(x_1756, 1, x_3);
x_1757 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1757, 0, x_1756);
return x_1757;
}
else
{
obj* x_1758; obj* x_1761; obj* x_1764; obj* x_1767; obj* x_1768; obj* x_1770; obj* x_1771; obj* x_1772; obj* x_1773; obj* x_1776; obj* x_1777; obj* x_1778; obj* x_1779; obj* x_1780; obj* x_1781; 
x_1758 = lean::cnstr_get(x_1752, 0);
lean::inc(x_1758);
lean::dec(x_1752);
x_1761 = lean::cnstr_get(x_2, 0);
lean::inc(x_1761);
lean::dec(x_2);
x_1764 = lean::cnstr_get(x_1761, 2);
lean::inc(x_1764);
lean::dec(x_1761);
x_1767 = l_Lean_FileMap_toPosition(x_1764, x_1758);
x_1768 = lean::cnstr_get(x_1767, 1);
lean::inc(x_1768);
x_1770 = lean::box(0);
x_1771 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1772 = l_Lean_KVMap_setNat(x_1770, x_1771, x_1768);
x_1773 = lean::cnstr_get(x_1767, 0);
lean::inc(x_1773);
lean::dec(x_1767);
x_1776 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1777 = l_Lean_KVMap_setNat(x_1772, x_1776, x_1773);
x_1778 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1779 = lean_expr_mk_mdata(x_1777, x_1778);
x_1780 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1780, 0, x_1779);
lean::cnstr_set(x_1780, 1, x_3);
x_1781 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1781, 0, x_1780);
return x_1781;
}
}
}
else
{
obj* x_1784; obj* x_1785; obj* x_1789; obj* x_1790; obj* x_1793; obj* x_1794; obj* x_1795; obj* x_1797; 
lean::dec(x_8);
lean::dec(x_10);
x_1784 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_1785 = lean::cnstr_get(x_1784, 0);
lean::inc(x_1785);
lean::dec(x_1784);
lean::inc(x_0);
x_1789 = lean::apply_1(x_1785, x_0);
x_1790 = lean::cnstr_get(x_1789, 1);
lean::inc(x_1790);
lean::dec(x_1789);
x_1793 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_1790);
x_1794 = l_Lean_Expander_getOptType___main___closed__1;
x_1795 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_1794, x_1793);
lean::inc(x_2);
x_1797 = l_Lean_Elaborator_toPexpr___main(x_1795, x_1, x_2, x_3);
if (lean::obj_tag(x_1797) == 0)
{
obj* x_1800; obj* x_1802; obj* x_1803; 
lean::dec(x_0);
lean::dec(x_2);
x_1800 = lean::cnstr_get(x_1797, 0);
if (lean::is_exclusive(x_1797)) {
 x_1802 = x_1797;
} else {
 lean::inc(x_1800);
 lean::dec(x_1797);
 x_1802 = lean::box(0);
}
if (lean::is_scalar(x_1802)) {
 x_1803 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1803 = x_1802;
}
lean::cnstr_set(x_1803, 0, x_1800);
return x_1803;
}
else
{
obj* x_1804; obj* x_1806; obj* x_1807; obj* x_1809; obj* x_1811; obj* x_1812; obj* x_1813; obj* x_1814; 
x_1804 = lean::cnstr_get(x_1797, 0);
if (lean::is_exclusive(x_1797)) {
 lean::cnstr_set(x_1797, 0, lean::box(0));
 x_1806 = x_1797;
} else {
 lean::inc(x_1804);
 lean::dec(x_1797);
 x_1806 = lean::box(0);
}
x_1807 = lean::cnstr_get(x_1804, 0);
x_1809 = lean::cnstr_get(x_1804, 1);
if (lean::is_exclusive(x_1804)) {
 lean::cnstr_set(x_1804, 0, lean::box(0));
 lean::cnstr_set(x_1804, 1, lean::box(0));
 x_1811 = x_1804;
} else {
 lean::inc(x_1807);
 lean::inc(x_1809);
 lean::dec(x_1804);
 x_1811 = lean::box(0);
}
x_1812 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1813 = l_Lean_Elaborator_Expr_mkAnnotation(x_1812, x_1807);
x_1814 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1814) == 0)
{
obj* x_1817; obj* x_1818; 
lean::dec(x_2);
if (lean::is_scalar(x_1811)) {
 x_1817 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1817 = x_1811;
}
lean::cnstr_set(x_1817, 0, x_1813);
lean::cnstr_set(x_1817, 1, x_1809);
if (lean::is_scalar(x_1806)) {
 x_1818 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1818 = x_1806;
}
lean::cnstr_set(x_1818, 0, x_1817);
return x_1818;
}
else
{
obj* x_1819; obj* x_1822; obj* x_1825; obj* x_1828; obj* x_1829; obj* x_1831; obj* x_1832; obj* x_1833; obj* x_1834; obj* x_1837; obj* x_1838; obj* x_1839; obj* x_1840; obj* x_1841; 
x_1819 = lean::cnstr_get(x_1814, 0);
lean::inc(x_1819);
lean::dec(x_1814);
x_1822 = lean::cnstr_get(x_2, 0);
lean::inc(x_1822);
lean::dec(x_2);
x_1825 = lean::cnstr_get(x_1822, 2);
lean::inc(x_1825);
lean::dec(x_1822);
x_1828 = l_Lean_FileMap_toPosition(x_1825, x_1819);
x_1829 = lean::cnstr_get(x_1828, 1);
lean::inc(x_1829);
x_1831 = lean::box(0);
x_1832 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1833 = l_Lean_KVMap_setNat(x_1831, x_1832, x_1829);
x_1834 = lean::cnstr_get(x_1828, 0);
lean::inc(x_1834);
lean::dec(x_1828);
x_1837 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1838 = l_Lean_KVMap_setNat(x_1833, x_1837, x_1834);
x_1839 = lean_expr_mk_mdata(x_1838, x_1813);
if (lean::is_scalar(x_1811)) {
 x_1840 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1840 = x_1811;
}
lean::cnstr_set(x_1840, 0, x_1839);
lean::cnstr_set(x_1840, 1, x_1809);
if (lean::is_scalar(x_1806)) {
 x_1841 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1841 = x_1806;
}
lean::cnstr_set(x_1841, 0, x_1840);
return x_1841;
}
}
}
}
else
{
obj* x_1844; obj* x_1845; obj* x_1849; obj* x_1850; obj* x_1851; obj* x_1854; obj* x_1856; 
lean::dec(x_8);
lean::dec(x_10);
x_1844 = l_Lean_Parser_Term_sortApp_HasView;
x_1845 = lean::cnstr_get(x_1844, 0);
lean::inc(x_1845);
lean::dec(x_1844);
lean::inc(x_0);
x_1849 = lean::apply_1(x_1845, x_0);
x_1850 = l_Lean_Parser_Term_sort_HasView;
x_1851 = lean::cnstr_get(x_1850, 0);
lean::inc(x_1851);
lean::dec(x_1850);
x_1854 = lean::cnstr_get(x_1849, 0);
lean::inc(x_1854);
x_1856 = lean::apply_1(x_1851, x_1854);
if (lean::obj_tag(x_1856) == 0)
{
obj* x_1858; obj* x_1862; 
lean::dec(x_1856);
x_1858 = lean::cnstr_get(x_1849, 1);
lean::inc(x_1858);
lean::dec(x_1849);
lean::inc(x_2);
x_1862 = l_Lean_Elaborator_toLevel___main(x_1858, x_1, x_2, x_3);
if (lean::obj_tag(x_1862) == 0)
{
obj* x_1865; obj* x_1867; obj* x_1868; 
lean::dec(x_0);
lean::dec(x_2);
x_1865 = lean::cnstr_get(x_1862, 0);
if (lean::is_exclusive(x_1862)) {
 x_1867 = x_1862;
} else {
 lean::inc(x_1865);
 lean::dec(x_1862);
 x_1867 = lean::box(0);
}
if (lean::is_scalar(x_1867)) {
 x_1868 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1868 = x_1867;
}
lean::cnstr_set(x_1868, 0, x_1865);
return x_1868;
}
else
{
obj* x_1869; obj* x_1871; obj* x_1872; obj* x_1874; obj* x_1876; obj* x_1877; obj* x_1878; 
x_1869 = lean::cnstr_get(x_1862, 0);
if (lean::is_exclusive(x_1862)) {
 lean::cnstr_set(x_1862, 0, lean::box(0));
 x_1871 = x_1862;
} else {
 lean::inc(x_1869);
 lean::dec(x_1862);
 x_1871 = lean::box(0);
}
x_1872 = lean::cnstr_get(x_1869, 0);
x_1874 = lean::cnstr_get(x_1869, 1);
if (lean::is_exclusive(x_1869)) {
 lean::cnstr_set(x_1869, 0, lean::box(0));
 lean::cnstr_set(x_1869, 1, lean::box(0));
 x_1876 = x_1869;
} else {
 lean::inc(x_1872);
 lean::inc(x_1874);
 lean::dec(x_1869);
 x_1876 = lean::box(0);
}
x_1877 = lean_expr_mk_sort(x_1872);
x_1878 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1878) == 0)
{
obj* x_1881; obj* x_1882; 
lean::dec(x_2);
if (lean::is_scalar(x_1876)) {
 x_1881 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1881 = x_1876;
}
lean::cnstr_set(x_1881, 0, x_1877);
lean::cnstr_set(x_1881, 1, x_1874);
if (lean::is_scalar(x_1871)) {
 x_1882 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1882 = x_1871;
}
lean::cnstr_set(x_1882, 0, x_1881);
return x_1882;
}
else
{
obj* x_1883; obj* x_1886; obj* x_1889; obj* x_1892; obj* x_1893; obj* x_1895; obj* x_1896; obj* x_1897; obj* x_1898; obj* x_1901; obj* x_1902; obj* x_1903; obj* x_1904; obj* x_1905; 
x_1883 = lean::cnstr_get(x_1878, 0);
lean::inc(x_1883);
lean::dec(x_1878);
x_1886 = lean::cnstr_get(x_2, 0);
lean::inc(x_1886);
lean::dec(x_2);
x_1889 = lean::cnstr_get(x_1886, 2);
lean::inc(x_1889);
lean::dec(x_1886);
x_1892 = l_Lean_FileMap_toPosition(x_1889, x_1883);
x_1893 = lean::cnstr_get(x_1892, 1);
lean::inc(x_1893);
x_1895 = lean::box(0);
x_1896 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1897 = l_Lean_KVMap_setNat(x_1895, x_1896, x_1893);
x_1898 = lean::cnstr_get(x_1892, 0);
lean::inc(x_1898);
lean::dec(x_1892);
x_1901 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1902 = l_Lean_KVMap_setNat(x_1897, x_1901, x_1898);
x_1903 = lean_expr_mk_mdata(x_1902, x_1877);
if (lean::is_scalar(x_1876)) {
 x_1904 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1904 = x_1876;
}
lean::cnstr_set(x_1904, 0, x_1903);
lean::cnstr_set(x_1904, 1, x_1874);
if (lean::is_scalar(x_1871)) {
 x_1905 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1905 = x_1871;
}
lean::cnstr_set(x_1905, 0, x_1904);
return x_1905;
}
}
}
else
{
obj* x_1907; obj* x_1911; 
lean::dec(x_1856);
x_1907 = lean::cnstr_get(x_1849, 1);
lean::inc(x_1907);
lean::dec(x_1849);
lean::inc(x_2);
x_1911 = l_Lean_Elaborator_toLevel___main(x_1907, x_1, x_2, x_3);
if (lean::obj_tag(x_1911) == 0)
{
obj* x_1914; obj* x_1916; obj* x_1917; 
lean::dec(x_0);
lean::dec(x_2);
x_1914 = lean::cnstr_get(x_1911, 0);
if (lean::is_exclusive(x_1911)) {
 x_1916 = x_1911;
} else {
 lean::inc(x_1914);
 lean::dec(x_1911);
 x_1916 = lean::box(0);
}
if (lean::is_scalar(x_1916)) {
 x_1917 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1917 = x_1916;
}
lean::cnstr_set(x_1917, 0, x_1914);
return x_1917;
}
else
{
obj* x_1918; obj* x_1920; obj* x_1921; obj* x_1923; obj* x_1925; obj* x_1926; obj* x_1927; obj* x_1928; 
x_1918 = lean::cnstr_get(x_1911, 0);
if (lean::is_exclusive(x_1911)) {
 lean::cnstr_set(x_1911, 0, lean::box(0));
 x_1920 = x_1911;
} else {
 lean::inc(x_1918);
 lean::dec(x_1911);
 x_1920 = lean::box(0);
}
x_1921 = lean::cnstr_get(x_1918, 0);
x_1923 = lean::cnstr_get(x_1918, 1);
if (lean::is_exclusive(x_1918)) {
 lean::cnstr_set(x_1918, 0, lean::box(0));
 lean::cnstr_set(x_1918, 1, lean::box(0));
 x_1925 = x_1918;
} else {
 lean::inc(x_1921);
 lean::inc(x_1923);
 lean::dec(x_1918);
 x_1925 = lean::box(0);
}
x_1926 = level_mk_succ(x_1921);
x_1927 = lean_expr_mk_sort(x_1926);
x_1928 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1928) == 0)
{
obj* x_1931; obj* x_1932; 
lean::dec(x_2);
if (lean::is_scalar(x_1925)) {
 x_1931 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1931 = x_1925;
}
lean::cnstr_set(x_1931, 0, x_1927);
lean::cnstr_set(x_1931, 1, x_1923);
if (lean::is_scalar(x_1920)) {
 x_1932 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1932 = x_1920;
}
lean::cnstr_set(x_1932, 0, x_1931);
return x_1932;
}
else
{
obj* x_1933; obj* x_1936; obj* x_1939; obj* x_1942; obj* x_1943; obj* x_1945; obj* x_1946; obj* x_1947; obj* x_1948; obj* x_1951; obj* x_1952; obj* x_1953; obj* x_1954; obj* x_1955; 
x_1933 = lean::cnstr_get(x_1928, 0);
lean::inc(x_1933);
lean::dec(x_1928);
x_1936 = lean::cnstr_get(x_2, 0);
lean::inc(x_1936);
lean::dec(x_2);
x_1939 = lean::cnstr_get(x_1936, 2);
lean::inc(x_1939);
lean::dec(x_1936);
x_1942 = l_Lean_FileMap_toPosition(x_1939, x_1933);
x_1943 = lean::cnstr_get(x_1942, 1);
lean::inc(x_1943);
x_1945 = lean::box(0);
x_1946 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1947 = l_Lean_KVMap_setNat(x_1945, x_1946, x_1943);
x_1948 = lean::cnstr_get(x_1942, 0);
lean::inc(x_1948);
lean::dec(x_1942);
x_1951 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1952 = l_Lean_KVMap_setNat(x_1947, x_1951, x_1948);
x_1953 = lean_expr_mk_mdata(x_1952, x_1927);
if (lean::is_scalar(x_1925)) {
 x_1954 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1954 = x_1925;
}
lean::cnstr_set(x_1954, 0, x_1953);
lean::cnstr_set(x_1954, 1, x_1923);
if (lean::is_scalar(x_1920)) {
 x_1955 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1955 = x_1920;
}
lean::cnstr_set(x_1955, 0, x_1954);
return x_1955;
}
}
}
}
}
else
{
obj* x_1958; obj* x_1959; obj* x_1963; 
lean::dec(x_8);
lean::dec(x_10);
x_1958 = l_Lean_Parser_Term_sort_HasView;
x_1959 = lean::cnstr_get(x_1958, 0);
lean::inc(x_1959);
lean::dec(x_1958);
lean::inc(x_0);
x_1963 = lean::apply_1(x_1959, x_0);
if (lean::obj_tag(x_1963) == 0)
{
obj* x_1965; 
lean::dec(x_1963);
x_1965 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1965) == 0)
{
obj* x_1968; obj* x_1969; obj* x_1970; 
lean::dec(x_2);
x_1968 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_1969 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1969, 0, x_1968);
lean::cnstr_set(x_1969, 1, x_3);
x_1970 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1970, 0, x_1969);
return x_1970;
}
else
{
obj* x_1971; obj* x_1974; obj* x_1977; obj* x_1980; obj* x_1981; obj* x_1983; obj* x_1984; obj* x_1985; obj* x_1986; obj* x_1989; obj* x_1990; obj* x_1991; obj* x_1992; obj* x_1993; obj* x_1994; 
x_1971 = lean::cnstr_get(x_1965, 0);
lean::inc(x_1971);
lean::dec(x_1965);
x_1974 = lean::cnstr_get(x_2, 0);
lean::inc(x_1974);
lean::dec(x_2);
x_1977 = lean::cnstr_get(x_1974, 2);
lean::inc(x_1977);
lean::dec(x_1974);
x_1980 = l_Lean_FileMap_toPosition(x_1977, x_1971);
x_1981 = lean::cnstr_get(x_1980, 1);
lean::inc(x_1981);
x_1983 = lean::box(0);
x_1984 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1985 = l_Lean_KVMap_setNat(x_1983, x_1984, x_1981);
x_1986 = lean::cnstr_get(x_1980, 0);
lean::inc(x_1986);
lean::dec(x_1980);
x_1989 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1990 = l_Lean_KVMap_setNat(x_1985, x_1989, x_1986);
x_1991 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_1992 = lean_expr_mk_mdata(x_1990, x_1991);
x_1993 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1993, 0, x_1992);
lean::cnstr_set(x_1993, 1, x_3);
x_1994 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1994, 0, x_1993);
return x_1994;
}
}
else
{
obj* x_1996; 
lean::dec(x_1963);
x_1996 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1996) == 0)
{
obj* x_1999; obj* x_2000; obj* x_2001; 
lean::dec(x_2);
x_1999 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2000 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2000, 0, x_1999);
lean::cnstr_set(x_2000, 1, x_3);
x_2001 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2001, 0, x_2000);
return x_2001;
}
else
{
obj* x_2002; obj* x_2005; obj* x_2008; obj* x_2011; obj* x_2012; obj* x_2014; obj* x_2015; obj* x_2016; obj* x_2017; obj* x_2020; obj* x_2021; obj* x_2022; obj* x_2023; obj* x_2024; obj* x_2025; 
x_2002 = lean::cnstr_get(x_1996, 0);
lean::inc(x_2002);
lean::dec(x_1996);
x_2005 = lean::cnstr_get(x_2, 0);
lean::inc(x_2005);
lean::dec(x_2);
x_2008 = lean::cnstr_get(x_2005, 2);
lean::inc(x_2008);
lean::dec(x_2005);
x_2011 = l_Lean_FileMap_toPosition(x_2008, x_2002);
x_2012 = lean::cnstr_get(x_2011, 1);
lean::inc(x_2012);
x_2014 = lean::box(0);
x_2015 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2016 = l_Lean_KVMap_setNat(x_2014, x_2015, x_2012);
x_2017 = lean::cnstr_get(x_2011, 0);
lean::inc(x_2017);
lean::dec(x_2011);
x_2020 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2021 = l_Lean_KVMap_setNat(x_2016, x_2020, x_2017);
x_2022 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2023 = lean_expr_mk_mdata(x_2021, x_2022);
x_2024 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2024, 0, x_2023);
lean::cnstr_set(x_2024, 1, x_3);
x_2025 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2025, 0, x_2024);
return x_2025;
}
}
}
}
else
{
obj* x_2027; obj* x_2028; obj* x_2032; obj* x_2033; 
lean::dec(x_10);
x_2027 = l_Lean_Parser_Term_pi_HasView;
x_2028 = lean::cnstr_get(x_2027, 0);
lean::inc(x_2028);
lean::dec(x_2027);
lean::inc(x_0);
x_2032 = lean::apply_1(x_2028, x_0);
x_2033 = lean::cnstr_get(x_2032, 1);
lean::inc(x_2033);
if (lean::obj_tag(x_2033) == 0)
{
obj* x_2038; obj* x_2039; obj* x_2041; 
lean::dec(x_2032);
lean::dec(x_2033);
lean::inc(x_0);
x_2038 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2038, 0, x_0);
x_2039 = l_Lean_Elaborator_toPexpr___main___closed__43;
lean::inc(x_2);
x_2041 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2038, x_2039, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2038);
if (lean::obj_tag(x_2041) == 0)
{
obj* x_2047; obj* x_2049; obj* x_2050; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2047 = lean::cnstr_get(x_2041, 0);
if (lean::is_exclusive(x_2041)) {
 x_2049 = x_2041;
} else {
 lean::inc(x_2047);
 lean::dec(x_2041);
 x_2049 = lean::box(0);
}
if (lean::is_scalar(x_2049)) {
 x_2050 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2050 = x_2049;
}
lean::cnstr_set(x_2050, 0, x_2047);
return x_2050;
}
else
{
obj* x_2051; 
x_2051 = lean::cnstr_get(x_2041, 0);
lean::inc(x_2051);
lean::dec(x_2041);
x_15 = x_2051;
goto lbl_16;
}
}
else
{
obj* x_2054; obj* x_2057; obj* x_2058; obj* x_2060; obj* x_2063; obj* x_2065; obj* x_2068; obj* x_2072; 
x_2054 = lean::cnstr_get(x_2033, 0);
lean::inc(x_2054);
lean::dec(x_2033);
x_2057 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2054);
x_2058 = lean::cnstr_get(x_2057, 1);
lean::inc(x_2058);
x_2060 = lean::cnstr_get(x_2057, 0);
lean::inc(x_2060);
lean::dec(x_2057);
x_2063 = lean::cnstr_get(x_2058, 0);
lean::inc(x_2063);
x_2065 = lean::cnstr_get(x_2058, 1);
lean::inc(x_2065);
lean::dec(x_2058);
x_2068 = lean::cnstr_get(x_2032, 3);
lean::inc(x_2068);
lean::dec(x_2032);
lean::inc(x_2);
x_2072 = l_Lean_Elaborator_toPexpr___main(x_2065, x_1, x_2, x_3);
if (lean::obj_tag(x_2072) == 0)
{
obj* x_2079; obj* x_2081; obj* x_2082; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2063);
lean::dec(x_2060);
lean::dec(x_2068);
x_2079 = lean::cnstr_get(x_2072, 0);
if (lean::is_exclusive(x_2072)) {
 x_2081 = x_2072;
} else {
 lean::inc(x_2079);
 lean::dec(x_2072);
 x_2081 = lean::box(0);
}
if (lean::is_scalar(x_2081)) {
 x_2082 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2082 = x_2081;
}
lean::cnstr_set(x_2082, 0, x_2079);
return x_2082;
}
else
{
obj* x_2083; obj* x_2086; obj* x_2088; obj* x_2092; 
x_2083 = lean::cnstr_get(x_2072, 0);
lean::inc(x_2083);
lean::dec(x_2072);
x_2086 = lean::cnstr_get(x_2083, 0);
lean::inc(x_2086);
x_2088 = lean::cnstr_get(x_2083, 1);
lean::inc(x_2088);
lean::dec(x_2083);
lean::inc(x_2);
x_2092 = l_Lean_Elaborator_toPexpr___main(x_2068, x_1, x_2, x_2088);
if (lean::obj_tag(x_2092) == 0)
{
obj* x_2099; obj* x_2101; obj* x_2102; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2063);
lean::dec(x_2060);
lean::dec(x_2086);
x_2099 = lean::cnstr_get(x_2092, 0);
if (lean::is_exclusive(x_2092)) {
 x_2101 = x_2092;
} else {
 lean::inc(x_2099);
 lean::dec(x_2092);
 x_2101 = lean::box(0);
}
if (lean::is_scalar(x_2101)) {
 x_2102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2102 = x_2101;
}
lean::cnstr_set(x_2102, 0, x_2099);
return x_2102;
}
else
{
obj* x_2103; obj* x_2106; obj* x_2108; obj* x_2110; obj* x_2111; uint8 x_2112; obj* x_2113; obj* x_2114; 
x_2103 = lean::cnstr_get(x_2092, 0);
lean::inc(x_2103);
lean::dec(x_2092);
x_2106 = lean::cnstr_get(x_2103, 0);
x_2108 = lean::cnstr_get(x_2103, 1);
if (lean::is_exclusive(x_2103)) {
 x_2110 = x_2103;
} else {
 lean::inc(x_2106);
 lean::inc(x_2108);
 lean::dec(x_2103);
 x_2110 = lean::box(0);
}
x_2111 = l_Lean_Elaborator_mangleIdent(x_2063);
x_2112 = lean::unbox(x_2060);
x_2113 = lean_expr_mk_pi(x_2111, x_2112, x_2086, x_2106);
if (lean::is_scalar(x_2110)) {
 x_2114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2114 = x_2110;
}
lean::cnstr_set(x_2114, 0, x_2113);
lean::cnstr_set(x_2114, 1, x_2108);
x_15 = x_2114;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2116; obj* x_2117; obj* x_2121; obj* x_2122; 
lean::dec(x_10);
x_2116 = l_Lean_Parser_Term_lambda_HasView;
x_2117 = lean::cnstr_get(x_2116, 0);
lean::inc(x_2117);
lean::dec(x_2116);
lean::inc(x_0);
x_2121 = lean::apply_1(x_2117, x_0);
x_2122 = lean::cnstr_get(x_2121, 1);
lean::inc(x_2122);
if (lean::obj_tag(x_2122) == 0)
{
obj* x_2127; obj* x_2128; obj* x_2130; 
lean::dec(x_2121);
lean::dec(x_2122);
lean::inc(x_0);
x_2127 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2127, 0, x_0);
x_2128 = l_Lean_Elaborator_toPexpr___main___closed__44;
lean::inc(x_2);
x_2130 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2127, x_2128, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2127);
if (lean::obj_tag(x_2130) == 0)
{
obj* x_2136; obj* x_2138; obj* x_2139; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2136 = lean::cnstr_get(x_2130, 0);
if (lean::is_exclusive(x_2130)) {
 x_2138 = x_2130;
} else {
 lean::inc(x_2136);
 lean::dec(x_2130);
 x_2138 = lean::box(0);
}
if (lean::is_scalar(x_2138)) {
 x_2139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2139 = x_2138;
}
lean::cnstr_set(x_2139, 0, x_2136);
return x_2139;
}
else
{
obj* x_2140; 
x_2140 = lean::cnstr_get(x_2130, 0);
lean::inc(x_2140);
lean::dec(x_2130);
x_15 = x_2140;
goto lbl_16;
}
}
else
{
obj* x_2143; obj* x_2146; obj* x_2147; obj* x_2149; obj* x_2152; obj* x_2154; obj* x_2157; obj* x_2161; 
x_2143 = lean::cnstr_get(x_2122, 0);
lean::inc(x_2143);
lean::dec(x_2122);
x_2146 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2143);
x_2147 = lean::cnstr_get(x_2146, 1);
lean::inc(x_2147);
x_2149 = lean::cnstr_get(x_2146, 0);
lean::inc(x_2149);
lean::dec(x_2146);
x_2152 = lean::cnstr_get(x_2147, 0);
lean::inc(x_2152);
x_2154 = lean::cnstr_get(x_2147, 1);
lean::inc(x_2154);
lean::dec(x_2147);
x_2157 = lean::cnstr_get(x_2121, 3);
lean::inc(x_2157);
lean::dec(x_2121);
lean::inc(x_2);
x_2161 = l_Lean_Elaborator_toPexpr___main(x_2154, x_1, x_2, x_3);
if (lean::obj_tag(x_2161) == 0)
{
obj* x_2168; obj* x_2170; obj* x_2171; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2149);
lean::dec(x_2152);
lean::dec(x_2157);
x_2168 = lean::cnstr_get(x_2161, 0);
if (lean::is_exclusive(x_2161)) {
 x_2170 = x_2161;
} else {
 lean::inc(x_2168);
 lean::dec(x_2161);
 x_2170 = lean::box(0);
}
if (lean::is_scalar(x_2170)) {
 x_2171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2171 = x_2170;
}
lean::cnstr_set(x_2171, 0, x_2168);
return x_2171;
}
else
{
obj* x_2172; obj* x_2175; obj* x_2177; obj* x_2181; 
x_2172 = lean::cnstr_get(x_2161, 0);
lean::inc(x_2172);
lean::dec(x_2161);
x_2175 = lean::cnstr_get(x_2172, 0);
lean::inc(x_2175);
x_2177 = lean::cnstr_get(x_2172, 1);
lean::inc(x_2177);
lean::dec(x_2172);
lean::inc(x_2);
x_2181 = l_Lean_Elaborator_toPexpr___main(x_2157, x_1, x_2, x_2177);
if (lean::obj_tag(x_2181) == 0)
{
obj* x_2188; obj* x_2190; obj* x_2191; 
lean::dec(x_2175);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2149);
lean::dec(x_2152);
x_2188 = lean::cnstr_get(x_2181, 0);
if (lean::is_exclusive(x_2181)) {
 x_2190 = x_2181;
} else {
 lean::inc(x_2188);
 lean::dec(x_2181);
 x_2190 = lean::box(0);
}
if (lean::is_scalar(x_2190)) {
 x_2191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2191 = x_2190;
}
lean::cnstr_set(x_2191, 0, x_2188);
return x_2191;
}
else
{
obj* x_2192; obj* x_2195; obj* x_2197; obj* x_2199; obj* x_2200; uint8 x_2201; obj* x_2202; obj* x_2203; 
x_2192 = lean::cnstr_get(x_2181, 0);
lean::inc(x_2192);
lean::dec(x_2181);
x_2195 = lean::cnstr_get(x_2192, 0);
x_2197 = lean::cnstr_get(x_2192, 1);
if (lean::is_exclusive(x_2192)) {
 x_2199 = x_2192;
} else {
 lean::inc(x_2195);
 lean::inc(x_2197);
 lean::dec(x_2192);
 x_2199 = lean::box(0);
}
x_2200 = l_Lean_Elaborator_mangleIdent(x_2152);
x_2201 = lean::unbox(x_2149);
x_2202 = lean_expr_mk_lambda(x_2200, x_2201, x_2175, x_2195);
if (lean::is_scalar(x_2199)) {
 x_2203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2203 = x_2199;
}
lean::cnstr_set(x_2203, 0, x_2202);
lean::cnstr_set(x_2203, 1, x_2197);
x_15 = x_2203;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2206; obj* x_2207; obj* x_2210; obj* x_2211; obj* x_2213; obj* x_2217; 
lean::dec(x_8);
lean::dec(x_10);
x_2206 = l_Lean_Parser_Term_app_HasView;
x_2207 = lean::cnstr_get(x_2206, 0);
lean::inc(x_2207);
lean::dec(x_2206);
x_2210 = lean::apply_1(x_2207, x_0);
x_2211 = lean::cnstr_get(x_2210, 0);
lean::inc(x_2211);
x_2213 = lean::cnstr_get(x_2210, 1);
lean::inc(x_2213);
lean::dec(x_2210);
lean::inc(x_2);
x_2217 = l_Lean_Elaborator_toPexpr___main(x_2211, x_1, x_2, x_3);
if (lean::obj_tag(x_2217) == 0)
{
obj* x_2220; obj* x_2222; obj* x_2223; 
lean::dec(x_2213);
lean::dec(x_2);
x_2220 = lean::cnstr_get(x_2217, 0);
if (lean::is_exclusive(x_2217)) {
 x_2222 = x_2217;
} else {
 lean::inc(x_2220);
 lean::dec(x_2217);
 x_2222 = lean::box(0);
}
if (lean::is_scalar(x_2222)) {
 x_2223 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2223 = x_2222;
}
lean::cnstr_set(x_2223, 0, x_2220);
return x_2223;
}
else
{
obj* x_2224; obj* x_2227; obj* x_2229; obj* x_2232; 
x_2224 = lean::cnstr_get(x_2217, 0);
lean::inc(x_2224);
lean::dec(x_2217);
x_2227 = lean::cnstr_get(x_2224, 0);
lean::inc(x_2227);
x_2229 = lean::cnstr_get(x_2224, 1);
lean::inc(x_2229);
lean::dec(x_2224);
x_2232 = l_Lean_Elaborator_toPexpr___main(x_2213, x_1, x_2, x_2229);
if (lean::obj_tag(x_2232) == 0)
{
obj* x_2234; obj* x_2236; obj* x_2237; 
lean::dec(x_2227);
x_2234 = lean::cnstr_get(x_2232, 0);
if (lean::is_exclusive(x_2232)) {
 x_2236 = x_2232;
} else {
 lean::inc(x_2234);
 lean::dec(x_2232);
 x_2236 = lean::box(0);
}
if (lean::is_scalar(x_2236)) {
 x_2237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2237 = x_2236;
}
lean::cnstr_set(x_2237, 0, x_2234);
return x_2237;
}
else
{
obj* x_2238; obj* x_2240; obj* x_2241; obj* x_2243; obj* x_2245; obj* x_2246; obj* x_2247; obj* x_2248; 
x_2238 = lean::cnstr_get(x_2232, 0);
if (lean::is_exclusive(x_2232)) {
 x_2240 = x_2232;
} else {
 lean::inc(x_2238);
 lean::dec(x_2232);
 x_2240 = lean::box(0);
}
x_2241 = lean::cnstr_get(x_2238, 0);
x_2243 = lean::cnstr_get(x_2238, 1);
if (lean::is_exclusive(x_2238)) {
 x_2245 = x_2238;
} else {
 lean::inc(x_2241);
 lean::inc(x_2243);
 lean::dec(x_2238);
 x_2245 = lean::box(0);
}
x_2246 = lean_expr_mk_app(x_2227, x_2241);
if (lean::is_scalar(x_2245)) {
 x_2247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2247 = x_2245;
}
lean::cnstr_set(x_2247, 0, x_2246);
lean::cnstr_set(x_2247, 1, x_2243);
if (lean::is_scalar(x_2240)) {
 x_2248 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2248 = x_2240;
}
lean::cnstr_set(x_2248, 0, x_2247);
return x_2248;
}
}
}
}
else
{
obj* x_2250; obj* x_2251; obj* x_2255; obj* x_2256; 
lean::dec(x_10);
x_2250 = l_Lean_Parser_identUnivs_HasView;
x_2251 = lean::cnstr_get(x_2250, 0);
lean::inc(x_2251);
lean::dec(x_2250);
lean::inc(x_0);
x_2255 = lean::apply_1(x_2251, x_0);
x_2256 = lean::cnstr_get(x_2255, 1);
lean::inc(x_2256);
if (lean::obj_tag(x_2256) == 0)
{
obj* x_2258; obj* x_2262; obj* x_2263; obj* x_2264; obj* x_2265; obj* x_2268; obj* x_2269; obj* x_2270; obj* x_2271; obj* x_2272; obj* x_2273; uint8 x_2274; 
x_2258 = lean::cnstr_get(x_2255, 0);
lean::inc(x_2258);
lean::dec(x_2255);
lean::inc(x_2258);
x_2262 = l_Lean_Elaborator_mangleIdent(x_2258);
x_2263 = lean::box(0);
x_2264 = lean_expr_mk_const(x_2262, x_2263);
x_2265 = lean::cnstr_get(x_2258, 3);
lean::inc(x_2265);
lean::dec(x_2258);
x_2268 = lean::mk_nat_obj(0ul);
x_2269 = l_List_enumFrom___main___rarg(x_2268, x_2265);
x_2270 = l_Lean_Elaborator_toPexpr___main___closed__45;
x_2271 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2270, x_2269);
x_2272 = lean_expr_mk_mdata(x_2271, x_2264);
x_2273 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2274 = lean_name_dec_eq(x_8, x_2273);
lean::dec(x_8);
if (x_2274 == 0)
{
obj* x_2276; 
x_2276 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2276) == 0)
{
obj* x_2279; obj* x_2280; 
lean::dec(x_2);
x_2279 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2279, 0, x_2272);
lean::cnstr_set(x_2279, 1, x_3);
x_2280 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2280, 0, x_2279);
return x_2280;
}
else
{
obj* x_2281; obj* x_2284; obj* x_2287; obj* x_2290; obj* x_2291; obj* x_2293; obj* x_2294; obj* x_2295; obj* x_2298; obj* x_2299; obj* x_2300; obj* x_2301; obj* x_2302; 
x_2281 = lean::cnstr_get(x_2276, 0);
lean::inc(x_2281);
lean::dec(x_2276);
x_2284 = lean::cnstr_get(x_2, 0);
lean::inc(x_2284);
lean::dec(x_2);
x_2287 = lean::cnstr_get(x_2284, 2);
lean::inc(x_2287);
lean::dec(x_2284);
x_2290 = l_Lean_FileMap_toPosition(x_2287, x_2281);
x_2291 = lean::cnstr_get(x_2290, 1);
lean::inc(x_2291);
x_2293 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2294 = l_Lean_KVMap_setNat(x_2263, x_2293, x_2291);
x_2295 = lean::cnstr_get(x_2290, 0);
lean::inc(x_2295);
lean::dec(x_2290);
x_2298 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2299 = l_Lean_KVMap_setNat(x_2294, x_2298, x_2295);
x_2300 = lean_expr_mk_mdata(x_2299, x_2272);
x_2301 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2301, 0, x_2300);
lean::cnstr_set(x_2301, 1, x_3);
x_2302 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2302, 0, x_2301);
return x_2302;
}
}
else
{
obj* x_2305; obj* x_2306; 
lean::dec(x_0);
lean::dec(x_2);
x_2305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2305, 0, x_2272);
lean::cnstr_set(x_2305, 1, x_3);
x_2306 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2306, 0, x_2305);
return x_2306;
}
}
else
{
obj* x_2307; obj* x_2310; obj* x_2313; obj* x_2317; 
x_2307 = lean::cnstr_get(x_2255, 0);
lean::inc(x_2307);
lean::dec(x_2255);
x_2310 = lean::cnstr_get(x_2256, 0);
lean::inc(x_2310);
lean::dec(x_2256);
x_2313 = lean::cnstr_get(x_2310, 1);
lean::inc(x_2313);
lean::dec(x_2310);
lean::inc(x_2);
x_2317 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_2313, x_1, x_2, x_3);
if (lean::obj_tag(x_2317) == 0)
{
obj* x_2322; obj* x_2324; obj* x_2325; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2307);
x_2322 = lean::cnstr_get(x_2317, 0);
if (lean::is_exclusive(x_2317)) {
 x_2324 = x_2317;
} else {
 lean::inc(x_2322);
 lean::dec(x_2317);
 x_2324 = lean::box(0);
}
if (lean::is_scalar(x_2324)) {
 x_2325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2325 = x_2324;
}
lean::cnstr_set(x_2325, 0, x_2322);
return x_2325;
}
else
{
obj* x_2326; obj* x_2328; obj* x_2329; obj* x_2331; obj* x_2333; obj* x_2335; obj* x_2336; obj* x_2337; obj* x_2338; obj* x_2341; obj* x_2342; obj* x_2343; obj* x_2344; obj* x_2345; obj* x_2346; uint8 x_2347; 
x_2326 = lean::cnstr_get(x_2317, 0);
if (lean::is_exclusive(x_2317)) {
 lean::cnstr_set(x_2317, 0, lean::box(0));
 x_2328 = x_2317;
} else {
 lean::inc(x_2326);
 lean::dec(x_2317);
 x_2328 = lean::box(0);
}
x_2329 = lean::cnstr_get(x_2326, 0);
x_2331 = lean::cnstr_get(x_2326, 1);
if (lean::is_exclusive(x_2326)) {
 lean::cnstr_set(x_2326, 0, lean::box(0));
 lean::cnstr_set(x_2326, 1, lean::box(0));
 x_2333 = x_2326;
} else {
 lean::inc(x_2329);
 lean::inc(x_2331);
 lean::dec(x_2326);
 x_2333 = lean::box(0);
}
lean::inc(x_2307);
x_2335 = l_Lean_Elaborator_mangleIdent(x_2307);
x_2336 = lean_expr_mk_const(x_2335, x_2329);
x_2337 = lean::box(0);
x_2338 = lean::cnstr_get(x_2307, 3);
lean::inc(x_2338);
lean::dec(x_2307);
x_2341 = lean::mk_nat_obj(0ul);
x_2342 = l_List_enumFrom___main___rarg(x_2341, x_2338);
x_2343 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2344 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2343, x_2342);
x_2345 = lean_expr_mk_mdata(x_2344, x_2336);
x_2346 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2347 = lean_name_dec_eq(x_8, x_2346);
lean::dec(x_8);
if (x_2347 == 0)
{
obj* x_2349; 
x_2349 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2349) == 0)
{
obj* x_2352; obj* x_2353; 
lean::dec(x_2);
if (lean::is_scalar(x_2333)) {
 x_2352 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2352 = x_2333;
}
lean::cnstr_set(x_2352, 0, x_2345);
lean::cnstr_set(x_2352, 1, x_2331);
if (lean::is_scalar(x_2328)) {
 x_2353 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2353 = x_2328;
}
lean::cnstr_set(x_2353, 0, x_2352);
return x_2353;
}
else
{
obj* x_2354; obj* x_2357; obj* x_2360; obj* x_2363; obj* x_2364; obj* x_2366; obj* x_2367; obj* x_2368; obj* x_2371; obj* x_2372; obj* x_2373; obj* x_2374; obj* x_2375; 
x_2354 = lean::cnstr_get(x_2349, 0);
lean::inc(x_2354);
lean::dec(x_2349);
x_2357 = lean::cnstr_get(x_2, 0);
lean::inc(x_2357);
lean::dec(x_2);
x_2360 = lean::cnstr_get(x_2357, 2);
lean::inc(x_2360);
lean::dec(x_2357);
x_2363 = l_Lean_FileMap_toPosition(x_2360, x_2354);
x_2364 = lean::cnstr_get(x_2363, 1);
lean::inc(x_2364);
x_2366 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2367 = l_Lean_KVMap_setNat(x_2337, x_2366, x_2364);
x_2368 = lean::cnstr_get(x_2363, 0);
lean::inc(x_2368);
lean::dec(x_2363);
x_2371 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2372 = l_Lean_KVMap_setNat(x_2367, x_2371, x_2368);
x_2373 = lean_expr_mk_mdata(x_2372, x_2345);
if (lean::is_scalar(x_2333)) {
 x_2374 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2374 = x_2333;
}
lean::cnstr_set(x_2374, 0, x_2373);
lean::cnstr_set(x_2374, 1, x_2331);
if (lean::is_scalar(x_2328)) {
 x_2375 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2375 = x_2328;
}
lean::cnstr_set(x_2375, 0, x_2374);
return x_2375;
}
}
else
{
obj* x_2378; obj* x_2379; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2333)) {
 x_2378 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2378 = x_2333;
}
lean::cnstr_set(x_2378, 0, x_2345);
lean::cnstr_set(x_2378, 1, x_2331);
if (lean::is_scalar(x_2328)) {
 x_2379 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2379 = x_2328;
}
lean::cnstr_set(x_2379, 0, x_2378);
return x_2379;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2383; obj* x_2385; obj* x_2386; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2383 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2385 = x_13;
} else {
 lean::inc(x_2383);
 lean::dec(x_13);
 x_2385 = lean::box(0);
}
if (lean::is_scalar(x_2385)) {
 x_2386 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2386 = x_2385;
}
lean::cnstr_set(x_2386, 0, x_2383);
return x_2386;
}
else
{
obj* x_2387; obj* x_2389; obj* x_2390; obj* x_2392; obj* x_2394; obj* x_2395; uint8 x_2396; 
x_2387 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2389 = x_13;
} else {
 lean::inc(x_2387);
 lean::dec(x_13);
 x_2389 = lean::box(0);
}
x_2390 = lean::cnstr_get(x_2387, 0);
x_2392 = lean::cnstr_get(x_2387, 1);
if (lean::is_exclusive(x_2387)) {
 lean::cnstr_set(x_2387, 0, lean::box(0));
 lean::cnstr_set(x_2387, 1, lean::box(0));
 x_2394 = x_2387;
} else {
 lean::inc(x_2390);
 lean::inc(x_2392);
 lean::dec(x_2387);
 x_2394 = lean::box(0);
}
x_2395 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2396 = lean_name_dec_eq(x_8, x_2395);
lean::dec(x_8);
if (x_2396 == 0)
{
obj* x_2398; 
x_2398 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2398) == 0)
{
obj* x_2401; obj* x_2402; 
lean::dec(x_2);
if (lean::is_scalar(x_2394)) {
 x_2401 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2401 = x_2394;
}
lean::cnstr_set(x_2401, 0, x_2390);
lean::cnstr_set(x_2401, 1, x_2392);
if (lean::is_scalar(x_2389)) {
 x_2402 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2402 = x_2389;
}
lean::cnstr_set(x_2402, 0, x_2401);
return x_2402;
}
else
{
obj* x_2403; obj* x_2406; obj* x_2409; obj* x_2412; obj* x_2413; obj* x_2415; obj* x_2416; obj* x_2417; obj* x_2418; obj* x_2421; obj* x_2422; obj* x_2423; obj* x_2424; obj* x_2425; 
x_2403 = lean::cnstr_get(x_2398, 0);
lean::inc(x_2403);
lean::dec(x_2398);
x_2406 = lean::cnstr_get(x_2, 0);
lean::inc(x_2406);
lean::dec(x_2);
x_2409 = lean::cnstr_get(x_2406, 2);
lean::inc(x_2409);
lean::dec(x_2406);
x_2412 = l_Lean_FileMap_toPosition(x_2409, x_2403);
x_2413 = lean::cnstr_get(x_2412, 1);
lean::inc(x_2413);
x_2415 = lean::box(0);
x_2416 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2417 = l_Lean_KVMap_setNat(x_2415, x_2416, x_2413);
x_2418 = lean::cnstr_get(x_2412, 0);
lean::inc(x_2418);
lean::dec(x_2412);
x_2421 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2422 = l_Lean_KVMap_setNat(x_2417, x_2421, x_2418);
x_2423 = lean_expr_mk_mdata(x_2422, x_2390);
if (lean::is_scalar(x_2394)) {
 x_2424 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2424 = x_2394;
}
lean::cnstr_set(x_2424, 0, x_2423);
lean::cnstr_set(x_2424, 1, x_2392);
if (lean::is_scalar(x_2389)) {
 x_2425 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2425 = x_2389;
}
lean::cnstr_set(x_2425, 0, x_2424);
return x_2425;
}
}
else
{
obj* x_2428; obj* x_2429; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2394)) {
 x_2428 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2428 = x_2394;
}
lean::cnstr_set(x_2428, 0, x_2390);
lean::cnstr_set(x_2428, 1, x_2392);
if (lean::is_scalar(x_2389)) {
 x_2429 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2429 = x_2389;
}
lean::cnstr_set(x_2429, 0, x_2428);
return x_2429;
}
}
}
lbl_16:
{
obj* x_2430; obj* x_2432; obj* x_2434; obj* x_2435; uint8 x_2436; 
x_2430 = lean::cnstr_get(x_15, 0);
x_2432 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2434 = x_15;
} else {
 lean::inc(x_2430);
 lean::inc(x_2432);
 lean::dec(x_15);
 x_2434 = lean::box(0);
}
x_2435 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2436 = lean_name_dec_eq(x_8, x_2435);
lean::dec(x_8);
if (x_2436 == 0)
{
obj* x_2438; 
x_2438 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2438) == 0)
{
obj* x_2441; obj* x_2442; 
lean::dec(x_2);
if (lean::is_scalar(x_2434)) {
 x_2441 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2441 = x_2434;
}
lean::cnstr_set(x_2441, 0, x_2430);
lean::cnstr_set(x_2441, 1, x_2432);
x_2442 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2442, 0, x_2441);
return x_2442;
}
else
{
obj* x_2443; obj* x_2446; obj* x_2449; obj* x_2452; obj* x_2453; obj* x_2455; obj* x_2456; obj* x_2457; obj* x_2458; obj* x_2461; obj* x_2462; obj* x_2463; obj* x_2464; obj* x_2465; 
x_2443 = lean::cnstr_get(x_2438, 0);
lean::inc(x_2443);
lean::dec(x_2438);
x_2446 = lean::cnstr_get(x_2, 0);
lean::inc(x_2446);
lean::dec(x_2);
x_2449 = lean::cnstr_get(x_2446, 2);
lean::inc(x_2449);
lean::dec(x_2446);
x_2452 = l_Lean_FileMap_toPosition(x_2449, x_2443);
x_2453 = lean::cnstr_get(x_2452, 1);
lean::inc(x_2453);
x_2455 = lean::box(0);
x_2456 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2457 = l_Lean_KVMap_setNat(x_2455, x_2456, x_2453);
x_2458 = lean::cnstr_get(x_2452, 0);
lean::inc(x_2458);
lean::dec(x_2452);
x_2461 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2462 = l_Lean_KVMap_setNat(x_2457, x_2461, x_2458);
x_2463 = lean_expr_mk_mdata(x_2462, x_2430);
if (lean::is_scalar(x_2434)) {
 x_2464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2464 = x_2434;
}
lean::cnstr_set(x_2464, 0, x_2463);
lean::cnstr_set(x_2464, 1, x_2432);
x_2465 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2465, 0, x_2464);
return x_2465;
}
}
else
{
obj* x_2468; obj* x_2469; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2434)) {
 x_2468 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2468 = x_2434;
}
lean::cnstr_set(x_2468, 0, x_2430);
lean::cnstr_set(x_2468, 1, x_2432);
x_2469 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2469, 0, x_2468);
return x_2469;
}
}
}
default:
{
obj* x_2470; 
x_2470 = lean::box(0);
x_4 = x_2470;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2473; obj* x_2474; obj* x_2475; obj* x_2476; obj* x_2477; obj* x_2478; obj* x_2480; 
lean::dec(x_4);
lean::inc(x_0);
x_2473 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2473, 0, x_0);
x_2474 = l_Lean_Parser_Syntax_format___main(x_0);
x_2475 = l_Lean_Options_empty;
x_2476 = l_Lean_Format_pretty(x_2474, x_2475);
x_2477 = l_Lean_Elaborator_toPexpr___main___closed__1;
x_2478 = lean::string_append(x_2477, x_2476);
lean::dec(x_2476);
x_2480 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2473, x_2478, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2473);
return x_2480;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_toPexpr___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toPexpr___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_toPexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toPexpr___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_toPexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toPexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_getNamespace(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_currentScope(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 6);
lean::inc(x_13);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_18 = x_8;
} else {
 lean::inc(x_16);
 lean::dec(x_8);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
if (lean::is_scalar(x_10)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_10;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_24 = x_8;
} else {
 lean::inc(x_22);
 lean::dec(x_8);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_22);
if (lean::is_scalar(x_10)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_10;
}
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
obj* l_Lean_Elaborator_getNamespace___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_getNamespace(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_Lean_Elaborator_oldElabCommand___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_RBNode_revFold___main___at_Lean_Elaborator_oldElabCommand___spec__2(x_0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_0 = x_10;
x_1 = x_2;
goto _start;
}
}
}
obj* l_RBTree_toList___at_Lean_Elaborator_oldElabCommand___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_RBNode_revFold___main___at_Lean_Elaborator_oldElabCommand___spec__2(x_1, x_0);
return x_2;
}
}
obj* l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(x_4);
x_8 = lean::box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_8);
return x_9;
}
}
}
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 6);
x_10 = lean::cnstr_get(x_1, 7);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 3);
 lean::cnstr_release(x_1, 4);
 lean::cnstr_release(x_1, 5);
 lean::cnstr_release(x_1, 8);
 x_12 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
x_15 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
x_16 = l_Lean_Elaborator_OrderedRBMap_ofList___rarg(x_15, x_13);
x_17 = lean::cnstr_get(x_0, 3);
lean::inc(x_17);
x_19 = l_Lean_Elaborator_OrderedRBMap_ofList___rarg(x_15, x_17);
x_20 = lean::cnstr_get(x_0, 4);
lean::inc(x_20);
x_22 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(x_20);
x_23 = lean::cnstr_get(x_0, 5);
lean::inc(x_23);
lean::dec(x_0);
if (lean::is_scalar(x_12)) {
 x_26 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_26 = x_12;
}
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_16);
lean::cnstr_set(x_26, 4, x_19);
lean::cnstr_set(x_26, 5, x_22);
lean::cnstr_set(x_26, 6, x_8);
lean::cnstr_set(x_26, 7, x_10);
lean::cnstr_set(x_26, 8, x_23);
return x_26;
}
}
obj* l_Lean_Elaborator_oldElabCommand(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 2);
lean::inc(x_7);
x_9 = l_Lean_Parser_Syntax_getPos(x_0);
lean::inc(x_4);
lean::inc(x_3);
x_12 = l_Lean_Elaborator_currentScope(x_2, x_3, x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_17; 
x_17 = lean::mk_nat_obj(0ul);
x_15 = x_17;
goto lbl_16;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
lean::dec(x_9);
x_15 = x_18;
goto lbl_16;
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_13);
x_25 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_27 = x_12;
} else {
 lean::inc(x_25);
 lean::dec(x_12);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_38; 
x_29 = lean::cnstr_get(x_12, 0);
lean::inc(x_29);
lean::dec(x_12);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
lean::inc(x_3);
x_38 = l_Lean_Elaborator_getNamespace(x_2, x_3, x_34);
if (lean::obj_tag(x_38) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_13);
lean::dec(x_32);
x_44 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_59; obj* x_61; obj* x_63; obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_81; obj* x_84; obj* x_85; obj* x_88; 
x_48 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 x_50 = x_38;
} else {
 lean::inc(x_48);
 lean::dec(x_38);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
x_56 = lean::cnstr_get(x_5, 0);
lean::inc(x_56);
lean::dec(x_5);
x_59 = lean::cnstr_get(x_4, 8);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_4, 9);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_32, 3);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
lean::dec(x_63);
x_68 = l_List_reverse___rarg(x_65);
x_69 = lean::cnstr_get(x_32, 4);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
lean::dec(x_69);
x_74 = l_List_reverse___rarg(x_71);
x_75 = lean::cnstr_get(x_32, 5);
lean::inc(x_75);
x_77 = l_RBTree_toList___at_Lean_Elaborator_oldElabCommand___spec__1(x_75);
x_78 = lean::cnstr_get(x_32, 8);
lean::inc(x_78);
lean::dec(x_32);
x_81 = lean::cnstr_get(x_4, 10);
lean::inc(x_81);
lean::dec(x_4);
x_84 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_84, 0, x_59);
lean::cnstr_set(x_84, 1, x_61);
lean::cnstr_set(x_84, 2, x_68);
lean::cnstr_set(x_84, 3, x_74);
lean::cnstr_set(x_84, 4, x_77);
lean::cnstr_set(x_84, 5, x_78);
lean::cnstr_set(x_84, 6, x_81);
lean::cnstr_set(x_84, 7, x_51);
x_85 = lean_elaborator_elaborate_command(x_56, x_13, x_84);
lean::dec(x_84);
lean::dec(x_56);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_3);
x_91 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_93 = x_85;
} else {
 lean::inc(x_91);
 lean::dec(x_85);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_53, 0);
x_96 = lean::cnstr_get(x_53, 1);
x_98 = lean::cnstr_get(x_53, 2);
x_100 = lean::cnstr_get(x_53, 3);
x_102 = lean::cnstr_get(x_53, 4);
x_104 = lean::cnstr_get(x_53, 5);
x_106 = lean::cnstr_get(x_53, 6);
x_108 = lean::cnstr_get(x_53, 7);
x_110 = lean::cnstr_get(x_53, 8);
x_112 = lean::cnstr_get(x_53, 9);
x_114 = lean::cnstr_get(x_53, 10);
if (lean::is_exclusive(x_53)) {
 x_116 = x_53;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::inc(x_108);
 lean::inc(x_110);
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_53);
 x_116 = lean::box(0);
}
x_117 = l_List_append___rarg(x_91, x_104);
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_94);
lean::cnstr_set(x_118, 1, x_96);
lean::cnstr_set(x_118, 2, x_98);
lean::cnstr_set(x_118, 3, x_100);
lean::cnstr_set(x_118, 4, x_102);
lean::cnstr_set(x_118, 5, x_117);
lean::cnstr_set(x_118, 6, x_106);
lean::cnstr_set(x_118, 7, x_108);
lean::cnstr_set(x_118, 8, x_110);
lean::cnstr_set(x_118, 9, x_112);
lean::cnstr_set(x_118, 10, x_114);
x_119 = lean::box(0);
if (lean::is_scalar(x_93)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_93;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_118);
if (lean::is_scalar(x_50)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_50;
}
lean::cnstr_set(x_121, 0, x_120);
return x_121;
}
else
{
obj* x_123; obj* x_126; obj* x_130; obj* x_131; 
lean::dec(x_50);
x_123 = lean::cnstr_get(x_85, 1);
lean::inc(x_123);
lean::dec(x_85);
x_126 = lean::cnstr_get(x_88, 0);
lean::inc(x_126);
lean::dec(x_88);
lean::inc(x_126);
x_130 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_oldElabCommand___lambda__1), 2, 1);
lean::closure_set(x_130, 0, x_126);
x_131 = l_Lean_Elaborator_modifyCurrentScope(x_130, x_2, x_3, x_53);
if (lean::obj_tag(x_131) == 0)
{
obj* x_134; obj* x_136; obj* x_137; 
lean::dec(x_126);
lean::dec(x_123);
x_134 = lean::cnstr_get(x_131, 0);
if (lean::is_exclusive(x_131)) {
 x_136 = x_131;
} else {
 lean::inc(x_134);
 lean::dec(x_131);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_134);
return x_137;
}
else
{
obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_161; obj* x_163; obj* x_165; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_138 = lean::cnstr_get(x_131, 0);
if (lean::is_exclusive(x_131)) {
 x_140 = x_131;
} else {
 lean::inc(x_138);
 lean::dec(x_131);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_138, 1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 x_143 = x_138;
} else {
 lean::inc(x_141);
 lean::dec(x_138);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_141, 0);
x_146 = lean::cnstr_get(x_141, 1);
x_148 = lean::cnstr_get(x_141, 2);
x_150 = lean::cnstr_get(x_141, 3);
x_152 = lean::cnstr_get(x_141, 4);
x_154 = lean::cnstr_get(x_141, 5);
x_156 = lean::cnstr_get(x_141, 6);
x_158 = lean::cnstr_get(x_141, 7);
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 8);
 lean::cnstr_release(x_141, 9);
 lean::cnstr_release(x_141, 10);
 x_160 = x_141;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::inc(x_152);
 lean::inc(x_154);
 lean::inc(x_156);
 lean::inc(x_158);
 lean::dec(x_141);
 x_160 = lean::box(0);
}
x_161 = lean::cnstr_get(x_126, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_126, 1);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_126, 6);
lean::inc(x_165);
lean::dec(x_126);
x_168 = l_List_append___rarg(x_123, x_154);
if (lean::is_scalar(x_160)) {
 x_169 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_169 = x_160;
}
lean::cnstr_set(x_169, 0, x_144);
lean::cnstr_set(x_169, 1, x_146);
lean::cnstr_set(x_169, 2, x_148);
lean::cnstr_set(x_169, 3, x_150);
lean::cnstr_set(x_169, 4, x_152);
lean::cnstr_set(x_169, 5, x_168);
lean::cnstr_set(x_169, 6, x_156);
lean::cnstr_set(x_169, 7, x_158);
lean::cnstr_set(x_169, 8, x_161);
lean::cnstr_set(x_169, 9, x_163);
lean::cnstr_set(x_169, 10, x_165);
x_170 = lean::box(0);
if (lean::is_scalar(x_143)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_143;
}
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_169);
if (lean::is_scalar(x_140)) {
 x_172 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_172 = x_140;
}
lean::cnstr_set(x_172, 0, x_171);
return x_172;
}
}
}
}
}
lbl_16:
{
switch (lean::obj_tag(x_1)) {
case 10:
{
obj* x_173; obj* x_175; obj* x_178; obj* x_179; obj* x_181; obj* x_182; obj* x_183; obj* x_186; obj* x_187; obj* x_188; 
x_173 = lean::cnstr_get(x_1, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_1, 1);
lean::inc(x_175);
lean::dec(x_1);
x_178 = l_Lean_FileMap_toPosition(x_7, x_15);
x_179 = lean::cnstr_get(x_178, 1);
lean::inc(x_179);
x_181 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_182 = l_Lean_KVMap_setNat(x_173, x_181, x_179);
x_183 = lean::cnstr_get(x_178, 0);
lean::inc(x_183);
lean::dec(x_178);
x_186 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_187 = l_Lean_KVMap_setNat(x_182, x_186, x_183);
x_188 = lean_expr_mk_mdata(x_187, x_175);
x_13 = x_188;
goto lbl_14;
}
default:
{
lean::dec(x_7);
lean::dec(x_15);
x_13 = x_1;
goto lbl_14;
}
}
}
}
}
obj* l_Lean_Elaborator_oldElabCommand___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Elaborator_oldElabCommand(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_7 = lean::box(0);
x_8 = lean_expr_mk_const(x_2, x_7);
x_9 = l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Lean_Elaborator_namesToPexpr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(x_0);
x_2 = l_Lean_Elaborator_mkEqns___closed__1;
x_3 = l_Lean_Expr_mkCapp(x_2, x_1);
return x_3;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_Lean_Elaborator_toPexpr___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 2);
lean::inc(x_18);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_13, 1);
lean::inc(x_21);
lean::dec(x_13);
lean::inc(x_2);
x_25 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_21, x_1, x_2, x_3);
if (lean::obj_tag(x_25) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_32 = x_25;
} else {
 lean::inc(x_30);
 lean::dec(x_25);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_25, 0);
lean::inc(x_34);
lean::dec(x_25);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_Lean_Expr_mkCapp(x_18, x_37);
x_43 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(x_10, x_1, x_2, x_39);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_12);
lean::dec(x_42);
x_46 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_50 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_52 = x_43;
} else {
 lean::inc(x_50);
 lean::dec(x_43);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
x_55 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_12;
}
lean::cnstr_set(x_58, 0, x_42);
lean::cnstr_set(x_58, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_52;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
}
}
}
obj* l_Lean_Elaborator_attrsToPexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(x_0, x_1, x_2, x_3);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Elaborator_mkEqns___closed__1;
x_18 = l_Lean_Expr_mkCapp(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_attrsToPexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_attrsToPexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("noncomputable");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("unsafe");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("private");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = 1;
x_5 = l_Lean_KVMap_setBool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("protected");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = 1;
x_5 = l_Lean_KVMap_setBool(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("docString");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("private");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_declModifiersToPexpr___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_declModifiersToPexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_4 = lean::box(0);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_16 = x_4;
goto lbl_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
lean::dec(x_7);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; 
lean::dec(x_18);
x_22 = l_Lean_Elaborator_declModifiersToPexpr___closed__3;
x_16 = x_22;
goto lbl_17;
}
else
{
obj* x_24; 
lean::dec(x_18);
x_24 = l_Lean_Elaborator_declModifiersToPexpr___closed__4;
x_16 = x_24;
goto lbl_17;
}
}
}
else
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_5, 0);
lean::inc(x_25);
lean::dec(x_5);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_16 = x_4;
goto lbl_17;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_7, 0);
lean::inc(x_31);
lean::dec(x_7);
if (lean::obj_tag(x_31) == 0)
{
obj* x_35; 
lean::dec(x_31);
x_35 = l_Lean_Elaborator_declModifiersToPexpr___closed__3;
x_16 = x_35;
goto lbl_17;
}
else
{
obj* x_37; 
lean::dec(x_31);
x_37 = l_Lean_Elaborator_declModifiersToPexpr___closed__4;
x_16 = x_37;
goto lbl_17;
}
}
}
else
{
obj* x_38; obj* x_41; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_Lean_Elaborator_declModifiersToPexpr___closed__5;
x_45 = l_Lean_KVMap_setString(x_4, x_44, x_41);
if (lean::obj_tag(x_7) == 0)
{
x_16 = x_45;
goto lbl_17;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_7, 0);
lean::inc(x_46);
lean::dec(x_7);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; uint8 x_51; obj* x_52; 
lean::dec(x_46);
x_50 = l_Lean_Elaborator_declModifiersToPexpr___closed__6;
x_51 = 1;
x_52 = l_Lean_KVMap_setBool(x_45, x_50, x_51);
x_16 = x_52;
goto lbl_17;
}
else
{
obj* x_54; uint8 x_55; obj* x_56; 
lean::dec(x_46);
x_54 = l_Lean_Elaborator_declModifiersToPexpr___closed__7;
x_55 = 1;
x_56 = l_Lean_KVMap_setBool(x_45, x_54, x_55);
x_16 = x_56;
goto lbl_17;
}
}
}
}
lbl_17:
{
uint8 x_57; 
if (lean::obj_tag(x_9) == 0)
{
uint8 x_59; 
x_59 = 0;
x_57 = x_59;
goto lbl_58;
}
else
{
uint8 x_61; 
lean::dec(x_9);
x_61 = 1;
x_57 = x_61;
goto lbl_58;
}
lbl_58:
{
obj* x_62; obj* x_63; 
x_62 = l_Lean_Elaborator_declModifiersToPexpr___closed__1;
x_63 = l_Lean_KVMap_setBool(x_16, x_62, x_57);
if (lean::obj_tag(x_11) == 0)
{
obj* x_64; uint8 x_65; obj* x_66; 
x_64 = l_Lean_Elaborator_declModifiersToPexpr___closed__2;
x_65 = 0;
x_66 = l_Lean_KVMap_setBool(x_63, x_64, x_65);
if (lean::obj_tag(x_13) == 0)
{
obj* x_67; 
x_67 = l_Lean_Elaborator_attrsToPexpr(x_4, x_1, x_2, x_3);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_66);
x_69 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_71 = x_67;
} else {
 lean::inc(x_69);
 lean::dec(x_67);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
return x_72;
}
else
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_73 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_75 = x_67;
} else {
 lean::inc(x_73);
 lean::dec(x_67);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_73, 0);
x_78 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_80 = x_73;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
x_81 = lean_expr_mk_mdata(x_66, x_76);
if (lean::is_scalar(x_80)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_80;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_78);
if (lean::is_scalar(x_75)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_75;
}
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
}
else
{
obj* x_84; obj* x_87; obj* x_90; 
x_84 = lean::cnstr_get(x_13, 0);
lean::inc(x_84);
lean::dec(x_13);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
lean::dec(x_84);
x_90 = l_Lean_Elaborator_attrsToPexpr(x_87, x_1, x_2, x_3);
if (lean::obj_tag(x_90) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_66);
x_92 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_94 = x_90;
} else {
 lean::inc(x_92);
 lean::dec(x_90);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
return x_95;
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_96 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_98 = x_90;
} else {
 lean::inc(x_96);
 lean::dec(x_90);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_96, 0);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean_expr_mk_mdata(x_66, x_99);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
if (lean::is_scalar(x_98)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_98;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
obj* x_108; uint8 x_109; obj* x_110; 
lean::dec(x_11);
x_108 = l_Lean_Elaborator_declModifiersToPexpr___closed__2;
x_109 = 1;
x_110 = l_Lean_KVMap_setBool(x_63, x_108, x_109);
if (lean::obj_tag(x_13) == 0)
{
obj* x_111; 
x_111 = l_Lean_Elaborator_attrsToPexpr(x_4, x_1, x_2, x_3);
if (lean::obj_tag(x_111) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_110);
x_113 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_115 = x_111;
} else {
 lean::inc(x_113);
 lean::dec(x_111);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
return x_116;
}
else
{
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_117 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_119 = x_111;
} else {
 lean::inc(x_117);
 lean::dec(x_111);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
x_122 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
x_125 = lean_expr_mk_mdata(x_110, x_120);
if (lean::is_scalar(x_124)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_124;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_122);
if (lean::is_scalar(x_119)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_119;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
}
else
{
obj* x_128; obj* x_131; obj* x_134; 
x_128 = lean::cnstr_get(x_13, 0);
lean::inc(x_128);
lean::dec(x_13);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
x_134 = l_Lean_Elaborator_attrsToPexpr(x_131, x_1, x_2, x_3);
if (lean::obj_tag(x_134) == 0)
{
obj* x_136; obj* x_138; obj* x_139; 
lean::dec(x_110);
x_136 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_138 = x_134;
} else {
 lean::inc(x_136);
 lean::dec(x_134);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
return x_139;
}
else
{
obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_140 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_142 = x_134;
} else {
 lean::inc(x_140);
 lean::dec(x_134);
 x_142 = lean::box(0);
}
x_143 = lean::cnstr_get(x_140, 0);
x_145 = lean::cnstr_get(x_140, 1);
if (lean::is_exclusive(x_140)) {
 x_147 = x_140;
} else {
 lean::inc(x_143);
 lean::inc(x_145);
 lean::dec(x_140);
 x_147 = lean::box(0);
}
x_148 = lean_expr_mk_mdata(x_110, x_143);
if (lean::is_scalar(x_147)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_147;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_145);
if (lean::is_scalar(x_142)) {
 x_150 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_150 = x_142;
}
lean::cnstr_set(x_150, 0, x_149);
return x_150;
}
}
}
}
}
}
}
obj* l_Lean_Elaborator_declModifiersToPexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_declModifiersToPexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Elaborator_identUnivParamsToPexpr___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_7 = l_Lean_Elaborator_mangleIdent(x_2);
x_8 = level_mk_param(x_7);
x_9 = l_List_map___main___at_Lean_Elaborator_identUnivParamsToPexpr___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Lean_Elaborator_identUnivParamsToPexpr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = l_Lean_Elaborator_mangleIdent(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean_expr_mk_const(x_3, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_List_map___main___at_Lean_Elaborator_identUnivParamsToPexpr___spec__1(x_12);
x_16 = lean_expr_mk_const(x_3, x_15);
return x_16;
}
}
}
obj* l_Lean_Elaborator_locally(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_23; 
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
lean::inc(x_2);
lean::inc(x_1);
x_23 = lean::apply_3(x_0, x_1, x_2, x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_29 = x_23;
} else {
 lean::inc(x_27);
 lean::dec(x_23);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_37, 0, x_16);
x_38 = l_Lean_Elaborator_modifyCurrentScope(x_37, x_1, x_2, x_34);
lean::dec(x_1);
return x_38;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_24; obj* x_26; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_8);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
lean::dec(x_14);
x_24 = l_Lean_Elaborator_mangleIdent(x_19);
lean::inc(x_2);
x_26 = l_Lean_Elaborator_toPexpr___main(x_21, x_1, x_2, x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_16);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_41; uint8 x_44; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
lean::dec(x_26);
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
lean::dec(x_36);
x_44 = lean::unbox(x_16);
lean::inc(x_24);
x_46 = lean_expr_local(x_24, x_24, x_39, x_44);
x_47 = l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(x_10, x_1, x_2, x_41);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_12);
lean::dec(x_46);
x_50 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_54 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_56 = x_47;
} else {
 lean::inc(x_54);
 lean::dec(x_47);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 0);
x_59 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_61 = x_54;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_54);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_12;
}
lean::cnstr_set(x_62, 0, x_46);
lean::cnstr_set(x_62, 1, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
if (lean::is_scalar(x_56)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_56;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
obj* l_Lean_Elaborator_simpleBindersToPexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(x_0, x_1, x_2, x_3);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Elaborator_mkEqns___closed__1;
x_18 = l_Lean_Expr_mkCapp(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_simpleBindersToPexpr___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_simpleBindersToPexpr(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_14 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::inc(x_3);
x_18 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_15, x_2, x_3, x_4);
if (lean::obj_tag(x_18) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_12);
x_24 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_26 = x_18;
} else {
 lean::inc(x_24);
 lean::dec(x_18);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_40; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_28, 0);
x_33 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_35 = x_28;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_28);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_10, 3);
lean::inc(x_36);
lean::dec(x_10);
lean::inc(x_3);
x_40 = l_Lean_Elaborator_toPexpr___main(x_36, x_2, x_3, x_33);
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_35);
lean::dec(x_31);
x_47 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_49 = x_40;
} else {
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; 
x_51 = lean::cnstr_get(x_40, 0);
lean::inc(x_51);
lean::dec(x_40);
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_54);
lean::inc(x_0);
if (lean::is_scalar(x_35)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_35;
}
lean::cnstr_set(x_61, 0, x_0);
lean::cnstr_set(x_61, 1, x_59);
x_62 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_0, x_12, x_2, x_3, x_56);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_14);
lean::dec(x_61);
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
return x_68;
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_69 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_71 = x_62;
} else {
 lean::inc(x_69);
 lean::dec(x_62);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_69, 0);
x_74 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 x_76 = x_69;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_69);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_14;
}
lean::cnstr_set(x_77, 0, x_61);
lean::cnstr_set(x_77, 1, x_72);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_74);
if (lean::is_scalar(x_71)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_71;
}
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
}
}
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(obj* x_0) {
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
x_7 = l_Lean_Elaborator_mangleIdent(x_2);
x_8 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_4);
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
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = level_mk_param(x_2);
x_9 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
x_10 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_9, x_0, x_2, x_8);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Lean_Elaborator_elabDefLike___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
x_18 = lean::cnstr_get(x_1, 8);
if (lean::is_exclusive(x_1)) {
 x_20 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_21);
x_25 = l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__3(x_8, x_24);
if (lean::is_scalar(x_20)) {
 x_26 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_26 = x_20;
}
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_25);
lean::cnstr_set(x_26, 4, x_10);
lean::cnstr_set(x_26, 5, x_12);
lean::cnstr_set(x_26, 6, x_14);
lean::cnstr_set(x_26, 7, x_16);
lean::cnstr_set(x_26, 8, x_18);
return x_26;
}
}
obj* _init_l_Lean_Elaborator_elabDefLike___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elabDefLike: unexpected input");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_elabDefLike___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("defs");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* l_Lean_Elaborator_elabDefLike(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_0);
x_17 = l_Lean_Elaborator_elabDefLike___closed__1;
x_18 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_16, x_17, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_16);
return x_18;
}
else
{
obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_31; obj* x_34; obj* x_36; 
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_2, 4);
lean::inc(x_25);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_7, 1);
lean::inc(x_28);
lean::dec(x_7);
x_31 = lean::cnstr_get(x_9, 0);
lean::inc(x_31);
lean::dec(x_9);
x_34 = lean::box(0);
lean::inc(x_5);
x_36 = l_Lean_Elaborator_declModifiersToPexpr(x_1, x_4, x_5, x_6);
if (lean::obj_tag(x_36) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
x_45 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_47 = x_36;
} else {
 lean::inc(x_45);
 lean::dec(x_36);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_36, 0);
lean::inc(x_49);
lean::dec(x_36);
x_52 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_set(x_49, 0, lean::box(0));
 lean::cnstr_set(x_49, 1, lean::box(0));
 x_56 = x_49;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_49);
 x_56 = lean::box(0);
}
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_3);
x_58 = lean_expr_mk_lit(x_57);
if (lean::obj_tag(x_21) == 0)
{
obj* x_61; obj* x_62; 
x_61 = lean::box(0);
if (lean::is_scalar(x_56)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_56;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_54);
x_59 = x_62;
goto lbl_60;
}
else
{
obj* x_64; obj* x_66; obj* x_68; 
lean::dec(x_56);
x_64 = lean::cnstr_get(x_21, 0);
lean::inc(x_64);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_66, 0, x_64);
lean::inc(x_5);
x_68 = l_Lean_Elaborator_modifyCurrentScope(x_66, x_4, x_5, x_54);
if (lean::obj_tag(x_68) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
lean::dec(x_58);
lean::dec(x_52);
x_78 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_80 = x_68;
} else {
 lean::inc(x_78);
 lean::dec(x_68);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_68, 0);
lean::inc(x_82);
lean::dec(x_68);
x_59 = x_82;
goto lbl_60;
}
}
lbl_60:
{
obj* x_85; obj* x_88; obj* x_91; obj* x_92; obj* x_95; obj* x_96; 
x_85 = lean::cnstr_get(x_59, 1);
lean::inc(x_85);
lean::dec(x_59);
x_88 = lean::cnstr_get(x_23, 0);
lean::inc(x_88);
lean::dec(x_23);
x_91 = l_Lean_Elaborator_mangleIdent(x_88);
x_92 = l_Lean_Expander_getOptType___main(x_28);
lean::dec(x_28);
lean::inc(x_5);
x_95 = l_Lean_Elaborator_toPexpr___main(x_92, x_4, x_5, x_85);
if (lean::obj_tag(x_21) == 0)
{
x_96 = x_34;
goto lbl_97;
}
else
{
obj* x_98; obj* x_101; obj* x_104; 
x_98 = lean::cnstr_get(x_21, 0);
lean::inc(x_98);
lean::dec(x_21);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
x_104 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_101);
x_96 = x_104;
goto lbl_97;
}
lbl_97:
{
if (lean::obj_tag(x_95) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_91);
lean::dec(x_25);
lean::dec(x_58);
lean::dec(x_52);
lean::dec(x_96);
x_113 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_115 = x_95;
} else {
 lean::inc(x_113);
 lean::dec(x_95);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
return x_116;
}
else
{
obj* x_117; obj* x_120; obj* x_121; obj* x_123; obj* x_125; uint8 x_126; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_117 = lean::cnstr_get(x_95, 0);
lean::inc(x_117);
lean::dec(x_95);
x_120 = l_Lean_Elaborator_namesToPexpr(x_96);
x_121 = lean::cnstr_get(x_117, 0);
x_123 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_set(x_117, 0, lean::box(0));
 lean::cnstr_set(x_117, 1, lean::box(0));
 x_125 = x_117;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::dec(x_117);
 x_125 = lean::box(0);
}
x_126 = 4;
lean::inc(x_121);
lean::inc(x_91);
lean::inc(x_91);
x_130 = lean_expr_local(x_91, x_91, x_121, x_126);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_34);
x_132 = l_Lean_Elaborator_mkEqns___closed__1;
x_133 = l_Lean_Expr_mkCapp(x_132, x_131);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_139; obj* x_142; obj* x_146; 
lean::dec(x_91);
lean::dec(x_125);
lean::dec(x_121);
x_139 = lean::cnstr_get(x_25, 0);
lean::inc(x_139);
lean::dec(x_25);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
lean::inc(x_5);
x_146 = l_Lean_Elaborator_toPexpr___main(x_142, x_4, x_5, x_123);
if (lean::obj_tag(x_146) == 0)
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_52);
lean::dec(x_120);
lean::dec(x_133);
x_154 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_156 = x_146;
} else {
 lean::inc(x_154);
 lean::dec(x_146);
 x_156 = lean::box(0);
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_154);
return x_157;
}
else
{
obj* x_158; 
x_158 = lean::cnstr_get(x_146, 0);
lean::inc(x_158);
lean::dec(x_146);
x_134 = x_158;
goto lbl_135;
}
}
case 1:
{
obj* x_163; obj* x_164; 
lean::dec(x_91);
lean::dec(x_25);
x_163 = l_Lean_Elaborator_mkEqns(x_121, x_34);
if (lean::is_scalar(x_125)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_125;
}
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_123);
x_134 = x_164;
goto lbl_135;
}
default:
{
obj* x_166; obj* x_170; 
lean::dec(x_125);
x_166 = lean::cnstr_get(x_25, 0);
lean::inc(x_166);
lean::dec(x_25);
lean::inc(x_5);
x_170 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_91, x_166, x_4, x_5, x_123);
if (lean::obj_tag(x_170) == 0)
{
obj* x_179; obj* x_181; obj* x_182; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_52);
lean::dec(x_120);
lean::dec(x_121);
lean::dec(x_133);
x_179 = lean::cnstr_get(x_170, 0);
if (lean::is_exclusive(x_170)) {
 x_181 = x_170;
} else {
 lean::inc(x_179);
 lean::dec(x_170);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_179);
return x_182;
}
else
{
obj* x_183; obj* x_186; obj* x_188; obj* x_190; obj* x_191; obj* x_192; 
x_183 = lean::cnstr_get(x_170, 0);
lean::inc(x_183);
lean::dec(x_170);
x_186 = lean::cnstr_get(x_183, 0);
x_188 = lean::cnstr_get(x_183, 1);
if (lean::is_exclusive(x_183)) {
 x_190 = x_183;
} else {
 lean::inc(x_186);
 lean::inc(x_188);
 lean::dec(x_183);
 x_190 = lean::box(0);
}
x_191 = l_Lean_Elaborator_mkEqns(x_121, x_186);
if (lean::is_scalar(x_190)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_190;
}
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_188);
x_134 = x_192;
goto lbl_135;
}
}
}
lbl_135:
{
obj* x_193; obj* x_195; obj* x_199; 
x_193 = lean::cnstr_get(x_134, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_134, 1);
lean::inc(x_195);
lean::dec(x_134);
lean::inc(x_5);
x_199 = l_Lean_Elaborator_simpleBindersToPexpr(x_31, x_4, x_5, x_195);
if (lean::obj_tag(x_199) == 0)
{
obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_193);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_52);
lean::dec(x_120);
lean::dec(x_133);
x_207 = lean::cnstr_get(x_199, 0);
if (lean::is_exclusive(x_199)) {
 x_209 = x_199;
} else {
 lean::inc(x_207);
 lean::dec(x_199);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
return x_210;
}
else
{
obj* x_211; obj* x_214; obj* x_216; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_211 = lean::cnstr_get(x_199, 0);
lean::inc(x_211);
lean::dec(x_199);
x_214 = lean::cnstr_get(x_211, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_211, 1);
lean::inc(x_216);
lean::dec(x_211);
x_219 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_219, 0, x_193);
lean::cnstr_set(x_219, 1, x_34);
x_220 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_220, 0, x_214);
lean::cnstr_set(x_220, 1, x_219);
x_221 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_221, 0, x_133);
lean::cnstr_set(x_221, 1, x_220);
x_222 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_222, 0, x_120);
lean::cnstr_set(x_222, 1, x_221);
x_223 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_223, 0, x_58);
lean::cnstr_set(x_223, 1, x_222);
x_224 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_224, 0, x_52);
lean::cnstr_set(x_224, 1, x_223);
x_225 = l_Lean_Expr_mkCapp(x_132, x_224);
x_226 = l_Lean_Elaborator_elabDefLike___closed__2;
x_227 = lean_expr_mk_mdata(x_226, x_225);
x_228 = l_Lean_Elaborator_oldElabCommand(x_0, x_227, x_4, x_5, x_216);
lean::dec(x_0);
return x_228;
}
}
}
}
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Elaborator_elabDefLike___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Elaborator_elabDefLike(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* _init_l_Lean_Elaborator_inferModToPexpr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_inferModToPexpr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_inferModToPexpr___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(2ul);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_inferModToPexpr(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Elaborator_inferModToPexpr___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Elaborator_inferModToPexpr___closed__2;
return x_3;
}
else
{
obj* x_4; 
x_4 = l_Lean_Elaborator_inferModToPexpr___closed__3;
return x_4;
}
}
}
}
obj* l_Lean_Elaborator_inferModToPexpr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_inferModToPexpr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_20; obj* x_23; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
x_23 = lean::apply_4(x_1, x_18, x_2, x_3, x_20);
return x_23;
}
}
}
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("declaration.elaborate: unexpected input");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_14 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_17 = lean::cnstr_get(x_10, 3);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_19);
x_24 = lean::box(0);
x_15 = x_24;
goto lbl_16;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_19, 0);
lean::inc(x_25);
lean::dec(x_19);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; 
lean::dec(x_10);
x_32 = lean::box(0);
x_15 = x_32;
goto lbl_16;
}
else
{
obj* x_34; obj* x_37; obj* x_41; 
lean::dec(x_14);
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
lean::dec(x_28);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
lean::inc(x_3);
x_41 = l_Lean_Elaborator_toPexpr___main(x_37, x_2, x_3, x_4);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_12);
x_46 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; obj* x_61; uint8 x_62; obj* x_64; obj* x_65; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::cnstr_get(x_10, 1);
lean::inc(x_58);
lean::dec(x_10);
x_61 = l_Lean_Elaborator_mangleIdent(x_58);
x_62 = 0;
lean::inc(x_61);
x_64 = lean_expr_local(x_61, x_61, x_53, x_62);
x_65 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(x_0, x_12, x_2, x_3, x_55);
if (lean::obj_tag(x_65) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_64);
x_67 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_69 = x_65;
} else {
 lean::inc(x_67);
 lean::dec(x_65);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
return x_70;
}
else
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_71 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_73 = x_65;
} else {
 lean::inc(x_71);
 lean::dec(x_65);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_71, 0);
x_76 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_78 = x_71;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_71);
 x_78 = lean::box(0);
}
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_64);
lean::cnstr_set(x_79, 1, x_74);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_73;
}
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
else
{
obj* x_85; 
lean::dec(x_25);
lean::dec(x_10);
lean::dec(x_17);
x_85 = lean::box(0);
x_15 = x_85;
goto lbl_16;
}
}
lbl_16:
{
obj* x_88; obj* x_89; obj* x_91; 
lean::dec(x_15);
lean::inc(x_0);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_0);
x_89 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_91 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_88, x_89, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_88);
if (lean::obj_tag(x_91) == 0)
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_98 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_100 = x_91;
} else {
 lean::inc(x_98);
 lean::dec(x_91);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_105; obj* x_107; obj* x_110; 
x_102 = lean::cnstr_get(x_91, 0);
lean::inc(x_102);
lean::dec(x_91);
x_105 = lean::cnstr_get(x_102, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_102, 1);
lean::inc(x_107);
lean::dec(x_102);
x_110 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(x_0, x_12, x_2, x_3, x_107);
if (lean::obj_tag(x_110) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_14);
lean::dec(x_105);
x_113 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_115 = x_110;
} else {
 lean::inc(x_113);
 lean::dec(x_110);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
return x_116;
}
else
{
obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_117 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_119 = x_110;
} else {
 lean::inc(x_117);
 lean::dec(x_110);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_117, 0);
x_122 = lean::cnstr_get(x_117, 1);
if (lean::is_exclusive(x_117)) {
 x_124 = x_117;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_117);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_125 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_125 = x_14;
}
lean::cnstr_set(x_125, 0, x_105);
lean::cnstr_set(x_125, 1, x_120);
if (lean::is_scalar(x_124)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_124;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_122);
if (lean::is_scalar(x_119)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_119;
}
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
}
}
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_declaration_elaborate___spec__3(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_12; obj* x_13; 
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
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_Lean_Elaborator_inferModToPexpr(x_7);
lean::dec(x_7);
x_12 = l_List_map___main___at_Lean_Elaborator_declaration_elaborate___spec__3(x_4);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
lean::inc(x_2);
x_17 = l_Lean_Elaborator_toPexpr___main(x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_23 = x_17;
} else {
 lean::inc(x_21);
 lean::dec(x_17);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_12);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
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
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_16 = x_2;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_22);
lean::inc(x_0);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_0);
x_28 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1;
lean::inc(x_4);
x_30 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_27, x_28, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
return x_41;
}
else
{
obj* x_42; 
x_42 = lean::cnstr_get(x_30, 0);
lean::inc(x_42);
lean::dec(x_30);
x_17 = x_42;
goto lbl_18;
}
}
else
{
obj* x_45; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_45 = lean::cnstr_get(x_22, 0);
lean::inc(x_45);
lean::dec(x_22);
x_48 = 0;
x_49 = lean::box(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_45);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_5);
x_17 = x_51;
goto lbl_18;
}
}
case 1:
{
obj* x_52; obj* x_55; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_12, 0);
lean::inc(x_52);
lean::dec(x_12);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = 1;
x_59 = lean::box(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_5);
x_17 = x_61;
goto lbl_18;
}
case 2:
{
obj* x_62; obj* x_65; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_12, 0);
lean::inc(x_62);
lean::dec(x_12);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = 2;
x_69 = lean::box(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
x_17 = x_71;
goto lbl_18;
}
default:
{
obj* x_72; obj* x_75; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; 
x_72 = lean::cnstr_get(x_12, 0);
lean::inc(x_72);
lean::dec(x_12);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
x_78 = 3;
x_79 = lean::box(x_78);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_75);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_5);
x_17 = x_81;
goto lbl_18;
}
}
lbl_18:
{
obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_92; uint8 x_93; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_105; obj* x_108; obj* x_111; obj* x_114; 
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_17, 1);
lean::inc(x_84);
lean::dec(x_17);
x_87 = lean::cnstr_get(x_82, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_82, 1);
lean::inc(x_89);
lean::dec(x_82);
x_92 = l_Lean_Elaborator_dummy;
x_93 = lean::unbox(x_87);
lean::inc(x_1);
lean::inc(x_1);
x_96 = lean_expr_local(x_1, x_1, x_92, x_93);
x_97 = lean::cnstr_get(x_89, 0);
lean::inc(x_97);
x_99 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_97);
x_100 = l_Lean_Elaborator_namesToPexpr(x_99);
x_101 = lean::cnstr_get(x_89, 1);
lean::inc(x_101);
x_103 = l_Lean_Elaborator_inferModToPexpr(x_101);
lean::dec(x_101);
x_105 = lean::cnstr_get(x_89, 2);
lean::inc(x_105);
lean::dec(x_89);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
x_111 = l_Lean_Expander_getOptType___main(x_108);
lean::dec(x_108);
lean::inc(x_4);
x_114 = l_Lean_Elaborator_toPexpr___main(x_111, x_3, x_4, x_84);
if (lean::obj_tag(x_114) == 0)
{
obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_96);
lean::dec(x_103);
lean::dec(x_100);
x_123 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_125 = x_114;
} else {
 lean::inc(x_123);
 lean::dec(x_114);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
return x_126;
}
else
{
obj* x_127; obj* x_130; obj* x_132; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_141; obj* x_142; 
x_127 = lean::cnstr_get(x_114, 0);
lean::inc(x_127);
lean::dec(x_114);
x_130 = lean::cnstr_get(x_127, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_127, 1);
lean::inc(x_132);
lean::dec(x_127);
x_135 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_16;
}
lean::cnstr_set(x_136, 0, x_130);
lean::cnstr_set(x_136, 1, x_135);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_103);
lean::cnstr_set(x_137, 1, x_136);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_100);
lean::cnstr_set(x_138, 1, x_137);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_96);
lean::cnstr_set(x_139, 1, x_138);
lean::inc(x_1);
x_141 = l_Lean_Expr_mkCapp(x_1, x_139);
x_142 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5(x_0, x_1, x_14, x_3, x_4, x_132);
if (lean::obj_tag(x_142) == 0)
{
obj* x_144; obj* x_146; obj* x_147; 
lean::dec(x_141);
x_144 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 x_146 = x_142;
} else {
 lean::inc(x_144);
 lean::dec(x_142);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_144);
return x_147;
}
else
{
obj* x_148; obj* x_150; obj* x_151; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_148 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 x_150 = x_142;
} else {
 lean::inc(x_148);
 lean::dec(x_142);
 x_150 = lean::box(0);
}
x_151 = lean::cnstr_get(x_148, 0);
x_153 = lean::cnstr_get(x_148, 1);
if (lean::is_exclusive(x_148)) {
 x_155 = x_148;
} else {
 lean::inc(x_151);
 lean::inc(x_153);
 lean::dec(x_148);
 x_155 = lean::box(0);
}
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_141);
lean::cnstr_set(x_156, 1, x_151);
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_153);
if (lean::is_scalar(x_150)) {
 x_158 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_158 = x_150;
}
lean::cnstr_set(x_158, 0, x_157);
return x_158;
}
}
}
}
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_14; 
x_9 = l_Lean_Elaborator_identUnivParamsToPexpr(x_0);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_7);
x_14 = l_Lean_Elaborator_toPexpr___main(x_10, x_6, x_7, x_8);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_22 = x_14;
} else {
 lean::inc(x_20);
 lean::dec(x_14);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_2);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_9);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Elaborator_mkEqns___closed__1;
x_36 = l_Lean_Expr_mkCapp(x_35, x_34);
x_37 = lean_expr_mk_mdata(x_3, x_36);
x_38 = l_Lean_Elaborator_oldElabCommand(x_4, x_37, x_6, x_7, x_29);
return x_38;
}
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; obj* x_15; 
x_15 = lean::cnstr_get(x_8, 1);
if (lean::obj_tag(x_15) == 0)
{
lean::inc(x_0);
x_13 = x_0;
goto lbl_14;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_13 = x_18;
goto lbl_14;
}
lbl_14:
{
obj* x_21; 
lean::inc(x_11);
x_21 = l_Lean_Elaborator_attrsToPexpr(x_13, x_10, x_11, x_12);
if (lean::obj_tag(x_21) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_33 = x_21;
} else {
 lean::inc(x_31);
 lean::dec(x_21);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_35 = lean::cnstr_get(x_21, 0);
lean::inc(x_35);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_35, 0);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
 lean::cnstr_set(x_35, 1, lean::box(0));
 x_42 = x_35;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
lean::inc(x_0);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_0);
x_45 = l_Lean_Elaborator_mkEqns___closed__1;
x_46 = l_Lean_Expr_mkCapp(x_45, x_44);
if (lean::obj_tag(x_7) == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_42;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_40);
x_47 = x_50;
goto lbl_48;
}
else
{
obj* x_52; obj* x_54; obj* x_56; 
lean::dec(x_42);
x_52 = lean::cnstr_get(x_7, 0);
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_54, 0, x_52);
lean::inc(x_11);
x_56 = l_Lean_Elaborator_modifyCurrentScope(x_54, x_10, x_11, x_40);
if (lean::obj_tag(x_56) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
x_67 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_69 = x_56;
} else {
 lean::inc(x_67);
 lean::dec(x_56);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_56, 0);
lean::inc(x_71);
lean::dec(x_56);
x_47 = x_71;
goto lbl_48;
}
}
lbl_48:
{
obj* x_74; obj* x_77; obj* x_80; obj* x_81; obj* x_83; obj* x_84; 
x_74 = lean::cnstr_get(x_47, 1);
lean::inc(x_74);
lean::dec(x_47);
x_77 = lean::cnstr_get(x_1, 0);
lean::inc(x_77);
lean::dec(x_1);
x_80 = l_Lean_Elaborator_mangleIdent(x_77);
x_81 = l_Lean_Expander_getOptType___main(x_2);
lean::inc(x_11);
x_83 = l_Lean_Elaborator_toPexpr___main(x_81, x_10, x_11, x_74);
if (lean::obj_tag(x_7) == 0)
{
lean::inc(x_0);
x_84 = x_0;
goto lbl_85;
}
else
{
obj* x_87; obj* x_90; obj* x_93; 
x_87 = lean::cnstr_get(x_7, 0);
lean::inc(x_87);
lean::dec(x_7);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_90);
x_84 = x_93;
goto lbl_85;
}
lbl_85:
{
if (lean::obj_tag(x_83) == 0)
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
lean::dec(x_80);
lean::dec(x_84);
x_104 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_106 = x_83;
} else {
 lean::inc(x_104);
 lean::dec(x_83);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
return x_107;
}
else
{
obj* x_108; obj* x_111; obj* x_112; obj* x_114; uint8 x_117; obj* x_119; obj* x_121; obj* x_122; obj* x_124; 
x_108 = lean::cnstr_get(x_83, 0);
lean::inc(x_108);
lean::dec(x_83);
x_111 = l_Lean_Elaborator_namesToPexpr(x_84);
x_112 = lean::cnstr_get(x_108, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_108, 1);
lean::inc(x_114);
lean::dec(x_108);
x_117 = 0;
lean::inc(x_80);
x_119 = lean_expr_local(x_80, x_80, x_112, x_117);
lean::inc(x_0);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_0);
x_122 = l_Lean_Expr_mkCapp(x_45, x_121);
lean::inc(x_11);
x_124 = l_Lean_Elaborator_simpleBindersToPexpr(x_3, x_10, x_11, x_114);
if (lean::obj_tag(x_124) == 0)
{
obj* x_134; obj* x_136; obj* x_137; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_46);
lean::dec(x_111);
lean::dec(x_122);
x_134 = lean::cnstr_get(x_124, 0);
if (lean::is_exclusive(x_124)) {
 x_136 = x_124;
} else {
 lean::inc(x_134);
 lean::dec(x_124);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_134);
return x_137;
}
else
{
obj* x_138; obj* x_141; obj* x_143; obj* x_149; 
x_138 = lean::cnstr_get(x_124, 0);
lean::inc(x_138);
lean::dec(x_124);
x_141 = lean::cnstr_get(x_138, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_138, 1);
lean::inc(x_143);
lean::dec(x_138);
lean::inc(x_11);
lean::inc(x_5);
lean::inc(x_4);
x_149 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(x_4, x_5, x_10, x_11, x_143);
if (lean::obj_tag(x_149) == 0)
{
obj* x_160; obj* x_162; obj* x_163; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_46);
lean::dec(x_111);
lean::dec(x_141);
lean::dec(x_122);
x_160 = lean::cnstr_get(x_149, 0);
if (lean::is_exclusive(x_149)) {
 x_162 = x_149;
} else {
 lean::inc(x_160);
 lean::dec(x_149);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
return x_163;
}
else
{
obj* x_164; obj* x_167; obj* x_169; obj* x_172; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_164 = lean::cnstr_get(x_149, 0);
lean::inc(x_164);
lean::dec(x_149);
x_167 = lean::cnstr_get(x_164, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
lean::dec(x_164);
x_172 = l_Lean_Expr_mkCapp(x_45, x_167);
lean::inc(x_0);
x_174 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_174, 0, x_172);
lean::cnstr_set(x_174, 1, x_0);
x_175 = l_Lean_Expr_mkCapp(x_45, x_174);
x_176 = l_List_map___main___at_Lean_Elaborator_declaration_elaborate___spec__3(x_5);
x_177 = l_Lean_Expr_mkCapp(x_45, x_176);
lean::inc(x_0);
x_179 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_179, 0, x_177);
lean::cnstr_set(x_179, 1, x_0);
x_180 = l_Lean_Expr_mkCapp(x_45, x_179);
x_181 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_0);
x_182 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_182, 0, x_175);
lean::cnstr_set(x_182, 1, x_181);
x_183 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_183, 0, x_141);
lean::cnstr_set(x_183, 1, x_182);
x_184 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_184, 0, x_122);
lean::cnstr_set(x_184, 1, x_183);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_111);
lean::cnstr_set(x_185, 1, x_184);
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_46);
lean::cnstr_set(x_186, 1, x_185);
x_187 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_187, 0, x_9);
lean::cnstr_set(x_187, 1, x_186);
x_188 = l_Lean_Expr_mkCapp(x_45, x_187);
x_189 = lean_expr_mk_mdata(x_6, x_188);
x_190 = l_Lean_Elaborator_oldElabCommand(x_4, x_189, x_10, x_11, x_169);
lean::dec(x_4);
return x_190;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_inferModToPexpr(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("mk");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
if (lean::obj_tag(x_9) == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
x_14 = x_17;
goto lbl_15;
}
else
{
obj* x_18; obj* x_20; obj* x_22; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_20, 0, x_18);
lean::inc(x_12);
x_22 = l_Lean_Elaborator_modifyCurrentScope(x_20, x_11, x_12, x_13);
if (lean::obj_tag(x_22) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_33 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_35 = x_22;
} else {
 lean::inc(x_33);
 lean::dec(x_22);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_22, 0);
lean::inc(x_37);
lean::dec(x_22);
x_14 = x_37;
goto lbl_15;
}
}
lbl_15:
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; uint8 x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; 
x_40 = lean::cnstr_get(x_14, 1);
lean::inc(x_40);
lean::dec(x_14);
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
lean::dec(x_0);
x_46 = l_Lean_Elaborator_mangleIdent(x_43);
x_47 = l_Lean_Elaborator_dummy;
x_48 = 0;
lean::inc(x_46);
x_50 = lean_expr_local(x_46, x_46, x_47, x_48);
x_51 = l_Lean_Expander_getOptType___main(x_1);
lean::inc(x_12);
x_53 = l_Lean_Elaborator_toPexpr___main(x_51, x_11, x_12, x_40);
if (lean::obj_tag(x_9) == 0)
{
lean::inc(x_6);
x_54 = x_6;
goto lbl_55;
}
else
{
obj* x_57; obj* x_60; obj* x_63; 
x_57 = lean::cnstr_get(x_9, 0);
lean::inc(x_57);
lean::dec(x_9);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
x_63 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_60);
x_54 = x_63;
goto lbl_55;
}
lbl_55:
{
if (lean::obj_tag(x_53) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_54);
lean::dec(x_50);
x_74 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_76 = x_53;
} else {
 lean::inc(x_74);
 lean::dec(x_53);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_88; 
x_78 = lean::cnstr_get(x_53, 0);
lean::inc(x_78);
lean::dec(x_53);
x_81 = l_Lean_Elaborator_namesToPexpr(x_54);
x_82 = lean::cnstr_get(x_78, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_78, 1);
lean::inc(x_84);
lean::dec(x_78);
lean::inc(x_12);
x_88 = l_Lean_Elaborator_simpleBindersToPexpr(x_2, x_11, x_12, x_84);
if (lean::obj_tag(x_88) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_82);
lean::dec(x_81);
lean::dec(x_50);
x_99 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_101 = x_88;
} else {
 lean::inc(x_99);
 lean::dec(x_88);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
return x_102;
}
else
{
obj* x_103; obj* x_106; obj* x_108; obj* x_111; 
x_103 = lean::cnstr_get(x_88, 0);
lean::inc(x_103);
lean::dec(x_88);
x_106 = lean::cnstr_get(x_103, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_103, 1);
lean::inc(x_108);
lean::dec(x_103);
if (lean::obj_tag(x_8) == 0)
{
lean::inc(x_6);
x_111 = x_6;
goto lbl_112;
}
else
{
obj* x_114; obj* x_115; 
x_114 = lean::cnstr_get(x_8, 0);
x_115 = lean::cnstr_get(x_114, 1);
lean::inc(x_115);
x_111 = x_115;
goto lbl_112;
}
lbl_112:
{
obj* x_118; 
lean::inc(x_12);
x_118 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4(x_111, x_11, x_12, x_108);
if (lean::obj_tag(x_118) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_82);
lean::dec(x_106);
lean::dec(x_81);
lean::dec(x_50);
x_130 = lean::cnstr_get(x_118, 0);
if (lean::is_exclusive(x_118)) {
 x_132 = x_118;
} else {
 lean::inc(x_130);
 lean::dec(x_118);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
return x_133;
}
else
{
obj* x_134; obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_146; obj* x_147; 
x_134 = lean::cnstr_get(x_118, 0);
lean::inc(x_134);
lean::dec(x_118);
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_134, 1);
lean::inc(x_139);
lean::dec(x_134);
x_142 = l_Lean_Elaborator_mkEqns___closed__1;
x_143 = l_Lean_Expr_mkCapp(x_142, x_137);
lean::inc(x_12);
lean::inc(x_3);
x_146 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5(x_3, x_142, x_4, x_11, x_12, x_139);
if (lean::obj_tag(x_5) == 0)
{
obj* x_149; 
x_149 = l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2;
x_147 = x_149;
goto lbl_148;
}
else
{
obj* x_150; obj* x_152; obj* x_155; 
x_150 = lean::cnstr_get(x_5, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_150, 0);
lean::inc(x_152);
lean::dec(x_150);
x_155 = l_Lean_Elaborator_mangleIdent(x_152);
x_147 = x_155;
goto lbl_148;
}
lbl_148:
{
obj* x_157; 
lean::inc(x_147);
x_157 = lean_expr_local(x_147, x_147, x_47, x_48);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_146) == 0)
{
obj* x_169; obj* x_171; obj* x_172; 
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_82);
lean::dec(x_106);
lean::dec(x_81);
lean::dec(x_50);
lean::dec(x_157);
lean::dec(x_143);
x_169 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_171 = x_146;
} else {
 lean::inc(x_169);
 lean::dec(x_146);
 x_171 = lean::box(0);
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_169);
return x_172;
}
else
{
obj* x_173; obj* x_176; obj* x_178; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_173 = lean::cnstr_get(x_146, 0);
lean::inc(x_173);
lean::dec(x_146);
x_176 = lean::cnstr_get(x_173, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_173, 1);
lean::inc(x_178);
lean::dec(x_173);
x_181 = l_Lean_Expr_mkCapp(x_142, x_176);
x_182 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_6);
x_183 = l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1;
x_184 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_182);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_157);
lean::cnstr_set(x_185, 1, x_184);
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_82);
lean::cnstr_set(x_186, 1, x_185);
x_187 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_187, 0, x_143);
lean::cnstr_set(x_187, 1, x_186);
x_188 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_188, 0, x_106);
lean::cnstr_set(x_188, 1, x_187);
x_189 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_189, 0, x_50);
lean::cnstr_set(x_189, 1, x_188);
x_190 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_190, 0, x_81);
lean::cnstr_set(x_190, 1, x_189);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_10);
lean::cnstr_set(x_191, 1, x_190);
x_192 = l_Lean_Expr_mkCapp(x_142, x_191);
x_193 = lean_expr_mk_mdata(x_7, x_192);
x_194 = l_Lean_Elaborator_oldElabCommand(x_3, x_193, x_11, x_12, x_178);
lean::dec(x_3);
return x_194;
}
}
else
{
if (lean::obj_tag(x_146) == 0)
{
obj* x_208; obj* x_210; obj* x_211; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_82);
lean::dec(x_106);
lean::dec(x_81);
lean::dec(x_50);
lean::dec(x_157);
lean::dec(x_143);
x_208 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_210 = x_146;
} else {
 lean::inc(x_208);
 lean::dec(x_146);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_208);
return x_211;
}
else
{
obj* x_212; obj* x_215; obj* x_218; obj* x_221; obj* x_223; obj* x_225; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
x_212 = lean::cnstr_get(x_5, 0);
lean::inc(x_212);
lean::dec(x_5);
x_215 = lean::cnstr_get(x_146, 0);
lean::inc(x_215);
lean::dec(x_146);
x_218 = lean::cnstr_get(x_212, 1);
lean::inc(x_218);
lean::dec(x_212);
x_221 = l_Lean_Elaborator_inferModToPexpr(x_218);
lean::dec(x_218);
x_223 = lean::cnstr_get(x_215, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_215, 1);
lean::inc(x_225);
lean::dec(x_215);
x_228 = l_Lean_Expr_mkCapp(x_142, x_223);
x_229 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_6);
x_230 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_230, 0, x_221);
lean::cnstr_set(x_230, 1, x_229);
x_231 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_231, 0, x_157);
lean::cnstr_set(x_231, 1, x_230);
x_232 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_232, 0, x_82);
lean::cnstr_set(x_232, 1, x_231);
x_233 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_233, 0, x_143);
lean::cnstr_set(x_233, 1, x_232);
x_234 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_234, 0, x_106);
lean::cnstr_set(x_234, 1, x_233);
x_235 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_235, 0, x_50);
lean::cnstr_set(x_235, 1, x_234);
x_236 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_236, 0, x_81);
lean::cnstr_set(x_236, 1, x_235);
x_237 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_237, 0, x_10);
lean::cnstr_set(x_237, 1, x_236);
x_238 = l_Lean_Expr_mkCapp(x_142, x_237);
x_239 = lean_expr_mk_mdata(x_7, x_238);
x_240 = l_Lean_Elaborator_oldElabCommand(x_3, x_239, x_11, x_12, x_225);
lean::dec(x_3);
return x_240;
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
obj* _init_l_Lean_Elaborator_declaration_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("def");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = lean::box(0);
x_3 = l_Lean_Name_toStringWithSep___main(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_Substring_ofString(x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("axiom");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("inductives");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_declaration_elaborate___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("structure");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* l_Lean_Elaborator_declaration_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
x_6 = l_Lean_Parser_command_declaration_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
lean::inc(x_0);
x_11 = lean::apply_1(x_7, x_0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_17);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_20);
lean::closure_set(x_24, 2, x_14);
lean::closure_set(x_24, 3, x_23);
x_25 = l_Lean_Elaborator_locally(x_24, x_1, x_2, x_3);
return x_25;
}
case 3:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_17);
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
lean::dec(x_11);
x_30 = lean::mk_nat_obj(0ul);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_31, 0, x_0);
lean::closure_set(x_31, 1, x_27);
lean::closure_set(x_31, 2, x_14);
lean::closure_set(x_31, 3, x_30);
x_32 = l_Lean_Elaborator_locally(x_31, x_1, x_2, x_3);
return x_32;
}
case 4:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_17);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::mk_nat_obj(2ul);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_38, 0, x_0);
lean::closure_set(x_38, 1, x_34);
lean::closure_set(x_38, 2, x_14);
lean::closure_set(x_38, 3, x_37);
x_39 = l_Lean_Elaborator_locally(x_38, x_1, x_2, x_3);
return x_39;
}
default:
{
obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_17);
x_41 = lean::cnstr_get(x_11, 0);
lean::inc(x_41);
lean::dec(x_11);
x_44 = lean::mk_nat_obj(6ul);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_45, 0, x_0);
lean::closure_set(x_45, 1, x_41);
lean::closure_set(x_45, 2, x_14);
lean::closure_set(x_45, 3, x_44);
x_46 = l_Lean_Elaborator_locally(x_45, x_1, x_2, x_3);
return x_46;
}
}
}
case 1:
{
obj* x_47; obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_64; 
x_47 = lean::cnstr_get(x_12, 0);
lean::inc(x_47);
lean::dec(x_12);
x_50 = lean::cnstr_get(x_11, 0);
lean::inc(x_50);
lean::dec(x_11);
x_53 = lean::box(0);
x_54 = lean::cnstr_get(x_47, 2);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_47, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_54, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_54, 1);
lean::inc(x_60);
lean::dec(x_54);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_60);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_58);
lean::cnstr_set(x_64, 1, x_63);
if (lean::obj_tag(x_56) == 0)
{
obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_65 = lean::cnstr_get(x_47, 3);
lean::inc(x_65);
lean::dec(x_47);
x_68 = l_Lean_Elaborator_declaration_elaborate___closed__1;
x_69 = l_Lean_Elaborator_declaration_elaborate___closed__2;
x_70 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_53);
lean::cnstr_set(x_70, 2, x_69);
lean::cnstr_set(x_70, 3, x_64);
lean::cnstr_set(x_70, 4, x_65);
x_71 = lean::mk_nat_obj(4ul);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_72, 0, x_0);
lean::closure_set(x_72, 1, x_50);
lean::closure_set(x_72, 2, x_70);
lean::closure_set(x_72, 3, x_71);
x_73 = l_Lean_Elaborator_locally(x_72, x_1, x_2, x_3);
return x_73;
}
else
{
obj* x_74; obj* x_77; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_74 = lean::cnstr_get(x_47, 3);
lean::inc(x_74);
lean::dec(x_47);
x_77 = lean::cnstr_get(x_56, 0);
lean::inc(x_77);
lean::dec(x_56);
x_80 = l_Lean_Elaborator_declaration_elaborate___closed__1;
x_81 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_53);
lean::cnstr_set(x_81, 2, x_77);
lean::cnstr_set(x_81, 3, x_64);
lean::cnstr_set(x_81, 4, x_74);
x_82 = lean::mk_nat_obj(4ul);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_83, 0, x_0);
lean::closure_set(x_83, 1, x_50);
lean::closure_set(x_83, 2, x_81);
lean::closure_set(x_83, 3, x_82);
x_84 = l_Lean_Elaborator_locally(x_83, x_1, x_2, x_3);
return x_84;
}
}
case 2:
{
obj* x_85; obj* x_88; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_99; obj* x_100; obj* x_101; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_85 = lean::cnstr_get(x_12, 0);
lean::inc(x_85);
lean::dec(x_12);
x_88 = lean::cnstr_get(x_11, 0);
lean::inc(x_88);
lean::dec(x_11);
x_91 = lean::box(0);
x_92 = lean::cnstr_get(x_85, 1);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_92, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_92, 1);
lean::inc(x_96);
lean::dec(x_92);
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_96);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_94);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::cnstr_get(x_85, 2);
lean::inc(x_101);
lean::dec(x_85);
x_104 = l_Lean_Elaborator_declaration_elaborate___closed__1;
x_105 = l_Lean_Elaborator_declaration_elaborate___closed__2;
x_106 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_91);
lean::cnstr_set(x_106, 2, x_105);
lean::cnstr_set(x_106, 3, x_100);
lean::cnstr_set(x_106, 4, x_101);
x_107 = lean::mk_nat_obj(3ul);
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_108, 0, x_0);
lean::closure_set(x_108, 1, x_88);
lean::closure_set(x_108, 2, x_106);
lean::closure_set(x_108, 3, x_107);
x_109 = l_Lean_Elaborator_locally(x_108, x_1, x_2, x_3);
return x_109;
}
case 3:
{
obj* x_110; obj* x_113; obj* x_115; 
x_110 = lean::cnstr_get(x_12, 0);
lean::inc(x_110);
lean::dec(x_12);
x_113 = lean::cnstr_get(x_110, 2);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_113, 0);
lean::inc(x_115);
if (lean::obj_tag(x_115) == 0)
{
obj* x_121; 
lean::dec(x_11);
lean::dec(x_113);
lean::dec(x_115);
lean::dec(x_110);
x_121 = lean::box(0);
x_4 = x_121;
goto lbl_5;
}
else
{
obj* x_122; 
x_122 = lean::cnstr_get(x_115, 0);
lean::inc(x_122);
lean::dec(x_115);
if (lean::obj_tag(x_122) == 0)
{
obj* x_125; obj* x_128; obj* x_131; obj* x_132; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_125 = lean::cnstr_get(x_110, 1);
lean::inc(x_125);
lean::dec(x_110);
x_128 = lean::cnstr_get(x_113, 1);
lean::inc(x_128);
lean::dec(x_113);
x_131 = lean::box(0);
x_132 = lean::cnstr_get(x_11, 0);
lean::inc(x_132);
lean::dec(x_11);
x_135 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_135, 0, x_132);
x_136 = l_Lean_Elaborator_declaration_elaborate___closed__3;
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declaration_elaborate___lambda__1___boxed), 9, 5);
lean::closure_set(x_137, 0, x_125);
lean::closure_set(x_137, 1, x_128);
lean::closure_set(x_137, 2, x_131);
lean::closure_set(x_137, 3, x_136);
lean::closure_set(x_137, 4, x_0);
x_138 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_138, 0, x_135);
lean::closure_set(x_138, 1, x_137);
x_139 = l_Lean_Elaborator_locally(x_138, x_1, x_2, x_3);
return x_139;
}
else
{
obj* x_144; 
lean::dec(x_11);
lean::dec(x_113);
lean::dec(x_122);
lean::dec(x_110);
x_144 = lean::box(0);
x_4 = x_144;
goto lbl_5;
}
}
}
case 4:
{
obj* x_145; obj* x_148; 
x_145 = lean::cnstr_get(x_12, 0);
lean::inc(x_145);
lean::dec(x_12);
x_148 = lean::cnstr_get(x_145, 0);
lean::inc(x_148);
if (lean::obj_tag(x_148) == 0)
{
obj* x_150; obj* x_152; 
x_150 = lean::cnstr_get(x_145, 4);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_150, 0);
lean::inc(x_152);
if (lean::obj_tag(x_152) == 0)
{
obj* x_158; 
lean::dec(x_145);
lean::dec(x_152);
lean::dec(x_150);
lean::dec(x_11);
x_158 = lean::box(0);
x_4 = x_158;
goto lbl_5;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_166; obj* x_169; obj* x_172; obj* x_173; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_159 = lean::cnstr_get(x_145, 2);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_145, 3);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_145, 6);
lean::inc(x_163);
lean::dec(x_145);
x_166 = lean::cnstr_get(x_150, 1);
lean::inc(x_166);
lean::dec(x_150);
x_169 = lean::cnstr_get(x_152, 0);
lean::inc(x_169);
lean::dec(x_152);
x_172 = lean::box(0);
x_173 = lean::cnstr_get(x_11, 0);
lean::inc(x_173);
lean::dec(x_11);
lean::inc(x_173);
x_177 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_177, 0, x_173);
x_178 = l_Lean_Elaborator_declaration_elaborate___closed__4;
x_179 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declaration_elaborate___lambda__2___boxed), 13, 9);
lean::closure_set(x_179, 0, x_172);
lean::closure_set(x_179, 1, x_161);
lean::closure_set(x_179, 2, x_166);
lean::closure_set(x_179, 3, x_169);
lean::closure_set(x_179, 4, x_0);
lean::closure_set(x_179, 5, x_163);
lean::closure_set(x_179, 6, x_178);
lean::closure_set(x_179, 7, x_159);
lean::closure_set(x_179, 8, x_173);
x_180 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_180, 0, x_177);
lean::closure_set(x_180, 1, x_179);
x_181 = l_Lean_Elaborator_locally(x_180, x_1, x_2, x_3);
return x_181;
}
}
else
{
obj* x_185; 
lean::dec(x_145);
lean::dec(x_148);
lean::dec(x_11);
x_185 = lean::box(0);
x_4 = x_185;
goto lbl_5;
}
}
default:
{
obj* x_186; obj* x_189; 
x_186 = lean::cnstr_get(x_12, 0);
lean::inc(x_186);
lean::dec(x_12);
x_189 = lean::cnstr_get(x_186, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_192; obj* x_194; 
lean::dec(x_189);
x_192 = lean::cnstr_get(x_186, 3);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_192, 0);
lean::inc(x_194);
if (lean::obj_tag(x_194) == 0)
{
obj* x_200; 
lean::dec(x_186);
lean::dec(x_194);
lean::dec(x_192);
lean::dec(x_11);
x_200 = lean::box(0);
x_4 = x_200;
goto lbl_5;
}
else
{
obj* x_201; obj* x_203; obj* x_205; obj* x_207; obj* x_209; obj* x_212; obj* x_215; obj* x_218; obj* x_219; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_201 = lean::cnstr_get(x_186, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_186, 2);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_186, 4);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_186, 6);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_186, 7);
lean::inc(x_209);
lean::dec(x_186);
x_212 = lean::cnstr_get(x_192, 1);
lean::inc(x_212);
lean::dec(x_192);
x_215 = lean::cnstr_get(x_194, 0);
lean::inc(x_215);
lean::dec(x_194);
x_218 = lean::box(0);
x_219 = lean::cnstr_get(x_11, 0);
lean::inc(x_219);
lean::dec(x_11);
x_222 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_222, 0, x_219);
x_223 = l_Lean_Elaborator_declaration_elaborate___closed__5;
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declaration_elaborate___lambda__3___boxed), 14, 10);
lean::closure_set(x_224, 0, x_203);
lean::closure_set(x_224, 1, x_212);
lean::closure_set(x_224, 2, x_215);
lean::closure_set(x_224, 3, x_0);
lean::closure_set(x_224, 4, x_209);
lean::closure_set(x_224, 5, x_207);
lean::closure_set(x_224, 6, x_218);
lean::closure_set(x_224, 7, x_223);
lean::closure_set(x_224, 8, x_205);
lean::closure_set(x_224, 9, x_201);
x_225 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_225, 0, x_222);
lean::closure_set(x_225, 1, x_224);
x_226 = l_Lean_Elaborator_locally(x_225, x_1, x_2, x_3);
return x_226;
}
}
else
{
obj* x_230; 
lean::dec(x_186);
lean::dec(x_189);
lean::dec(x_11);
x_230 = lean::box(0);
x_4 = x_230;
goto lbl_5;
}
}
}
lbl_5:
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_4);
x_232 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_232, 0, x_0);
x_233 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1;
x_234 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed), 5, 2);
lean::closure_set(x_234, 0, x_232);
lean::closure_set(x_234, 1, x_233);
x_235 = l_Lean_Elaborator_locally(x_234, x_1, x_2, x_3);
return x_235;
}
}
}
obj* l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Elaborator_declaration_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__5(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Elaborator_declaration_elaborate___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_6);
return x_9;
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; 
x_13 = l_Lean_Elaborator_declaration_elaborate___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean::dec(x_2);
lean::dec(x_8);
lean::dec(x_10);
return x_13;
}
}
obj* l_Lean_Elaborator_declaration_elaborate___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
x_14 = l_Lean_Elaborator_declaration_elaborate___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean::dec(x_1);
lean::dec(x_8);
lean::dec(x_11);
return x_14;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get(x_3, 2);
x_10 = lean::cnstr_get(x_3, 3);
x_12 = lean::cnstr_get(x_3, 4);
x_14 = lean::cnstr_get(x_3, 5);
x_16 = lean::cnstr_get(x_3, 6);
x_18 = lean::cnstr_get(x_3, 7);
x_20 = lean::cnstr_get(x_3, 8);
if (lean::is_exclusive(x_3)) {
 x_22 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_3);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_0, 0);
x_25 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_27 = x_0;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_0);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_1);
x_29 = x_28;
x_30 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
x_31 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_30, x_12, x_2, x_29);
if (lean::is_scalar(x_22)) {
 x_32 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_32 = x_22;
}
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_6);
lean::cnstr_set(x_32, 2, x_8);
lean::cnstr_set(x_32, 3, x_10);
lean::cnstr_set(x_32, 4, x_31);
lean::cnstr_set(x_32, 5, x_14);
lean::cnstr_set(x_32, 6, x_16);
lean::cnstr_set(x_32, 7, x_18);
lean::cnstr_set(x_32, 8, x_20);
return x_32;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_11 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_0);
 x_11 = lean::box(0);
}
lean::inc(x_7);
x_15 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_7);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_25 = x_16;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Expander_bindingAnnotationUpdate;
x_27 = l_Lean_Parser_Syntax_isOfKind___main(x_26, x_23);
lean::dec(x_23);
if (x_27 == 0)
{
uint8 x_31; obj* x_32; obj* x_33; 
lean::dec(x_18);
lean::dec(x_21);
x_31 = 1;
x_32 = lean::box(x_31);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_3);
x_12 = x_33;
goto lbl_13;
}
else
{
obj* x_36; 
lean::dec(x_25);
lean::inc(x_2);
x_36 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_18);
lean::dec(x_21);
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_61; 
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
x_55 = l_Lean_Elaborator_mangleIdent(x_21);
x_56 = lean::cnstr_get(x_50, 4);
lean::inc(x_56);
lean::dec(x_50);
x_59 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
lean::inc(x_55);
x_61 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_59, x_56, x_55);
if (lean::obj_tag(x_61) == 0)
{
obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_18);
x_63 = lean::box(0);
x_64 = l_Lean_Name_toString___closed__1;
lean::inc(x_55);
x_66 = l_Lean_Name_toStringWithSep___main(x_64, x_55);
x_67 = l_Lean_Parser_Substring_ofString(x_66);
x_68 = lean::box(0);
x_69 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_69, 0, x_63);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set(x_69, 2, x_55);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set(x_69, 4, x_68);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_72 = l_String_splitAux___main___closed__1;
lean::inc(x_2);
x_74 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_71, x_72, x_1, x_2, x_52);
lean::dec(x_52);
lean::dec(x_71);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_90; uint8 x_91; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_74, 0);
lean::inc(x_85);
lean::dec(x_74);
x_88 = lean::cnstr_get(x_85, 1);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_release(x_85, 0);
 x_90 = x_85;
} else {
 lean::inc(x_88);
 lean::dec(x_85);
 x_90 = lean::box(0);
}
x_91 = 0;
x_92 = lean::box(x_91);
if (lean::is_scalar(x_90)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_90;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_88);
x_12 = x_93;
goto lbl_13;
}
}
else
{
obj* x_94; obj* x_97; obj* x_100; obj* x_102; 
x_94 = lean::cnstr_get(x_61, 0);
lean::inc(x_94);
lean::dec(x_61);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1___boxed), 4, 3);
lean::closure_set(x_100, 0, x_97);
lean::closure_set(x_100, 1, x_18);
lean::closure_set(x_100, 2, x_55);
lean::inc(x_2);
x_102 = l_Lean_Elaborator_modifyCurrentScope(x_100, x_1, x_2, x_52);
if (lean::obj_tag(x_102) == 0)
{
obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_107 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_109 = x_102;
} else {
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
return x_110;
}
else
{
obj* x_111; obj* x_114; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; 
x_111 = lean::cnstr_get(x_102, 0);
lean::inc(x_111);
lean::dec(x_102);
x_114 = lean::cnstr_get(x_111, 1);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 x_116 = x_111;
} else {
 lean::inc(x_114);
 lean::dec(x_111);
 x_116 = lean::box(0);
}
x_117 = 0;
x_118 = lean::box(x_117);
if (lean::is_scalar(x_116)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_116;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_114);
x_12 = x_119;
goto lbl_13;
}
}
}
}
lbl_13:
{
obj* x_120; obj* x_122; obj* x_125; 
x_120 = lean::cnstr_get(x_12, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_12, 1);
lean::inc(x_122);
lean::dec(x_12);
x_125 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(x_9, x_1, x_2, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_120);
x_129 = lean::cnstr_get(x_125, 0);
if (lean::is_exclusive(x_125)) {
 x_131 = x_125;
} else {
 lean::inc(x_129);
 lean::dec(x_125);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_135; uint8 x_136; 
x_133 = lean::cnstr_get(x_125, 0);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_set(x_125, 0, lean::box(0));
 x_135 = x_125;
} else {
 lean::inc(x_133);
 lean::dec(x_125);
 x_135 = lean::box(0);
}
x_136 = lean::unbox(x_120);
if (x_136 == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_7);
lean::dec(x_11);
x_139 = lean::cnstr_get(x_133, 0);
x_141 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 x_143 = x_133;
} else {
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_133);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_139);
lean::cnstr_set(x_144, 1, x_141);
if (lean::is_scalar(x_135)) {
 x_145 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_145 = x_135;
}
lean::cnstr_set(x_145, 0, x_144);
return x_145;
}
else
{
obj* x_146; obj* x_148; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_146 = lean::cnstr_get(x_133, 0);
x_148 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 x_150 = x_133;
} else {
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_133);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_151 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_151 = x_11;
}
lean::cnstr_set(x_151, 0, x_7);
lean::cnstr_set(x_151, 1, x_146);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_148);
if (lean::is_scalar(x_135)) {
 x_153 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_153 = x_135;
}
lean::cnstr_set(x_153, 0, x_152);
return x_153;
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_variables_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("variables.elaborate: unexpected input");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_variables_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("variables");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* l_Lean_Elaborator_variables_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_4 = l_Lean_Parser_command_variables_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_16; obj* x_18; 
lean::dec(x_10);
lean::inc(x_0);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_0);
x_16 = l_Lean_Elaborator_variables_elaborate___closed__1;
lean::inc(x_2);
x_18 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_15, x_16, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_25 = x_18;
} else {
 lean::inc(x_23);
 lean::dec(x_18);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
return x_26;
}
else
{
obj* x_27; obj* x_30; obj* x_32; obj* x_36; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
lean::inc(x_2);
x_36 = l_Lean_Elaborator_simpleBindersToPexpr(x_30, x_1, x_2, x_32);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_0);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_41 = x_36;
} else {
 lean::inc(x_39);
 lean::dec(x_36);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
return x_42;
}
else
{
obj* x_43; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
lean::dec(x_36);
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = l_Lean_Elaborator_variables_elaborate___closed__2;
x_52 = lean_expr_mk_mdata(x_51, x_46);
x_53 = l_Lean_Elaborator_oldElabCommand(x_0, x_52, x_1, x_2, x_48);
lean::dec(x_0);
return x_53;
}
}
}
else
{
obj* x_55; obj* x_59; 
x_55 = lean::cnstr_get(x_10, 0);
lean::inc(x_55);
lean::dec(x_10);
lean::inc(x_2);
x_59 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(x_55, x_1, x_2, x_3);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_64 = x_59;
} else {
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
return x_65;
}
else
{
obj* x_66; obj* x_69; obj* x_71; obj* x_75; 
x_66 = lean::cnstr_get(x_59, 0);
lean::inc(x_66);
lean::dec(x_59);
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
lean::inc(x_2);
x_75 = l_Lean_Elaborator_simpleBindersToPexpr(x_69, x_1, x_2, x_71);
if (lean::obj_tag(x_75) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_2);
x_78 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_80 = x_75;
} else {
 lean::inc(x_78);
 lean::dec(x_75);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
lean::dec(x_75);
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
lean::dec(x_82);
x_90 = l_Lean_Elaborator_variables_elaborate___closed__2;
x_91 = lean_expr_mk_mdata(x_90, x_85);
x_92 = l_Lean_Elaborator_oldElabCommand(x_0, x_91, x_1, x_2, x_87);
lean::dec(x_0);
return x_92;
}
}
}
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_variables_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_variables_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_Lean_Elaborator_mangleIdent(x_2);
x_8 = lean::box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
x_18 = lean::cnstr_get(x_1, 8);
if (lean::is_exclusive(x_1)) {
 x_20 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(x_12, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_24);
lean::cnstr_set(x_25, 6, x_14);
lean::cnstr_set(x_25, 7, x_16);
lean::cnstr_set(x_25, 8, x_18);
return x_25;
}
}
obj* l_Lean_Elaborator_include_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_4 = l_Lean_Parser_command_include_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_include_elaborate___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_Lean_Elaborator_modifyCurrentScope(x_9, x_1, x_2, x_3);
return x_10;
}
}
obj* l_Lean_Elaborator_include_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_include_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_Module_header_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not implemented: imports");
return x_0;
}
}
obj* l_Lean_Elaborator_Module_header_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_4 = l_Lean_Parser_Module_header_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_0);
x_14 = l_Lean_Elaborator_Module_header_elaborate___closed__1;
x_15 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_13, x_14, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_13);
return x_15;
}
else
{
obj* x_18; obj* x_19; 
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_18 = x_10;
} else {
 lean::dec(x_10);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_3);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_19);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_0);
x_30 = l_Lean_Elaborator_Module_header_elaborate___closed__1;
x_31 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_29, x_30, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_29);
return x_31;
}
}
}
}
obj* l_Lean_Elaborator_Module_header_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_Module_header_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_precToNat___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0ul);
return x_1;
}
else
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_5);
return x_8;
}
}
}
obj* l_Lean_Elaborator_precToNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_precToNat___main(x_0);
return x_1;
}
}
obj* _init_l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("registerNotationTokens: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_13 = l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1;
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_5, 3);
lean::inc(x_19);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_8, 0);
lean::inc(x_22);
lean::dec(x_8);
x_25 = lean::cnstr_get(x_0, 1);
x_27 = lean::cnstr_get(x_0, 2);
x_29 = lean::cnstr_get(x_0, 3);
x_31 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_33 = x_0;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_0);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_14, 0);
x_36 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_38 = x_14;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_14);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_22, 1);
lean::inc(x_39);
lean::dec(x_22);
x_42 = l_String_trim(x_39);
lean::dec(x_39);
x_44 = l_Lean_Elaborator_precToNat___main(x_19);
x_45 = lean::box(0);
lean::inc(x_42);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
x_48 = lean::mk_nat_obj(0ul);
x_49 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_42, x_47, x_36, x_48);
lean::dec(x_42);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_49);
if (lean::is_scalar(x_33)) {
 x_52 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_52 = x_33;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_25);
lean::cnstr_set(x_52, 2, x_27);
lean::cnstr_set(x_52, 3, x_29);
lean::cnstr_set(x_52, 4, x_31);
x_0 = x_52;
x_1 = x_16;
goto _start;
}
}
}
}
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationTokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1(x_1, x_2);
return x_5;
}
}
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg(obj* x_0) {
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
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
}
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg), 1, 0);
return x_1;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("registerNotationParser: unreachable");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderIdent_Parser), 5, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binders_Parser), 5, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("registerNotationParser: unimplemented");
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
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
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; 
lean::dec(x_2);
x_15 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
x_7 = x_15;
goto lbl_8;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_25, 0, x_22);
x_26 = lean::mk_nat_obj(0ul);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_27, 0, x_22);
lean::closure_set(x_27, 1, x_26);
lean::closure_set(x_27, 2, x_25);
x_30 = lean::cnstr_get(x_2, 1);
lean::inc(x_30);
lean::dec(x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; 
x_33 = l_Lean_Expander_noExpansion___closed__1;
x_28 = x_33;
goto lbl_29;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_38; 
lean::dec(x_34);
x_38 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2;
x_28 = x_38;
goto lbl_29;
}
case 1:
{
obj* x_40; 
lean::dec(x_34);
x_40 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3;
x_28 = x_40;
goto lbl_29;
}
default:
{
obj* x_41; obj* x_44; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; 
x_47 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4;
x_28 = x_47;
goto lbl_29;
}
else
{
obj* x_48; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_set(x_44, 0, lean::box(0));
 x_50 = x_44;
} else {
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
switch (lean::obj_tag(x_51)) {
case 0:
{
obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
lean::dec(x_51);
x_57 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_54);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_58, 0, x_57);
if (lean::is_scalar(x_50)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_50;
}
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_28 = x_60;
goto lbl_29;
}
case 2:
{
obj* x_61; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_61 = lean::cnstr_get(x_51, 0);
lean::inc(x_61);
lean::dec(x_51);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Elaborator_precToNat___main(x_64);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_68, 0, x_67);
if (lean::is_scalar(x_50)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_50;
}
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_28 = x_70;
goto lbl_29;
}
default:
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_51);
x_73 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5;
x_28 = x_73;
goto lbl_29;
}
}
}
}
}
}
lbl_29:
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_27);
x_75 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_77 = x_28;
} else {
 lean::inc(x_75);
 lean::dec(x_28);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
x_7 = x_78;
goto lbl_8;
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_79 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_81 = x_28;
} else {
 lean::inc(x_79);
 lean::dec(x_28);
 x_81 = lean::box(0);
}
x_82 = l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg(x_79);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_27);
lean::cnstr_set(x_83, 1, x_82);
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_83);
x_7 = x_84;
goto lbl_8;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_6);
lean::dec(x_4);
x_87 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_89 = x_7;
} else {
 lean::inc(x_87);
 lean::dec(x_7);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; 
x_91 = lean::cnstr_get(x_7, 0);
lean::inc(x_91);
lean::dec(x_7);
x_94 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(x_4);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_6);
lean::dec(x_91);
x_97 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_99 = x_94;
} else {
 lean::inc(x_97);
 lean::dec(x_94);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_103 = x_94;
} else {
 lean::inc(x_101);
 lean::dec(x_94);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_6;
}
lean::cnstr_set(x_104, 0, x_91);
lean::cnstr_set(x_104, 1, x_101);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
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
x_7 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(obj* x_0) {
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed), 7, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(x_4);
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
obj* _init_l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_getLeading___boxed), 6, 0);
return x_0;
}
}
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::inc(x_5);
x_8 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_16 = x_8;
} else {
 lean::inc(x_14);
 lean::dec(x_8);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
else
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_23; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_23 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_30; 
x_24 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_release(x_5, 1);
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_39; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_26);
x_39 = l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
return x_39;
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_40 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_42 = x_8;
} else {
 lean::inc(x_40);
 lean::dec(x_8);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_30, 0);
lean::inc(x_43);
lean::dec(x_30);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_String_trim(x_46);
lean::dec(x_46);
x_51 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(x_40);
x_52 = l_List_join___main___rarg(x_51);
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_3, 0);
lean::inc(x_56);
lean::dec(x_3);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_26);
x_60 = lean::cnstr_get(x_2, 0);
x_62 = lean::cnstr_get(x_2, 1);
x_64 = lean::cnstr_get(x_2, 2);
x_66 = lean::cnstr_get(x_2, 3);
x_68 = lean::cnstr_get(x_2, 4);
if (lean::is_exclusive(x_2)) {
 x_70 = x_2;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_2);
 x_70 = lean::box(0);
}
x_71 = lean::box(0);
x_72 = lean_name_mk_string(x_71, x_49);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_73, 0, x_0);
lean::closure_set(x_73, 1, x_52);
x_74 = l_Lean_Parser_TokenMap_insert___rarg(x_62, x_72, x_73);
if (lean::is_scalar(x_70)) {
 x_75 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_75 = x_70;
}
lean::cnstr_set(x_75, 0, x_60);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set(x_75, 2, x_64);
lean::cnstr_set(x_75, 3, x_66);
lean::cnstr_set(x_75, 4, x_68);
if (lean::is_scalar(x_42)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_42;
}
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_56);
x_78 = lean::cnstr_get(x_2, 0);
x_80 = lean::cnstr_get(x_2, 1);
x_82 = lean::cnstr_get(x_2, 2);
x_84 = lean::cnstr_get(x_2, 3);
x_86 = lean::cnstr_get(x_2, 4);
if (lean::is_exclusive(x_2)) {
 x_88 = x_2;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::inc(x_82);
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_2);
 x_88 = lean::box(0);
}
x_89 = lean::box(0);
x_90 = lean_name_mk_string(x_89, x_49);
x_91 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(x_52);
x_92 = l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
if (lean::is_scalar(x_26)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_26;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3), 8, 2);
lean::closure_set(x_94, 0, x_0);
lean::closure_set(x_94, 1, x_93);
x_95 = l_Lean_Parser_TokenMap_insert___rarg(x_82, x_90, x_94);
if (lean::is_scalar(x_88)) {
 x_96 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_96 = x_88;
}
lean::cnstr_set(x_96, 0, x_78);
lean::cnstr_set(x_96, 1, x_80);
lean::cnstr_set(x_96, 2, x_95);
lean::cnstr_set(x_96, 3, x_84);
lean::cnstr_set(x_96, 4, x_86);
if (lean::is_scalar(x_42)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_42;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
else
{
obj* x_99; 
lean::dec(x_53);
x_99 = lean::cnstr_get(x_3, 0);
lean::inc(x_99);
lean::dec(x_3);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_26);
x_103 = lean::cnstr_get(x_2, 0);
x_105 = lean::cnstr_get(x_2, 1);
x_107 = lean::cnstr_get(x_2, 2);
x_109 = lean::cnstr_get(x_2, 3);
x_111 = lean::cnstr_get(x_2, 4);
if (lean::is_exclusive(x_2)) {
 x_113 = x_2;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::dec(x_2);
 x_113 = lean::box(0);
}
x_114 = lean::box(0);
x_115 = lean_name_mk_string(x_114, x_49);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_116, 0, x_0);
lean::closure_set(x_116, 1, x_52);
x_117 = l_Lean_Parser_TokenMap_insert___rarg(x_109, x_115, x_116);
if (lean::is_scalar(x_113)) {
 x_118 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_118 = x_113;
}
lean::cnstr_set(x_118, 0, x_103);
lean::cnstr_set(x_118, 1, x_105);
lean::cnstr_set(x_118, 2, x_107);
lean::cnstr_set(x_118, 3, x_117);
lean::cnstr_set(x_118, 4, x_111);
if (lean::is_scalar(x_42)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_42;
}
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
else
{
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_99);
x_121 = lean::cnstr_get(x_2, 0);
x_123 = lean::cnstr_get(x_2, 1);
x_125 = lean::cnstr_get(x_2, 2);
x_127 = lean::cnstr_get(x_2, 3);
x_129 = lean::cnstr_get(x_2, 4);
if (lean::is_exclusive(x_2)) {
 x_131 = x_2;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::inc(x_125);
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_2);
 x_131 = lean::box(0);
}
x_132 = lean::box(0);
x_133 = lean_name_mk_string(x_132, x_49);
x_134 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(x_52);
x_135 = l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
if (lean::is_scalar(x_26)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_26;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3), 8, 2);
lean::closure_set(x_137, 0, x_0);
lean::closure_set(x_137, 1, x_136);
x_138 = l_Lean_Parser_TokenMap_insert___rarg(x_129, x_133, x_137);
if (lean::is_scalar(x_131)) {
 x_139 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_139 = x_131;
}
lean::cnstr_set(x_139, 0, x_121);
lean::cnstr_set(x_139, 1, x_123);
lean::cnstr_set(x_139, 2, x_125);
lean::cnstr_set(x_139, 3, x_127);
lean::cnstr_set(x_139, 4, x_138);
if (lean::is_scalar(x_42)) {
 x_140 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_140 = x_42;
}
lean::cnstr_set(x_140, 0, x_139);
return x_140;
}
}
}
}
}
}
}
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_15; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
x_15 = l_Lean_Elaborator_CommandParserConfig_registerNotationTokens(x_13, x_0);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = l_Lean_Parser_command_reserveNotation_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_8);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::inc(x_3);
x_26 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_24, x_16, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_24);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_3);
lean::dec(x_10);
x_31 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_33 = x_26;
} else {
 lean::inc(x_31);
 lean::dec(x_26);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_26, 0);
lean::inc(x_35);
lean::dec(x_26);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_0 = x_38;
x_1 = x_10;
x_4 = x_40;
goto _start;
}
}
else
{
obj* x_45; 
lean::dec(x_8);
x_45 = lean::cnstr_get(x_15, 0);
lean::inc(x_45);
lean::dec(x_15);
x_0 = x_45;
x_1 = x_10;
goto _start;
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 2);
lean::inc(x_15);
x_17 = l_Lean_Elaborator_CommandParserConfig_registerNotationTokens(x_15, x_0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_22 = l_Lean_Parser_command_notation_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_13);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::inc(x_3);
x_29 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_27, x_19, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_3);
lean::dec(x_10);
x_34 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_36 = x_29;
} else {
 lean::inc(x_34);
 lean::dec(x_29);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_43; 
x_38 = lean::cnstr_get(x_29, 0);
lean::inc(x_38);
lean::dec(x_29);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
lean::dec(x_38);
x_0 = x_41;
x_1 = x_10;
x_4 = x_43;
goto _start;
}
}
else
{
obj* x_47; obj* x_50; obj* x_54; 
x_47 = lean::cnstr_get(x_17, 0);
lean::inc(x_47);
lean::dec(x_17);
x_50 = lean::cnstr_get(x_8, 0);
lean::inc(x_50);
lean::dec(x_8);
lean::inc(x_13);
x_54 = l_Lean_Elaborator_CommandParserConfig_registerNotationParser(x_50, x_13, x_47);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_65; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
lean::dec(x_54);
x_58 = l_Lean_Parser_command_notation_HasView;
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_13);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::inc(x_3);
x_65 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_63, x_55, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_63);
if (lean::obj_tag(x_65) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_3);
lean::dec(x_10);
x_70 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_72 = x_65;
} else {
 lean::inc(x_70);
 lean::dec(x_65);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
return x_73;
}
else
{
obj* x_74; obj* x_77; obj* x_79; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_77 = lean::cnstr_get(x_74, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_0 = x_77;
x_1 = x_10;
x_4 = x_79;
goto _start;
}
}
else
{
obj* x_84; 
lean::dec(x_13);
x_84 = lean::cnstr_get(x_54, 0);
lean::inc(x_84);
lean::dec(x_54);
x_0 = x_84;
x_1 = x_10;
goto _start;
}
}
}
}
}
obj* l_Lean_Elaborator_updateParserConfig(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; 
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_Lean_Elaborator_currentScope(x_0, x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_12, 1);
lean::inc(x_19);
lean::dec(x_12);
x_22 = lean::cnstr_get(x_15, 0);
x_24 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_26 = x_15;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_15);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_2, 0);
x_29 = lean::cnstr_get(x_2, 1);
x_31 = lean::cnstr_get(x_2, 2);
x_33 = lean::cnstr_get(x_2, 3);
x_35 = lean::cnstr_get(x_2, 4);
x_37 = lean::cnstr_get(x_2, 5);
x_39 = lean::cnstr_get(x_2, 7);
x_41 = lean::cnstr_get(x_2, 8);
x_43 = lean::cnstr_get(x_2, 9);
x_45 = lean::cnstr_get(x_2, 10);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 lean::cnstr_set(x_2, 4, lean::box(0));
 lean::cnstr_set(x_2, 5, lean::box(0));
 lean::cnstr_release(x_2, 6);
 lean::cnstr_set(x_2, 7, lean::box(0));
 lean::cnstr_set(x_2, 8, lean::box(0));
 lean::cnstr_set(x_2, 9, lean::box(0));
 lean::cnstr_set(x_2, 10, lean::box(0));
 x_47 = x_2;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_2);
 x_47 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_27);
x_50 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(x_22, x_27, x_0, x_1, x_19);
if (lean::obj_tag(x_50) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_1);
lean::dec(x_45);
lean::dec(x_47);
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
lean::dec(x_29);
lean::dec(x_31);
lean::dec(x_17);
lean::dec(x_24);
lean::dec(x_41);
lean::dec(x_43);
x_66 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_68 = x_50;
} else {
 lean::inc(x_66);
 lean::dec(x_50);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
return x_69;
}
else
{
obj* x_70; obj* x_73; obj* x_75; obj* x_78; obj* x_82; obj* x_83; 
x_70 = lean::cnstr_get(x_50, 0);
lean::inc(x_70);
lean::dec(x_50);
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_70, 1);
lean::inc(x_75);
lean::dec(x_70);
x_78 = lean::cnstr_get(x_17, 2);
lean::inc(x_78);
lean::dec(x_17);
lean::inc(x_29);
x_82 = l_List_append___rarg(x_29, x_78);
x_83 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(x_73, x_82, x_0, x_1, x_75);
if (lean::obj_tag(x_83) == 0)
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_45);
lean::dec(x_47);
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
lean::dec(x_29);
lean::dec(x_31);
lean::dec(x_24);
lean::dec(x_41);
lean::dec(x_43);
x_97 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_99 = x_83;
} else {
 lean::inc(x_97);
 lean::dec(x_83);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
return x_100;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_101 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_103 = x_83;
} else {
 lean::inc(x_101);
 lean::dec(x_83);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_101, 0);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 1);
 x_106 = x_101;
} else {
 lean::inc(x_104);
 lean::dec(x_101);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_26;
}
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set(x_107, 1, x_24);
if (lean::is_scalar(x_47)) {
 x_108 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_108 = x_47;
}
lean::cnstr_set(x_108, 0, x_27);
lean::cnstr_set(x_108, 1, x_29);
lean::cnstr_set(x_108, 2, x_31);
lean::cnstr_set(x_108, 3, x_33);
lean::cnstr_set(x_108, 4, x_35);
lean::cnstr_set(x_108, 5, x_37);
lean::cnstr_set(x_108, 6, x_107);
lean::cnstr_set(x_108, 7, x_39);
lean::cnstr_set(x_108, 8, x_41);
lean::cnstr_set(x_108, 9, x_43);
lean::cnstr_set(x_108, 10, x_45);
x_109 = lean::box(0);
if (lean::is_scalar(x_106)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_106;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_108);
if (lean::is_scalar(x_103)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_103;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Elaborator_updateParserConfig___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_updateParserConfig(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_Elaborator_postprocessNotationSpec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_maxPrec;
x_7 = l_Lean_Parser_number_View_ofNat(x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_Lean_Elaborator_postprocessNotationSpec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
return x_0;
}
else
{
obj* x_5; obj* x_7; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_14 = x_3;
} else {
 lean::inc(x_12);
 lean::dec(x_3);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_17 = x_5;
} else {
 lean::inc(x_15);
 lean::dec(x_5);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get(x_7, 1);
x_22 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 3);
 x_24 = x_7;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_7);
 x_24 = lean::box(0);
}
x_25 = l_Lean_Elaborator_postprocessNotationSpec___closed__1;
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_22);
lean::cnstr_set(x_26, 3, x_25);
if (lean::is_scalar(x_17)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_17;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_15);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_3);
return x_0;
}
}
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_Lean_Elaborator_reserveNotation_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_4 = l_Lean_Parser_command_reserveNotation_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_13 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Elaborator_postprocessNotationSpec(x_13);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::cnstr_get(x_3, 0);
x_20 = lean::cnstr_get(x_3, 1);
x_22 = lean::cnstr_get(x_3, 2);
x_24 = lean::cnstr_get(x_3, 3);
x_26 = lean::cnstr_get(x_3, 4);
x_28 = lean::cnstr_get(x_3, 5);
x_30 = lean::cnstr_get(x_3, 6);
x_32 = lean::cnstr_get(x_3, 7);
x_34 = lean::cnstr_get(x_3, 8);
x_36 = lean::cnstr_get(x_3, 9);
x_38 = lean::cnstr_get(x_3, 10);
if (lean::is_exclusive(x_3)) {
 x_40 = x_3;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_3);
 x_40 = lean::box(0);
}
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_17);
lean::cnstr_set(x_41, 1, x_18);
if (lean::is_scalar(x_40)) {
 x_42 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_42 = x_40;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_20);
lean::cnstr_set(x_42, 2, x_22);
lean::cnstr_set(x_42, 3, x_24);
lean::cnstr_set(x_42, 4, x_26);
lean::cnstr_set(x_42, 5, x_28);
lean::cnstr_set(x_42, 6, x_30);
lean::cnstr_set(x_42, 7, x_32);
lean::cnstr_set(x_42, 8, x_34);
lean::cnstr_set(x_42, 9, x_36);
lean::cnstr_set(x_42, 10, x_38);
x_43 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_42);
return x_43;
}
}
obj* l_Lean_Elaborator_reserveNotation_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_reserveNotation_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
uint8 l_Lean_Elaborator_matchPrecedence___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_1);
x_4 = 1;
return x_4;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_20; uint8 x_21; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_13);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
lean::dec(x_10);
x_20 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_17);
x_21 = lean::nat_dec_eq(x_16, x_20);
lean::dec(x_20);
lean::dec(x_16);
return x_21;
}
}
}
}
obj* l_Lean_Elaborator_matchPrecedence___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_matchPrecedence___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Elaborator_matchPrecedence(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Elaborator_matchPrecedence___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_matchPrecedence___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_matchPrecedence(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
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
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_2);
x_18 = lean::box(0);
x_7 = x_18;
goto lbl_8;
}
else
{
obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_11, 3);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
x_28 = lean::cnstr_get(x_19, 0);
x_30 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 lean::cnstr_set(x_19, 1, lean::box(0));
 x_32 = x_19;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_19);
 x_32 = lean::box(0);
}
x_35 = lean::cnstr_get(x_28, 1);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_43; 
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_32);
lean::dec(x_22);
lean::dec(x_25);
x_43 = lean::box(0);
x_7 = x_43;
goto lbl_8;
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_52; obj* x_54; obj* x_57; uint8 x_59; 
x_44 = lean::cnstr_get(x_28, 3);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
 x_48 = x_35;
} else {
 lean::inc(x_46);
 lean::dec(x_35);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_25, 1);
lean::inc(x_49);
lean::dec(x_25);
x_52 = l_String_trim(x_49);
lean::dec(x_49);
x_54 = lean::cnstr_get(x_46, 1);
lean::inc(x_54);
lean::dec(x_46);
x_57 = l_String_trim(x_54);
lean::dec(x_54);
x_59 = lean::string_dec_eq(x_52, x_57);
lean::dec(x_57);
lean::dec(x_52);
if (x_59 == 0)
{
obj* x_69; 
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_48);
lean::dec(x_32);
lean::dec(x_22);
lean::dec(x_44);
x_69 = lean::box(0);
x_7 = x_69;
goto lbl_8;
}
else
{
uint8 x_70; 
x_70 = l_Lean_Elaborator_matchPrecedence___main(x_22, x_44);
if (x_70 == 0)
{
obj* x_76; 
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_48);
lean::dec(x_32);
x_76 = lean::box(0);
x_7 = x_76;
goto lbl_8;
}
else
{
obj* x_77; 
x_77 = lean::cnstr_get(x_9, 1);
lean::inc(x_77);
lean::dec(x_9);
if (lean::obj_tag(x_77) == 0)
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_80; 
if (lean::is_scalar(x_48)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_48;
}
lean::cnstr_set(x_80, 0, x_30);
x_33 = x_80;
goto lbl_34;
}
else
{
obj* x_83; 
lean::dec(x_30);
lean::dec(x_48);
x_83 = lean::box(0);
x_33 = x_83;
goto lbl_34;
}
}
else
{
obj* x_85; obj* x_87; 
lean::dec(x_48);
x_85 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_set(x_77, 0, lean::box(0));
 x_87 = x_77;
} else {
 lean::inc(x_85);
 lean::dec(x_77);
 x_87 = lean::box(0);
}
switch (lean::obj_tag(x_85)) {
case 0:
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_90; 
lean::dec(x_85);
lean::dec(x_87);
x_90 = lean::box(0);
x_33 = x_90;
goto lbl_34;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_30, 0);
lean::inc(x_91);
switch (lean::obj_tag(x_91)) {
case 0:
{
obj* x_93; obj* x_96; obj* x_99; obj* x_102; uint8 x_105; 
x_93 = lean::cnstr_get(x_85, 0);
lean::inc(x_93);
lean::dec(x_85);
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_93, 1);
lean::inc(x_99);
lean::dec(x_93);
x_102 = lean::cnstr_get(x_96, 1);
lean::inc(x_102);
lean::dec(x_96);
x_105 = l_Lean_Elaborator_matchPrecedence___main(x_99, x_102);
if (x_105 == 0)
{
obj* x_108; 
lean::dec(x_30);
lean::dec(x_87);
x_108 = lean::box(0);
x_33 = x_108;
goto lbl_34;
}
else
{
obj* x_109; 
if (lean::is_scalar(x_87)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_87;
}
lean::cnstr_set(x_109, 0, x_30);
x_33 = x_109;
goto lbl_34;
}
}
default:
{
obj* x_114; 
lean::dec(x_30);
lean::dec(x_91);
lean::dec(x_85);
lean::dec(x_87);
x_114 = lean::box(0);
x_33 = x_114;
goto lbl_34;
}
}
}
}
case 1:
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_117; 
lean::dec(x_85);
lean::dec(x_87);
x_117 = lean::box(0);
x_33 = x_117;
goto lbl_34;
}
else
{
obj* x_118; 
x_118 = lean::cnstr_get(x_30, 0);
lean::inc(x_118);
switch (lean::obj_tag(x_118)) {
case 1:
{
obj* x_120; obj* x_123; obj* x_126; obj* x_129; uint8 x_132; 
x_120 = lean::cnstr_get(x_85, 0);
lean::inc(x_120);
lean::dec(x_85);
x_123 = lean::cnstr_get(x_118, 0);
lean::inc(x_123);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_120, 1);
lean::inc(x_126);
lean::dec(x_120);
x_129 = lean::cnstr_get(x_123, 1);
lean::inc(x_129);
lean::dec(x_123);
x_132 = l_Lean_Elaborator_matchPrecedence___main(x_126, x_129);
if (x_132 == 0)
{
obj* x_135; 
lean::dec(x_30);
lean::dec(x_87);
x_135 = lean::box(0);
x_33 = x_135;
goto lbl_34;
}
else
{
obj* x_136; 
if (lean::is_scalar(x_87)) {
 x_136 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_136 = x_87;
}
lean::cnstr_set(x_136, 0, x_30);
x_33 = x_136;
goto lbl_34;
}
}
default:
{
obj* x_141; 
lean::dec(x_30);
lean::dec(x_85);
lean::dec(x_87);
lean::dec(x_118);
x_141 = lean::box(0);
x_33 = x_141;
goto lbl_34;
}
}
}
}
default:
{
obj* x_142; obj* x_144; obj* x_145; 
x_142 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 lean::cnstr_set(x_85, 0, lean::box(0));
 x_144 = x_85;
} else {
 lean::inc(x_142);
 lean::dec(x_85);
 x_144 = lean::box(0);
}
if (lean::obj_tag(x_30) == 0)
{
obj* x_150; 
lean::dec(x_87);
lean::dec(x_142);
lean::dec(x_144);
x_150 = lean::box(0);
x_33 = x_150;
goto lbl_34;
}
else
{
obj* x_151; obj* x_153; 
x_151 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 x_153 = x_30;
} else {
 lean::inc(x_151);
 lean::dec(x_30);
 x_153 = lean::box(0);
}
switch (lean::obj_tag(x_151)) {
case 2:
{
obj* x_154; 
x_154 = lean::cnstr_get(x_142, 1);
lean::inc(x_154);
if (lean::obj_tag(x_154) == 0)
{
obj* x_156; obj* x_159; 
x_156 = lean::cnstr_get(x_151, 0);
lean::inc(x_156);
lean::dec(x_151);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
if (lean::obj_tag(x_159) == 0)
{
obj* x_163; 
lean::dec(x_153);
x_163 = lean::box(0);
x_145 = x_163;
goto lbl_146;
}
else
{
obj* x_164; obj* x_166; 
x_164 = lean::cnstr_get(x_159, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_164, 1);
lean::inc(x_166);
lean::dec(x_164);
switch (lean::obj_tag(x_166)) {
case 0:
{
obj* x_170; 
lean::dec(x_166);
if (lean::is_scalar(x_153)) {
 x_170 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_170 = x_153;
}
lean::cnstr_set(x_170, 0, x_159);
x_145 = x_170;
goto lbl_146;
}
default:
{
obj* x_174; 
lean::dec(x_159);
lean::dec(x_153);
lean::dec(x_166);
x_174 = lean::box(0);
x_145 = x_174;
goto lbl_146;
}
}
}
}
else
{
obj* x_176; obj* x_178; 
lean::dec(x_153);
x_176 = lean::cnstr_get(x_154, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_176, 1);
lean::inc(x_178);
lean::dec(x_176);
switch (lean::obj_tag(x_178)) {
case 0:
{
obj* x_181; obj* x_184; 
x_181 = lean::cnstr_get(x_151, 0);
lean::inc(x_181);
lean::dec(x_151);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
lean::dec(x_181);
if (lean::obj_tag(x_184) == 0)
{
obj* x_189; 
lean::dec(x_178);
lean::dec(x_154);
x_189 = lean::box(0);
x_145 = x_189;
goto lbl_146;
}
else
{
obj* x_190; obj* x_192; obj* x_193; 
x_190 = lean::cnstr_get(x_184, 0);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_set(x_184, 0, lean::box(0));
 x_192 = x_184;
} else {
 lean::inc(x_190);
 lean::dec(x_184);
 x_192 = lean::box(0);
}
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
switch (lean::obj_tag(x_193)) {
case 0:
{
obj* x_196; obj* x_199; obj* x_202; obj* x_203; uint8 x_204; 
x_196 = lean::cnstr_get(x_178, 0);
lean::inc(x_196);
lean::dec(x_178);
x_199 = lean::cnstr_get(x_193, 0);
lean::inc(x_199);
lean::dec(x_193);
x_202 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_196);
x_203 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_199);
x_204 = lean::nat_dec_eq(x_202, x_203);
lean::dec(x_203);
lean::dec(x_202);
if (x_204 == 0)
{
obj* x_209; 
lean::dec(x_192);
lean::dec(x_154);
x_209 = lean::box(0);
x_145 = x_209;
goto lbl_146;
}
else
{
obj* x_210; 
if (lean::is_scalar(x_192)) {
 x_210 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_210 = x_192;
}
lean::cnstr_set(x_210, 0, x_154);
x_145 = x_210;
goto lbl_146;
}
}
default:
{
obj* x_215; 
lean::dec(x_178);
lean::dec(x_193);
lean::dec(x_192);
lean::dec(x_154);
x_215 = lean::box(0);
x_145 = x_215;
goto lbl_146;
}
}
}
}
default:
{
obj* x_219; 
lean::dec(x_178);
lean::dec(x_154);
lean::dec(x_151);
x_219 = lean::box(0);
x_145 = x_219;
goto lbl_146;
}
}
}
}
default:
{
obj* x_225; 
lean::dec(x_87);
lean::dec(x_153);
lean::dec(x_151);
lean::dec(x_142);
lean::dec(x_144);
x_225 = lean::box(0);
x_33 = x_225;
goto lbl_34;
}
}
}
lbl_146:
{
if (lean::obj_tag(x_145) == 0)
{
obj* x_229; 
lean::dec(x_87);
lean::dec(x_142);
lean::dec(x_144);
x_229 = lean::box(0);
x_33 = x_229;
goto lbl_34;
}
else
{
obj* x_230; obj* x_232; obj* x_233; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_230 = lean::cnstr_get(x_145, 0);
if (lean::is_exclusive(x_145)) {
 x_232 = x_145;
} else {
 lean::inc(x_230);
 lean::dec(x_145);
 x_232 = lean::box(0);
}
x_233 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 1);
 x_235 = x_142;
} else {
 lean::inc(x_233);
 lean::dec(x_142);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
lean::cnstr_set(x_236, 1, x_230);
if (lean::is_scalar(x_144)) {
 x_237 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_237 = x_144;
}
lean::cnstr_set(x_237, 0, x_236);
if (lean::is_scalar(x_232)) {
 x_238 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_238 = x_232;
}
lean::cnstr_set(x_238, 0, x_237);
if (lean::is_scalar(x_87)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_87;
}
lean::cnstr_set(x_239, 0, x_238);
x_33 = x_239;
goto lbl_34;
}
}
}
}
}
}
}
}
lbl_34:
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_242; 
lean::dec(x_28);
lean::dec(x_32);
x_242 = lean::box(0);
x_7 = x_242;
goto lbl_8;
}
else
{
obj* x_243; obj* x_245; obj* x_246; obj* x_247; 
x_243 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_245 = x_33;
} else {
 lean::inc(x_243);
 lean::dec(x_33);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_32;
}
lean::cnstr_set(x_246, 0, x_28);
lean::cnstr_set(x_246, 1, x_243);
if (lean::is_scalar(x_245)) {
 x_247 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_247 = x_245;
}
lean::cnstr_set(x_247, 0, x_246);
x_7 = x_247;
goto lbl_8;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_250; 
lean::dec(x_6);
lean::dec(x_4);
x_250 = lean::box(0);
return x_250;
}
else
{
obj* x_251; obj* x_254; 
x_251 = lean::cnstr_get(x_7, 0);
lean::inc(x_251);
lean::dec(x_7);
x_254 = l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(x_4);
if (lean::obj_tag(x_254) == 0)
{
obj* x_257; 
lean::dec(x_6);
lean::dec(x_251);
x_257 = lean::box(0);
return x_257;
}
else
{
obj* x_258; obj* x_260; obj* x_261; obj* x_262; 
x_258 = lean::cnstr_get(x_254, 0);
if (lean::is_exclusive(x_254)) {
 x_260 = x_254;
} else {
 lean::inc(x_258);
 lean::dec(x_254);
 x_260 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_261 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_261 = x_6;
}
lean::cnstr_set(x_261, 0, x_251);
lean::cnstr_set(x_261, 1, x_258);
if (lean::is_scalar(x_260)) {
 x_262 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_262 = x_260;
}
lean::cnstr_set(x_262, 0, x_261);
return x_262;
}
}
}
}
}
}
obj* l_Lean_Elaborator_matchSpec(obj* x_0, obj* x_1) {
_start:
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; 
x_11 = lean::box(0);
x_7 = x_11;
goto lbl_8;
}
else
{
obj* x_16; 
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_4);
x_16 = lean::box(0);
return x_16;
}
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_23; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_4);
lean::dec(x_2);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_17);
x_25 = lean::box(0);
x_7 = x_25;
goto lbl_8;
}
}
lbl_8:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_7);
x_27 = lean::cnstr_get(x_1, 1);
lean::inc(x_27);
lean::dec(x_1);
x_30 = l_List_zip___rarg___closed__1;
x_31 = l_List_zipWith___main___rarg(x_30, x_4, x_27);
x_32 = l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; 
lean::dec(x_6);
lean::dec(x_2);
x_35 = lean::box(0);
return x_35;
}
else
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_38 = x_32;
} else {
 lean::inc(x_36);
 lean::dec(x_32);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_6;
}
lean::cnstr_set(x_39, 0, x_2);
lean::cnstr_set(x_39, 1, x_36);
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
}
}
obj* l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 2);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_Lean_Elaborator_matchSpec(x_9, x_11);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_17; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
}
obj* _init_l_Lean_Elaborator_notation_elaborateAux___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid notation, matches multiple reserved notations");
return x_0;
}
}
obj* l_Lean_Elaborator_notation_elaborateAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_0);
x_7 = l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(x_0, x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
x_17 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 x_19 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_0);
 x_19 = lean::box(0);
}
x_20 = l_Lean_Elaborator_postprocessNotationSpec(x_13);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_11);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set(x_21, 3, x_15);
lean::cnstr_set(x_21, 4, x_17);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_3);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 3);
x_36 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_Lean_Elaborator_postprocessNotationSpec(x_27);
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_32);
lean::cnstr_set(x_40, 2, x_39);
lean::cnstr_set(x_40, 3, x_34);
lean::cnstr_set(x_40, 4, x_36);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_3);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
else
{
obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_7);
lean::dec(x_24);
x_45 = l_Lean_Parser_command_notation_HasView;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
lean::dec(x_45);
x_49 = lean::apply_1(x_46, x_0);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = l_Lean_Elaborator_notation_elaborateAux___closed__1;
x_52 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_50, x_51, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_50);
if (lean::obj_tag(x_52) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
x_55 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_57 = x_52;
} else {
 lean::inc(x_55);
 lean::dec(x_52);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_59 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_61 = x_52;
} else {
 lean::inc(x_59);
 lean::dec(x_52);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 0);
x_64 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 x_66 = x_59;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_59);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_62, 0);
x_69 = lean::cnstr_get(x_62, 1);
x_71 = lean::cnstr_get(x_62, 2);
x_73 = lean::cnstr_get(x_62, 3);
x_75 = lean::cnstr_get(x_62, 4);
if (lean::is_exclusive(x_62)) {
 x_77 = x_62;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_62);
 x_77 = lean::box(0);
}
x_78 = l_Lean_Elaborator_postprocessNotationSpec(x_71);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_67);
lean::cnstr_set(x_79, 1, x_69);
lean::cnstr_set(x_79, 2, x_78);
lean::cnstr_set(x_79, 3, x_73);
lean::cnstr_set(x_79, 4, x_75);
if (lean::is_scalar(x_66)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_66;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_64);
if (lean::is_scalar(x_61)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_61;
}
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
obj* l_Lean_Elaborator_notation_elaborateAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_notation_elaborateAux(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_mkNotationKind___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_notation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_mkNotationKind___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
x_9 = lean::cnstr_get(x_0, 4);
x_11 = lean::cnstr_get(x_0, 5);
x_13 = lean::cnstr_get(x_0, 6);
x_15 = lean::cnstr_get(x_0, 7);
x_17 = lean::cnstr_get(x_0, 8);
x_19 = lean::cnstr_get(x_0, 9);
x_21 = lean::cnstr_get(x_0, 10);
if (lean::is_exclusive(x_0)) {
 x_23 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_0);
 x_23 = lean::box(0);
}
x_24 = lean::mk_nat_obj(1ul);
x_25 = lean::nat_add(x_5, x_24);
if (lean::is_scalar(x_23)) {
 x_26 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_26 = x_23;
}
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_3);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set(x_26, 3, x_7);
lean::cnstr_set(x_26, 4, x_9);
lean::cnstr_set(x_26, 5, x_11);
lean::cnstr_set(x_26, 6, x_13);
lean::cnstr_set(x_26, 7, x_15);
lean::cnstr_set(x_26, 8, x_17);
lean::cnstr_set(x_26, 9, x_19);
lean::cnstr_set(x_26, 10, x_21);
x_27 = l_Lean_Elaborator_mkNotationKind___rarg___closed__1;
x_28 = lean_name_mk_numeral(x_27, x_5);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
obj* l_Lean_Elaborator_mkNotationKind(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_mkNotationKind___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Elaborator_mkNotationKind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_mkNotationKind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_registerNotationMacro(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_mkNotationKind___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
lean::inc(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_0);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer), 3, 1);
lean::closure_set(x_21, 0, x_19);
x_22 = lean::cnstr_get(x_15, 7);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
x_28 = lean::cnstr_get(x_15, 2);
x_30 = lean::cnstr_get(x_15, 3);
x_32 = lean::cnstr_get(x_15, 4);
x_34 = lean::cnstr_get(x_15, 5);
x_36 = lean::cnstr_get(x_15, 6);
x_38 = lean::cnstr_get(x_15, 8);
x_40 = lean::cnstr_get(x_15, 9);
x_42 = lean::cnstr_get(x_15, 10);
if (lean::is_exclusive(x_15)) {
 x_44 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_22);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_15);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_22, 0);
x_47 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_49 = x_22;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_22);
 x_49 = lean::box(0);
}
x_50 = l_RBNode_insert___at_Lean_Expander_builtinTransformers___spec__1(x_47, x_13, x_21);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_50);
if (lean::is_scalar(x_44)) {
 x_52 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_52 = x_44;
}
lean::cnstr_set(x_52, 0, x_24);
lean::cnstr_set(x_52, 1, x_26);
lean::cnstr_set(x_52, 2, x_28);
lean::cnstr_set(x_52, 3, x_30);
lean::cnstr_set(x_52, 4, x_32);
lean::cnstr_set(x_52, 5, x_34);
lean::cnstr_set(x_52, 6, x_36);
lean::cnstr_set(x_52, 7, x_51);
lean::cnstr_set(x_52, 8, x_38);
lean::cnstr_set(x_52, 9, x_40);
lean::cnstr_set(x_52, 10, x_42);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_19);
lean::cnstr_set(x_53, 1, x_52);
if (lean::is_scalar(x_12)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_12;
}
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
obj* l_Lean_Elaborator_registerNotationMacro___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_registerNotationMacro(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(uint8 x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(x_0, x_3);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::obj_tag(x_5) == 0)
{
return x_4;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_5, 0);
switch (lean::obj_tag(x_6)) {
case 2:
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_6, 0);
x_8 = lean::cnstr_get(x_7, 1);
if (lean::obj_tag(x_8) == 0)
{
return x_4;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_8, 0);
x_10 = lean::cnstr_get(x_9, 1);
switch (lean::obj_tag(x_10)) {
case 3:
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
default:
{
return x_4;
}
}
}
}
default:
{
return x_4;
}
}
}
}
}
}
obj* l_Lean_Elaborator_notation_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
x_18 = lean::cnstr_get(x_1, 8);
if (lean::is_exclusive(x_1)) {
 x_20 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_6);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_4);
lean::cnstr_set(x_22, 2, x_21);
lean::cnstr_set(x_22, 3, x_8);
lean::cnstr_set(x_22, 4, x_10);
lean::cnstr_set(x_22, 5, x_12);
lean::cnstr_set(x_22, 6, x_14);
lean::cnstr_set(x_22, 7, x_16);
lean::cnstr_set(x_22, 8, x_18);
return x_22;
}
}
obj* _init_l_Lean_Elaborator_notation_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1ul);
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_notation_elaborate___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ignoring notation using 'fold' action");
return x_0;
}
}
obj* l_Lean_Elaborator_notation_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; uint8 x_14; uint8 x_15; 
x_4 = l_Lean_Parser_command_notation_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_14 = 0;
x_15 = l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(x_14, x_11);
lean::dec(x_11);
if (x_15 == 0)
{
obj* x_18; 
lean::inc(x_2);
x_18 = l_Lean_Elaborator_notation_elaborateAux(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_20 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_22 = x_18;
} else {
 lean::inc(x_20);
 lean::dec(x_18);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_29; obj* x_33; 
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
lean::dec(x_18);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
lean::inc(x_27);
x_33 = l_Lean_Elaborator_registerNotationMacro(x_27, x_1, x_2, x_29);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_2);
lean::dec(x_27);
x_36 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
return x_39;
}
else
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
lean::dec(x_33);
x_43 = lean::cnstr_get(x_27, 0);
lean::inc(x_43);
lean::dec(x_27);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_46 = lean::cnstr_get(x_40, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_46, 0);
x_53 = lean::cnstr_get(x_46, 1);
x_55 = lean::cnstr_get(x_46, 2);
x_57 = lean::cnstr_get(x_46, 3);
x_59 = lean::cnstr_get(x_46, 4);
x_61 = lean::cnstr_get(x_46, 5);
x_63 = lean::cnstr_get(x_46, 6);
x_65 = lean::cnstr_get(x_46, 7);
x_67 = lean::cnstr_get(x_46, 8);
x_69 = lean::cnstr_get(x_46, 9);
x_71 = lean::cnstr_get(x_46, 10);
if (lean::is_exclusive(x_46)) {
 x_73 = x_46;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::inc(x_61);
 lean::inc(x_63);
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_46);
 x_73 = lean::box(0);
}
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_48);
lean::cnstr_set(x_74, 1, x_53);
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_51);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set(x_75, 2, x_55);
lean::cnstr_set(x_75, 3, x_57);
lean::cnstr_set(x_75, 4, x_59);
lean::cnstr_set(x_75, 5, x_61);
lean::cnstr_set(x_75, 6, x_63);
lean::cnstr_set(x_75, 7, x_65);
lean::cnstr_set(x_75, 8, x_67);
lean::cnstr_set(x_75, 9, x_69);
lean::cnstr_set(x_75, 10, x_71);
x_76 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_75);
return x_76;
}
else
{
obj* x_78; obj* x_80; obj* x_83; obj* x_85; 
lean::dec(x_43);
x_78 = lean::cnstr_get(x_40, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_40, 1);
lean::inc(x_80);
lean::dec(x_40);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_notation_elaborate___lambda__1), 2, 1);
lean::closure_set(x_83, 0, x_78);
lean::inc(x_2);
x_85 = l_Lean_Elaborator_modifyCurrentScope(x_83, x_1, x_2, x_80);
if (lean::obj_tag(x_85) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_2);
x_87 = lean::cnstr_get(x_85, 0);
if (lean::is_exclusive(x_85)) {
 x_89 = x_85;
} else {
 lean::inc(x_87);
 lean::dec(x_85);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_97; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
lean::dec(x_85);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_94);
return x_97;
}
}
}
}
}
else
{
obj* x_99; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_128; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_8);
x_99 = lean::cnstr_get(x_2, 0);
lean::inc(x_99);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_3, 0);
x_104 = lean::cnstr_get(x_3, 1);
x_106 = lean::cnstr_get(x_3, 2);
x_108 = lean::cnstr_get(x_3, 3);
x_110 = lean::cnstr_get(x_3, 4);
x_112 = lean::cnstr_get(x_3, 5);
x_114 = lean::cnstr_get(x_3, 6);
x_116 = lean::cnstr_get(x_3, 7);
x_118 = lean::cnstr_get(x_3, 8);
x_120 = lean::cnstr_get(x_3, 9);
x_122 = lean::cnstr_get(x_3, 10);
if (lean::is_exclusive(x_3)) {
 x_124 = x_3;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::inc(x_108);
 lean::inc(x_110);
 lean::inc(x_112);
 lean::inc(x_114);
 lean::inc(x_116);
 lean::inc(x_118);
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_3);
 x_124 = lean::box(0);
}
x_125 = lean::cnstr_get(x_99, 0);
lean::inc(x_125);
lean::dec(x_99);
x_128 = lean::box(0);
x_129 = l_Lean_Elaborator_notation_elaborate___closed__1;
x_130 = 1;
x_131 = l_String_splitAux___main___closed__1;
x_132 = l_Lean_Elaborator_notation_elaborate___closed__2;
x_133 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_133, 0, x_125);
lean::cnstr_set(x_133, 1, x_129);
lean::cnstr_set(x_133, 2, x_128);
lean::cnstr_set(x_133, 3, x_131);
lean::cnstr_set(x_133, 4, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*5, x_130);
x_134 = x_133;
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_112);
if (lean::is_scalar(x_124)) {
 x_136 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_136 = x_124;
}
lean::cnstr_set(x_136, 0, x_102);
lean::cnstr_set(x_136, 1, x_104);
lean::cnstr_set(x_136, 2, x_106);
lean::cnstr_set(x_136, 3, x_108);
lean::cnstr_set(x_136, 4, x_110);
lean::cnstr_set(x_136, 5, x_135);
lean::cnstr_set(x_136, 6, x_114);
lean::cnstr_set(x_136, 7, x_116);
lean::cnstr_set(x_136, 8, x_118);
lean::cnstr_set(x_136, 9, x_120);
lean::cnstr_set(x_136, 10, x_122);
x_137 = lean::box(0);
x_138 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_136);
x_139 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_139, 0, x_138);
return x_139;
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_notation_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_notation_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_universe_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
x_18 = lean::cnstr_get(x_1, 8);
if (lean::is_exclusive(x_1)) {
 x_20 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
lean::inc(x_0);
x_22 = level_mk_param(x_0);
x_23 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
x_24 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_23, x_8, x_0, x_22);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_12);
lean::cnstr_set(x_25, 6, x_14);
lean::cnstr_set(x_25, 7, x_16);
lean::cnstr_set(x_25, 8, x_18);
return x_25;
}
}
obj* _init_l_Lean_Elaborator_universe_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("a universe named '");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_universe_elaborate___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("' has already been declared in this Scope");
return x_0;
}
}
obj* l_Lean_Elaborator_universe_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_13; obj* x_15; 
x_4 = l_Lean_Parser_command_universe_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_13 = l_Lean_Elaborator_mangleIdent(x_10);
lean::inc(x_2);
x_15 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_21 = x_15;
} else {
 lean::inc(x_19);
 lean::dec(x_15);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_34; obj* x_36; 
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
lean::dec(x_15);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_31 = lean::cnstr_get(x_26, 3);
lean::inc(x_31);
lean::dec(x_26);
x_34 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
lean::inc(x_13);
x_36 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_34, x_31, x_13);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_39; 
lean::dec(x_0);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_universe_elaborate___lambda__1), 2, 1);
lean::closure_set(x_38, 0, x_13);
x_39 = l_Lean_Elaborator_modifyCurrentScope(x_38, x_1, x_2, x_28);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_40 = x_36;
} else {
 lean::dec(x_36);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_0);
x_42 = l_Lean_Name_toString___closed__1;
x_43 = l_Lean_Name_toStringWithSep___main(x_42, x_13);
x_44 = l_Lean_Elaborator_universe_elaborate___closed__1;
x_45 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_47 = l_Lean_Elaborator_universe_elaborate___closed__2;
x_48 = lean::string_append(x_45, x_47);
x_49 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_41, x_48, x_1, x_2, x_28);
lean::dec(x_28);
lean::dec(x_41);
return x_49;
}
}
}
}
obj* l_Lean_Elaborator_universe_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_universe_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown identifier '");
return x_0;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'attribute' command, identifier is ambiguous");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
x_12 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_14 = x_0;
} else {
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
lean::inc(x_8);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_8);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_18);
x_23 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = l_Char_HasRepr___closed__1;
x_27 = lean::string_append(x_24, x_26);
lean::inc(x_2);
x_29 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_17, x_27, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_17);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_12);
lean::dec(x_14);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_44; obj* x_47; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_47 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_12, x_1, x_2, x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_14);
lean::dec(x_42);
x_50 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_54 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_56 = x_47;
} else {
 lean::inc(x_54);
 lean::dec(x_47);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 0);
x_59 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_61 = x_54;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_54);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_14;
}
lean::cnstr_set(x_62, 0, x_42);
lean::cnstr_set(x_62, 1, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
if (lean::is_scalar(x_56)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_56;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_10, 1);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_8);
x_68 = lean::cnstr_get(x_0, 1);
lean::inc(x_68);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_release(x_10, 1);
 x_73 = x_10;
} else {
 lean::inc(x_71);
 lean::dec(x_10);
 x_73 = lean::box(0);
}
x_74 = lean::box(0);
x_75 = lean_expr_mk_const(x_71, x_74);
x_76 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_68, x_1, x_2, x_3);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_73);
lean::dec(x_75);
x_79 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_81 = x_76;
} else {
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_85 = x_76;
} else {
 lean::inc(x_83);
 lean::dec(x_76);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_83, 0);
x_88 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_90 = x_83;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_83);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_91 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_91 = x_73;
}
lean::cnstr_set(x_91, 0, x_75);
lean::cnstr_set(x_91, 1, x_86);
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_88);
if (lean::is_scalar(x_85)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_85;
}
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
}
else
{
obj* x_95; obj* x_96; obj* x_99; obj* x_100; obj* x_101; obj* x_103; 
lean::dec(x_10);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_95 = x_65;
} else {
 lean::dec(x_65);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_0, 1);
lean::inc(x_96);
lean::dec(x_0);
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_8);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
x_101 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2;
lean::inc(x_2);
x_103 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_100, x_101, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_100);
if (lean::obj_tag(x_103) == 0)
{
obj* x_109; obj* x_111; obj* x_112; 
lean::dec(x_2);
lean::dec(x_95);
lean::dec(x_96);
x_109 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 x_111 = x_103;
} else {
 lean::inc(x_109);
 lean::dec(x_103);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
return x_112;
}
else
{
obj* x_113; obj* x_116; obj* x_118; obj* x_121; 
x_113 = lean::cnstr_get(x_103, 0);
lean::inc(x_113);
lean::dec(x_103);
x_116 = lean::cnstr_get(x_113, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_113, 1);
lean::inc(x_118);
lean::dec(x_113);
x_121 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_96, x_1, x_2, x_118);
if (lean::obj_tag(x_121) == 0)
{
obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_95);
lean::dec(x_116);
x_124 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_126 = x_121;
} else {
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
return x_127;
}
else
{
obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_128 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_130 = x_121;
} else {
 lean::inc(x_128);
 lean::dec(x_121);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_128, 0);
x_133 = lean::cnstr_get(x_128, 1);
if (lean::is_exclusive(x_128)) {
 x_135 = x_128;
} else {
 lean::inc(x_131);
 lean::inc(x_133);
 lean::dec(x_128);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_136 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_136 = x_95;
}
lean::cnstr_set(x_136, 0, x_116);
lean::cnstr_set(x_136, 1, x_131);
if (lean::is_scalar(x_135)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_135;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_133);
if (lean::is_scalar(x_130)) {
 x_138 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_138 = x_130;
}
lean::cnstr_set(x_138, 0, x_137);
return x_138;
}
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_attribute_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("attribute");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_attribute_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("local");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_attribute_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = l_Lean_Parser_command_attribute_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 3);
lean::inc(x_12);
lean::inc(x_2);
x_15 = l_Lean_Elaborator_attrsToPexpr(x_12, x_1, x_2, x_3);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_18; 
x_18 = 0;
x_16 = x_18;
goto lbl_17;
}
else
{
uint8 x_20; 
lean::dec(x_10);
x_20 = 1;
x_16 = x_20;
goto lbl_17;
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_26 = x_15;
} else {
 lean::inc(x_24);
 lean::dec(x_15);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_43; 
x_28 = lean::cnstr_get(x_15, 0);
lean::inc(x_28);
lean::dec(x_15);
x_31 = l_Lean_Elaborator_attribute_elaborate___closed__1;
x_32 = l_Lean_Elaborator_attribute_elaborate___closed__2;
x_33 = l_Lean_KVMap_setBool(x_31, x_32, x_16);
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_28, 1);
lean::inc(x_36);
lean::dec(x_28);
x_39 = lean::cnstr_get(x_9, 5);
lean::inc(x_39);
lean::dec(x_9);
lean::inc(x_2);
x_43 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_39, x_1, x_2, x_36);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_33);
lean::dec(x_34);
x_48 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
return x_51;
}
else
{
obj* x_52; obj* x_55; obj* x_57; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_52 = lean::cnstr_get(x_43, 0);
lean::inc(x_52);
lean::dec(x_43);
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
lean::dec(x_52);
x_60 = l_Lean_Elaborator_mkEqns___closed__1;
x_61 = l_Lean_Expr_mkCapp(x_60, x_55);
x_62 = lean_expr_mk_app(x_34, x_61);
x_63 = lean_expr_mk_mdata(x_33, x_62);
x_64 = l_Lean_Elaborator_oldElabCommand(x_0, x_63, x_1, x_2, x_57);
lean::dec(x_0);
return x_64;
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_attribute_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_attribute_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_check_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("#check");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
return x_6;
}
}
obj* l_Lean_Elaborator_check_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_14; 
x_4 = l_Lean_Parser_command_check_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
lean::inc(x_2);
x_14 = l_Lean_Elaborator_toPexpr___main(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_Lean_Elaborator_check_elaborate___closed__1;
x_30 = lean_expr_mk_mdata(x_29, x_24);
x_31 = l_Lean_Elaborator_oldElabCommand(x_0, x_30, x_1, x_2, x_26);
lean::dec(x_0);
return x_31;
}
}
}
obj* l_Lean_Elaborator_check_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_check_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_open_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
x_18 = lean::cnstr_get(x_1, 8);
if (lean::is_exclusive(x_1)) {
 x_20 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = l_List_append___rarg(x_16, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_12);
lean::cnstr_set(x_25, 6, x_14);
lean::cnstr_set(x_25, 7, x_24);
lean::cnstr_set(x_25, 8, x_18);
return x_25;
}
}
obj* l_Lean_Elaborator_open_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_4 = l_Lean_Parser_command_open_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_open_elaborate___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = l_Lean_Elaborator_modifyCurrentScope(x_9, x_1, x_2, x_3);
return x_10;
}
}
obj* l_Lean_Elaborator_open_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_open_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_4);
x_11 = l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_Lean_Elaborator_export_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_4 = l_Lean_Parser_command_export_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = l_Lean_Elaborator_getNamespace(x_1, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_13 = x_9;
} else {
 lean::inc(x_11);
 lean::dec(x_9);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_15 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 1);
x_20 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_22 = x_15;
} else {
 lean::inc(x_20);
 lean::inc(x_18);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_18, 0);
x_25 = lean::cnstr_get(x_18, 1);
x_27 = lean::cnstr_get(x_18, 2);
x_29 = lean::cnstr_get(x_18, 3);
x_31 = lean::cnstr_get(x_18, 4);
x_33 = lean::cnstr_get(x_18, 5);
x_35 = lean::cnstr_get(x_18, 6);
x_37 = lean::cnstr_get(x_18, 7);
x_39 = lean::cnstr_get(x_18, 8);
x_41 = lean::cnstr_get(x_18, 9);
x_43 = lean::cnstr_get(x_18, 10);
if (lean::is_exclusive(x_18)) {
 x_45 = x_18;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_18);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_8, 1);
lean::inc(x_46);
lean::dec(x_8);
x_49 = l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(x_20, x_46);
x_50 = l_List_append___rarg(x_29, x_49);
if (lean::is_scalar(x_45)) {
 x_51 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_51 = x_45;
}
lean::cnstr_set(x_51, 0, x_23);
lean::cnstr_set(x_51, 1, x_25);
lean::cnstr_set(x_51, 2, x_27);
lean::cnstr_set(x_51, 3, x_50);
lean::cnstr_set(x_51, 4, x_31);
lean::cnstr_set(x_51, 5, x_33);
lean::cnstr_set(x_51, 6, x_35);
lean::cnstr_set(x_51, 7, x_37);
lean::cnstr_set(x_51, 8, x_39);
lean::cnstr_set(x_51, 9, x_41);
lean::cnstr_set(x_51, 10, x_43);
x_52 = lean::box(0);
if (lean::is_scalar(x_22)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_22;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
if (lean::is_scalar(x_17)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_17;
}
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
obj* l_Lean_Elaborator_export_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_export_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_initQuot_elaborate___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("command");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("initQuot");
x_4 = lean_name_mk_string(x_0, x_3);
x_5 = lean::box(0);
x_6 = l_Lean_KVMap_setName(x_5, x_2, x_4);
x_7 = l_Lean_Elaborator_dummy;
x_8 = lean_expr_mk_mdata(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Elaborator_initQuot_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Elaborator_initQuot_elaborate___closed__1;
x_5 = l_Lean_Elaborator_oldElabCommand(x_0, x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Elaborator_initQuot_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_initQuot_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_setOption_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
x_10 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_1, 5);
x_14 = lean::cnstr_get(x_1, 6);
x_16 = lean::cnstr_get(x_1, 7);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 8);
 x_18 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_2);
lean::cnstr_set(x_19, 1, x_4);
lean::cnstr_set(x_19, 2, x_6);
lean::cnstr_set(x_19, 3, x_8);
lean::cnstr_set(x_19, 4, x_10);
lean::cnstr_set(x_19, 5, x_12);
lean::cnstr_set(x_19, 6, x_14);
lean::cnstr_set(x_19, 7, x_16);
lean::cnstr_set(x_19, 8, x_0);
return x_19;
}
}
obj* l_Lean_Elaborator_setOption_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_15; 
x_4 = l_Lean_Parser_command_setOption_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 2);
lean::inc(x_11);
lean::dec(x_9);
lean::inc(x_2);
x_15 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_21 = x_15;
} else {
 lean::inc(x_19);
 lean::dec(x_15);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
lean::dec(x_15);
x_26 = lean::cnstr_get(x_8, 2);
lean::inc(x_26);
lean::dec(x_8);
switch (lean::obj_tag(x_26)) {
case 0:
{
obj* x_29; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_35; obj* x_38; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_29);
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_23, 1);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_33, 8);
lean::inc(x_38);
lean::dec(x_33);
x_41 = 1;
x_42 = l_Lean_KVMap_setBool(x_38, x_11, x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_43, 0, x_42);
x_44 = l_Lean_Elaborator_modifyCurrentScope(x_43, x_1, x_2, x_35);
return x_44;
}
else
{
obj* x_46; obj* x_48; obj* x_51; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_29);
x_46 = lean::cnstr_get(x_23, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_23, 1);
lean::inc(x_48);
lean::dec(x_23);
x_51 = lean::cnstr_get(x_46, 8);
lean::inc(x_51);
lean::dec(x_46);
x_54 = 0;
x_55 = l_Lean_KVMap_setBool(x_51, x_11, x_54);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_56, 0, x_55);
x_57 = l_Lean_Elaborator_modifyCurrentScope(x_56, x_1, x_2, x_48);
return x_57;
}
}
case 1:
{
obj* x_58; obj* x_60; obj* x_63; obj* x_66; obj* x_69; 
x_58 = lean::cnstr_get(x_23, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_23, 1);
lean::inc(x_60);
lean::dec(x_23);
x_63 = lean::cnstr_get(x_58, 8);
lean::inc(x_63);
lean::dec(x_58);
x_66 = lean::cnstr_get(x_26, 0);
lean::inc(x_66);
lean::dec(x_26);
x_69 = l_Lean_Parser_stringLit_View_value(x_66);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_11);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_71, 0, x_63);
x_72 = l_Lean_Elaborator_modifyCurrentScope(x_71, x_1, x_2, x_60);
return x_72;
}
else
{
obj* x_73; obj* x_76; obj* x_77; obj* x_78; 
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
lean::dec(x_69);
x_76 = l_Lean_KVMap_setString(x_63, x_11, x_73);
x_77 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_77, 0, x_76);
x_78 = l_Lean_Elaborator_modifyCurrentScope(x_77, x_1, x_2, x_60);
return x_78;
}
}
default:
{
obj* x_79; obj* x_81; obj* x_84; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_79 = lean::cnstr_get(x_23, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_23, 1);
lean::inc(x_81);
lean::dec(x_23);
x_84 = lean::cnstr_get(x_79, 8);
lean::inc(x_84);
lean::dec(x_79);
x_87 = lean::cnstr_get(x_26, 0);
lean::inc(x_87);
lean::dec(x_26);
x_90 = l_Lean_Parser_number_View_toNat___main(x_87);
x_91 = l_Lean_KVMap_setNat(x_84, x_11, x_90);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_92, 0, x_91);
x_93 = l_Lean_Elaborator_modifyCurrentScope(x_92, x_1, x_2, x_81);
return x_93;
}
}
}
}
}
obj* l_Lean_Elaborator_setOption_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_setOption_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mfor___main___at_Lean_Elaborator_noKind_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_16; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_16 = lean::apply_3(x_1, x_9, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_22 = x_16;
} else {
 lean::inc(x_20);
 lean::dec(x_16);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_0 = x_11;
x_3 = x_27;
goto _start;
}
}
}
}
obj* _init_l_Lean_Elaborator_noKind_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("noKind.elaborate: unreachable");
return x_0;
}
}
obj* l_Lean_Elaborator_noKind_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_0);
x_5 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = l_Lean_Elaborator_noKind_elaborate___closed__1;
x_8 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_6, x_7, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_List_mfor___main___at_Lean_Elaborator_noKind_elaborate___spec__1(x_16, x_1, x_2, x_3);
return x_19;
}
}
}
obj* _init_l_Lean_Elaborator_end_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'end', there is no open Scope to end");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_end_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = lean::box(0);
x_3 = l_Lean_Name_toStringWithSep___main(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_Substring_ofString(x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = l_Lean_Elaborator_mangleIdent(x_7);
return x_8;
}
}
obj* _init_l_Lean_Elaborator_end_elaborate___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_end_elaborate___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", expected Name '");
return x_0;
}
}
obj* l_Lean_Elaborator_end_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = l_Lean_Elaborator_end_elaborate___closed__1;
x_8 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_6, x_7, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_4);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_0);
x_15 = l_Lean_Elaborator_end_elaborate___closed__1;
x_16 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_14, x_15, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_14);
return x_16;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_47; obj* x_48; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_3, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_3, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_3, 5);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 6);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_3, 7);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_3, 8);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_3, 9);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_3, 10);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
lean::dec(x_4);
x_42 = l_Lean_Parser_command_end_HasView;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
lean::dec(x_42);
lean::inc(x_0);
x_47 = lean::apply_1(x_43, x_0);
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_51; obj* x_53; uint8 x_54; 
x_51 = lean::cnstr_get(x_39, 1);
lean::inc(x_51);
x_53 = l_Lean_Elaborator_end_elaborate___closed__2;
x_54 = lean_name_dec_eq(x_53, x_51);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_73; 
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_0);
x_56 = lean::cnstr_get(x_39, 0);
lean::inc(x_56);
lean::dec(x_39);
x_59 = l_Lean_Elaborator_end_elaborate___closed__3;
x_60 = lean::string_append(x_59, x_56);
lean::dec(x_56);
x_62 = l_Lean_Elaborator_end_elaborate___closed__4;
x_63 = lean::string_append(x_60, x_62);
x_64 = l_Lean_Name_toString___closed__1;
x_65 = l_Lean_Name_toStringWithSep___main(x_64, x_51);
x_66 = lean::string_append(x_63, x_65);
lean::dec(x_65);
x_68 = l_Char_HasRepr___closed__1;
x_69 = lean::string_append(x_66, x_68);
lean::inc(x_2);
x_71 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_55, x_69, x_1, x_2, x_3);
lean::dec(x_55);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 lean::cnstr_release(x_3, 4);
 lean::cnstr_release(x_3, 5);
 lean::cnstr_release(x_3, 6);
 lean::cnstr_release(x_3, 7);
 lean::cnstr_release(x_3, 8);
 lean::cnstr_release(x_3, 9);
 lean::cnstr_release(x_3, 10);
 x_73 = x_3;
} else {
 lean::dec(x_3);
 x_73 = lean::box(0);
}
if (lean::obj_tag(x_71) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_73);
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_35);
lean::dec(x_37);
x_87 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_89 = x_71;
} else {
 lean::inc(x_87);
 lean::dec(x_71);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_92; obj* x_93; 
lean::dec(x_71);
if (lean::is_scalar(x_73)) {
 x_92 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_92 = x_73;
}
lean::cnstr_set(x_92, 0, x_19);
lean::cnstr_set(x_92, 1, x_21);
lean::cnstr_set(x_92, 2, x_23);
lean::cnstr_set(x_92, 3, x_25);
lean::cnstr_set(x_92, 4, x_11);
lean::cnstr_set(x_92, 5, x_27);
lean::cnstr_set(x_92, 6, x_29);
lean::cnstr_set(x_92, 7, x_31);
lean::cnstr_set(x_92, 8, x_33);
lean::cnstr_set(x_92, 9, x_35);
lean::cnstr_set(x_92, 10, x_37);
x_93 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_92);
return x_93;
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_0);
lean::dec(x_51);
lean::dec(x_39);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 lean::cnstr_release(x_3, 4);
 lean::cnstr_release(x_3, 5);
 lean::cnstr_release(x_3, 6);
 lean::cnstr_release(x_3, 7);
 lean::cnstr_release(x_3, 8);
 lean::cnstr_release(x_3, 9);
 lean::cnstr_release(x_3, 10);
 x_97 = x_3;
} else {
 lean::dec(x_3);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_19);
lean::cnstr_set(x_98, 1, x_21);
lean::cnstr_set(x_98, 2, x_23);
lean::cnstr_set(x_98, 3, x_25);
lean::cnstr_set(x_98, 4, x_11);
lean::cnstr_set(x_98, 5, x_27);
lean::cnstr_set(x_98, 6, x_29);
lean::cnstr_set(x_98, 7, x_31);
lean::cnstr_set(x_98, 8, x_33);
lean::cnstr_set(x_98, 9, x_35);
lean::cnstr_set(x_98, 10, x_37);
x_99 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_98);
return x_99;
}
}
else
{
obj* x_100; obj* x_102; obj* x_104; obj* x_105; uint8 x_106; 
x_100 = lean::cnstr_get(x_39, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 x_104 = x_48;
} else {
 lean::inc(x_102);
 lean::dec(x_48);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Elaborator_mangleIdent(x_102);
x_106 = lean_name_dec_eq(x_105, x_100);
lean::dec(x_105);
if (x_106 == 0)
{
obj* x_108; obj* x_109; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_126; 
if (lean::is_scalar(x_104)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_104;
}
lean::cnstr_set(x_108, 0, x_0);
x_109 = lean::cnstr_get(x_39, 0);
lean::inc(x_109);
lean::dec(x_39);
x_112 = l_Lean_Elaborator_end_elaborate___closed__3;
x_113 = lean::string_append(x_112, x_109);
lean::dec(x_109);
x_115 = l_Lean_Elaborator_end_elaborate___closed__4;
x_116 = lean::string_append(x_113, x_115);
x_117 = l_Lean_Name_toString___closed__1;
x_118 = l_Lean_Name_toStringWithSep___main(x_117, x_100);
x_119 = lean::string_append(x_116, x_118);
lean::dec(x_118);
x_121 = l_Char_HasRepr___closed__1;
x_122 = lean::string_append(x_119, x_121);
lean::inc(x_2);
x_124 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_108, x_122, x_1, x_2, x_3);
lean::dec(x_108);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 lean::cnstr_release(x_3, 4);
 lean::cnstr_release(x_3, 5);
 lean::cnstr_release(x_3, 6);
 lean::cnstr_release(x_3, 7);
 lean::cnstr_release(x_3, 8);
 lean::cnstr_release(x_3, 9);
 lean::cnstr_release(x_3, 10);
 x_126 = x_3;
} else {
 lean::dec(x_3);
 x_126 = lean::box(0);
}
if (lean::obj_tag(x_124) == 0)
{
obj* x_140; obj* x_142; obj* x_143; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_126);
x_140 = lean::cnstr_get(x_124, 0);
if (lean::is_exclusive(x_124)) {
 x_142 = x_124;
} else {
 lean::inc(x_140);
 lean::dec(x_124);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_140);
return x_143;
}
else
{
obj* x_145; obj* x_146; 
lean::dec(x_124);
if (lean::is_scalar(x_126)) {
 x_145 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_145 = x_126;
}
lean::cnstr_set(x_145, 0, x_19);
lean::cnstr_set(x_145, 1, x_21);
lean::cnstr_set(x_145, 2, x_23);
lean::cnstr_set(x_145, 3, x_25);
lean::cnstr_set(x_145, 4, x_11);
lean::cnstr_set(x_145, 5, x_27);
lean::cnstr_set(x_145, 6, x_29);
lean::cnstr_set(x_145, 7, x_31);
lean::cnstr_set(x_145, 8, x_33);
lean::cnstr_set(x_145, 9, x_35);
lean::cnstr_set(x_145, 10, x_37);
x_146 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_145);
return x_146;
}
}
else
{
obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_0);
lean::dec(x_104);
lean::dec(x_100);
lean::dec(x_39);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 lean::cnstr_release(x_3, 4);
 lean::cnstr_release(x_3, 5);
 lean::cnstr_release(x_3, 6);
 lean::cnstr_release(x_3, 7);
 lean::cnstr_release(x_3, 8);
 lean::cnstr_release(x_3, 9);
 lean::cnstr_release(x_3, 10);
 x_151 = x_3;
} else {
 lean::dec(x_3);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_19);
lean::cnstr_set(x_152, 1, x_21);
lean::cnstr_set(x_152, 2, x_23);
lean::cnstr_set(x_152, 3, x_25);
lean::cnstr_set(x_152, 4, x_11);
lean::cnstr_set(x_152, 5, x_27);
lean::cnstr_set(x_152, 6, x_29);
lean::cnstr_set(x_152, 7, x_31);
lean::cnstr_set(x_152, 8, x_33);
lean::cnstr_set(x_152, 9, x_35);
lean::cnstr_set(x_152, 10, x_37);
x_153 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_152);
return x_153;
}
}
}
}
}
}
obj* l_Lean_Elaborator_end_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_end_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_section_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("section");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_section_elaborate___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".");
x_2 = lean::box(0);
x_3 = l_Lean_Name_toStringWithSep___main(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_Substring_ofString(x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
return x_7;
}
}
obj* l_Lean_Elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_4 = l_Lean_Parser_command_section_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_15; 
x_15 = l_Lean_Elaborator_section_elaborate___closed__2;
x_13 = x_15;
goto lbl_14;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_9, 0);
lean::inc(x_16);
lean::dec(x_9);
x_13 = x_16;
goto lbl_14;
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_13);
x_20 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_22 = x_12;
} else {
 lean::inc(x_20);
 lean::dec(x_12);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_24 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_26 = x_12;
} else {
 lean::inc(x_24);
 lean::dec(x_12);
 x_26 = lean::box(0);
}
x_27 = l_Lean_Elaborator_mangleIdent(x_13);
x_28 = lean::cnstr_get(x_24, 1);
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::inc(x_28);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_28, 0);
x_35 = lean::cnstr_get(x_28, 1);
x_37 = lean::cnstr_get(x_28, 2);
x_39 = lean::cnstr_get(x_28, 3);
x_41 = lean::cnstr_get(x_28, 4);
x_43 = lean::cnstr_get(x_28, 5);
x_45 = lean::cnstr_get(x_28, 6);
x_47 = lean::cnstr_get(x_28, 7);
x_49 = lean::cnstr_get(x_28, 8);
x_51 = lean::cnstr_get(x_28, 9);
x_53 = lean::cnstr_get(x_28, 10);
if (lean::is_exclusive(x_28)) {
 x_55 = x_28;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::inc(x_49);
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_28);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_30, 2);
x_58 = lean::cnstr_get(x_30, 3);
x_60 = lean::cnstr_get(x_30, 4);
x_62 = lean::cnstr_get(x_30, 5);
x_64 = lean::cnstr_get(x_30, 6);
x_66 = lean::cnstr_get(x_30, 7);
x_68 = lean::cnstr_get(x_30, 8);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_70 = x_30;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_30);
 x_70 = lean::box(0);
}
x_71 = l_Lean_Elaborator_section_elaborate___closed__1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_27);
lean::cnstr_set(x_72, 2, x_56);
lean::cnstr_set(x_72, 3, x_58);
lean::cnstr_set(x_72, 4, x_60);
lean::cnstr_set(x_72, 5, x_62);
lean::cnstr_set(x_72, 6, x_64);
lean::cnstr_set(x_72, 7, x_66);
lean::cnstr_set(x_72, 8, x_68);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_41);
if (lean::is_scalar(x_55)) {
 x_74 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_74 = x_55;
}
lean::cnstr_set(x_74, 0, x_33);
lean::cnstr_set(x_74, 1, x_35);
lean::cnstr_set(x_74, 2, x_37);
lean::cnstr_set(x_74, 3, x_39);
lean::cnstr_set(x_74, 4, x_73);
lean::cnstr_set(x_74, 5, x_43);
lean::cnstr_set(x_74, 6, x_45);
lean::cnstr_set(x_74, 7, x_47);
lean::cnstr_set(x_74, 8, x_49);
lean::cnstr_set(x_74, 9, x_51);
lean::cnstr_set(x_74, 10, x_53);
x_75 = lean::box(0);
if (lean::is_scalar(x_32)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_32;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_74);
if (lean::is_scalar(x_26)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_26;
}
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
}
}
obj* l_Lean_Elaborator_section_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_section_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_namespace_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("namespace");
return x_0;
}
}
obj* l_Lean_Elaborator_namespace_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_14; 
x_4 = l_Lean_Parser_command_namespace_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = l_Lean_Elaborator_mangleIdent(x_9);
lean::inc(x_2);
x_14 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_12);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_19 = x_14;
} else {
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_29; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_Lean_Elaborator_getNamespace(x_1, x_2, x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_12);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_36 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_38 = x_29;
} else {
 lean::inc(x_36);
 lean::dec(x_29);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_24, 2);
x_46 = lean::cnstr_get(x_24, 3);
x_48 = lean::cnstr_get(x_24, 4);
x_50 = lean::cnstr_get(x_24, 5);
x_52 = lean::cnstr_get(x_24, 6);
x_54 = lean::cnstr_get(x_24, 7);
x_56 = lean::cnstr_get(x_24, 8);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_58 = x_24;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::inc(x_48);
 lean::inc(x_50);
 lean::inc(x_52);
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_24);
 x_58 = lean::box(0);
}
lean::inc(x_12);
x_60 = l_Lean_Name_append___main(x_39, x_12);
lean::dec(x_39);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_52);
x_63 = l_Lean_Elaborator_namespace_elaborate___closed__1;
if (lean::is_scalar(x_58)) {
 x_64 = lean::alloc_cnstr(0, 9, 0);
} else {
 x_64 = x_58;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_12);
lean::cnstr_set(x_64, 2, x_44);
lean::cnstr_set(x_64, 3, x_46);
lean::cnstr_set(x_64, 4, x_48);
lean::cnstr_set(x_64, 5, x_50);
lean::cnstr_set(x_64, 6, x_62);
lean::cnstr_set(x_64, 7, x_54);
lean::cnstr_set(x_64, 8, x_56);
x_65 = lean::cnstr_get(x_41, 0);
x_67 = lean::cnstr_get(x_41, 1);
x_69 = lean::cnstr_get(x_41, 2);
x_71 = lean::cnstr_get(x_41, 3);
x_73 = lean::cnstr_get(x_41, 4);
x_75 = lean::cnstr_get(x_41, 5);
x_77 = lean::cnstr_get(x_41, 6);
x_79 = lean::cnstr_get(x_41, 7);
x_81 = lean::cnstr_get(x_41, 8);
x_83 = lean::cnstr_get(x_41, 9);
x_85 = lean::cnstr_get(x_41, 10);
if (lean::is_exclusive(x_41)) {
 x_87 = x_41;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_41);
 x_87 = lean::box(0);
}
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_64);
lean::cnstr_set(x_88, 1, x_73);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_65);
lean::cnstr_set(x_89, 1, x_67);
lean::cnstr_set(x_89, 2, x_69);
lean::cnstr_set(x_89, 3, x_71);
lean::cnstr_set(x_89, 4, x_88);
lean::cnstr_set(x_89, 5, x_75);
lean::cnstr_set(x_89, 6, x_77);
lean::cnstr_set(x_89, 7, x_79);
lean::cnstr_set(x_89, 8, x_81);
lean::cnstr_set(x_89, 9, x_83);
lean::cnstr_set(x_89, 10, x_85);
x_90 = lean::box(0);
if (lean::is_scalar(x_43)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_43;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
if (lean::is_scalar(x_38)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_38;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
}
}
obj* l_Lean_Elaborator_namespace_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_namespace_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_eoi_elaborate___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid end of input, expected 'end'");
return x_0;
}
}
obj* l_Lean_Elaborator_eoi_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; uint8 x_10; 
x_4 = lean::cnstr_get(x_3, 4);
lean::inc(x_4);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_List_lengthAux___main___rarg(x_4, x_6);
lean::dec(x_4);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_dec_lt(x_9, x_7);
lean::dec(x_7);
if (x_10 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_3);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_0);
x_18 = l_Lean_Elaborator_eoi_elaborate___closed__1;
x_19 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_17, x_18, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_17);
return x_19;
}
}
}
obj* l_Lean_Elaborator_eoi_elaborate___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_eoi_elaborate(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
x_22 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_13, x_1, x_2);
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
x_25 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_7, x_1, x_2);
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
x_44 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_34, x_1, x_2);
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
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
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
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
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
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__2(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__1(x_0, x_7, x_9);
x_0 = x_12;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_Elaborator_elaborators() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_0 = l_Lean_Parser_Module_header;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Module_header_elaborate___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_Lean_Parser_command_notation;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_notation_elaborate___boxed), 4, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_command_reserveNotation;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_reserveNotation_elaborate___boxed), 4, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_command_universe;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_universe_elaborate___boxed), 4, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_noKind;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_noKind_elaborate), 4, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_command_end;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_end_elaborate___boxed), 4, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_command_section;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_section_elaborate___boxed), 4, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_command_namespace;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_namespace_elaborate___boxed), 4, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_command_variables;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_variables_elaborate___boxed), 4, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_include;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_include_elaborate___boxed), 4, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_command_declaration;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declaration_elaborate), 4, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_Lean_Parser_command_attribute;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_attribute_elaborate___boxed), 4, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_open;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_open_elaborate___boxed), 4, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_command_export;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_export_elaborate___boxed), 4, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_Parser_command_check;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_check_elaborate___boxed), 4, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_initQuot;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_initQuot_elaborate___boxed), 4, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_command_setOption;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___boxed), 4, 0);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_Lean_Parser_Module_eoi;
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_eoi_elaborate___boxed), 4, 0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_47);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_44);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_41);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_38);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_35);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_32);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_29);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_26);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_23);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_20);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_17);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_14);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_11);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_8);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_5);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_2);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::box(0);
x_74 = l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__3(x_73, x_72);
return x_74;
}
}
uint8 l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean_name_dec_eq(x_0, x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(x_0, x_4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
uint8 l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(x_0, x_1, x_4);
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_6, 2);
x_8 = lean_name_dec_eq(x_7, x_0);
if (x_8 == 0)
{
return x_5;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
}
uint8 l_Lean_Elaborator_isOpenNamespace___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::box(0);
x_3 = lean_name_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_0, 6);
x_5 = l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 7);
x_7 = 0;
x_8 = l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(x_1, x_7, x_6);
if (x_8 == 0)
{
return x_7;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
}
obj* l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(x_0, x_3, x_2);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Elaborator_isOpenNamespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_isOpenNamespace___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Elaborator_isOpenNamespace(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Elaborator_isOpenNamespace___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_isOpenNamespace___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_isOpenNamespace(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(x_0, x_1, x_4);
x_6 = lean::cnstr_get(x_3, 2);
x_7 = lean_name_dec_eq(x_0, x_6);
if (x_7 == 0)
{
return x_5;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_Lean_Elaborator_matchOpenSpec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_10; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 2);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_Lean_Name_append___main(x_7, x_0);
lean::dec(x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; uint8 x_21; 
x_13 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 2);
lean::inc(x_18);
lean::dec(x_16);
x_21 = lean_name_dec_eq(x_0, x_18);
lean::dec(x_18);
if (x_21 == 0)
{
obj* x_23; uint8 x_26; uint8 x_27; 
x_23 = lean::cnstr_get(x_13, 2);
lean::inc(x_23);
lean::dec(x_13);
x_26 = 0;
x_27 = l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(x_0, x_26, x_23);
lean::dec(x_23);
if (x_27 == 0)
{
obj* x_32; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_15);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_39; obj* x_41; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_33, 2);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_Lean_Name_append___main(x_36, x_0);
lean::dec(x_36);
if (lean::is_scalar(x_15)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_15;
}
lean::cnstr_set(x_41, 0, x_39);
return x_41;
}
}
else
{
obj* x_43; obj* x_46; obj* x_49; obj* x_51; 
lean::dec(x_13);
x_43 = lean::cnstr_get(x_1, 0);
lean::inc(x_43);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_43, 2);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_Lean_Name_append___main(x_46, x_0);
lean::dec(x_46);
if (lean::is_scalar(x_15)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_15;
}
lean::cnstr_set(x_51, 0, x_49);
return x_51;
}
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(x_0, x_3, x_2);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_List_reverse___rarg(x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_1, 8);
lean::inc(x_12);
lean::inc(x_0);
x_15 = l_Lean_Name_append___main(x_7, x_0);
x_16 = l_Lean_Environment_contains(x_12, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_7);
lean::dec(x_11);
x_2 = x_9;
goto _start;
}
else
{
obj* x_21; 
if (lean::is_scalar(x_11)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_11;
}
lean::cnstr_set(x_21, 0, x_7);
lean::cnstr_set(x_21, 1, x_3);
x_2 = x_9;
x_3 = x_21;
goto _start;
}
}
}
}
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = l_Lean_Elaborator_matchOpenSpec(x_0, x_4);
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_List_reverse___rarg(x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_9 = x_1;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
lean::inc(x_0);
x_11 = l_Lean_Environment_contains(x_0, x_5);
if (x_11 == 0)
{
lean::dec(x_5);
lean::dec(x_9);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_2);
x_1 = x_7;
x_2 = x_15;
goto _start;
}
}
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = l_Lean_Elaborator_isOpenNamespace___main(x_0, x_9);
lean::dec(x_9);
if (x_11 == 0)
{
lean::dec(x_4);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_16; 
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_2);
x_1 = x_6;
x_2 = x_16;
goto _start;
}
}
}
}
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
lean::inc(x_0);
x_13 = l_Lean_Elaborator_matchOpenSpec(x_0, x_9);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_16; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_List_reverse___rarg(x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_11; 
x_5 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_9 = x_1;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
lean::inc(x_0);
x_11 = l_Lean_Environment_contains(x_0, x_5);
if (x_11 == 0)
{
lean::dec(x_5);
lean::dec(x_9);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_2);
x_1 = x_7;
x_2 = x_15;
goto _start;
}
}
}
}
obj* _init_l_Lean_Elaborator_resolveContext___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_root_");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_resolveContext___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_3);
x_5 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; 
x_12 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_19 = x_12;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_15, 4);
lean::inc(x_20);
x_22 = l_Lean_SMap_insert___main___at_Lean_Environment_add___spec__1___closed__1;
lean::inc(x_0);
x_24 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_22, x_20, x_0);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_30; 
x_25 = lean::cnstr_get(x_15, 6);
lean::inc(x_25);
x_27 = lean::box(0);
lean::inc(x_3);
lean::inc(x_0);
x_30 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(x_0, x_3, x_25, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_34; obj* x_35; uint8 x_38; obj* x_39; obj* x_42; obj* x_44; obj* x_45; obj* x_48; obj* x_50; obj* x_51; 
x_31 = l_Lean_Elaborator_resolveContext___main___closed__1;
x_32 = lean::box(0);
lean::inc(x_0);
x_34 = l_Lean_Name_replacePrefix___main(x_0, x_31, x_32);
x_35 = lean::cnstr_get(x_3, 8);
lean::inc(x_35);
lean::inc(x_35);
x_38 = l_Lean_Environment_contains(x_35, x_34);
x_39 = lean::cnstr_get(x_15, 7);
lean::inc(x_39);
lean::inc(x_0);
x_42 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(x_0, x_39);
lean::inc(x_35);
x_44 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(x_35, x_42, x_27);
x_45 = lean::cnstr_get(x_3, 3);
lean::inc(x_45);
lean::dec(x_3);
x_48 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(x_15, x_45, x_27);
lean::dec(x_15);
x_50 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(x_0, x_48);
x_51 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(x_35, x_50, x_27);
if (x_38 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_34);
x_53 = l_List_append___rarg(x_30, x_44);
x_54 = l_List_append___rarg(x_53, x_51);
if (lean::is_scalar(x_19)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_19;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_14;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_34);
lean::cnstr_set(x_57, 1, x_30);
x_58 = l_List_append___rarg(x_57, x_44);
x_59 = l_List_append___rarg(x_58, x_51);
if (lean::is_scalar(x_19)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_19;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_14;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
else
{
obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_3);
lean::dec(x_15);
x_64 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 1);
 x_66 = x_30;
} else {
 lean::inc(x_64);
 lean::dec(x_30);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Name_append___main(x_64, x_0);
lean::dec(x_64);
if (lean::is_scalar(x_66)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_66;
}
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_27);
if (lean::is_scalar(x_19)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_19;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_14;
}
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
else
{
obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
lean::dec(x_19);
x_76 = lean::cnstr_get(x_24, 0);
lean::inc(x_76);
lean::dec(x_24);
x_79 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 x_81 = x_76;
} else {
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::box(0);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_82);
lean::cnstr_set(x_86, 1, x_85);
if (lean::is_scalar(x_81)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_81;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_14;
}
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
}
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Elaborator_resolveContext___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_resolveContext___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_resolveContext(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_resolveContext___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_resolveContext___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_resolveContext(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_2);
x_14 = l_Lean_Elaborator_preresolve___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_30; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_10, x_1, x_2, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 0);
x_42 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
obj* l_Lean_Elaborator_preresolve___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
lean::inc(x_4);
x_8 = l_Lean_Elaborator_mangleIdent(x_4);
x_9 = l_Lean_Elaborator_resolveContext___main(x_8, x_1, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_6);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_16 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_18 = x_9;
} else {
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
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
x_24 = lean::cnstr_get(x_4, 0);
x_26 = lean::cnstr_get(x_4, 1);
x_28 = lean::cnstr_get(x_4, 2);
x_30 = lean::cnstr_get(x_4, 3);
x_32 = lean::cnstr_get(x_4, 4);
if (lean::is_exclusive(x_4)) {
 x_34 = x_4;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_4);
 x_34 = lean::box(0);
}
x_35 = l_List_append___rarg(x_19, x_30);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_24);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_28);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set(x_36, 4, x_32);
if (lean::is_scalar(x_6)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_6;
}
lean::cnstr_set(x_37, 0, x_36);
if (lean::is_scalar(x_23)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_23;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_21);
if (lean::is_scalar(x_18)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_18;
}
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
case 2:
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
x_47 = lean::cnstr_get(x_40, 2);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 lean::cnstr_set(x_40, 1, lean::box(0));
 lean::cnstr_set(x_40, 2, lean::box(0));
 x_49 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
x_50 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_45, x_1, x_2, x_3);
if (lean::obj_tag(x_50) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_42);
lean::dec(x_43);
lean::dec(x_47);
lean::dec(x_49);
x_55 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_59 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_61 = x_50;
} else {
 lean::inc(x_59);
 lean::dec(x_50);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 0);
x_64 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 x_66 = x_59;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_59);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_49;
}
lean::cnstr_set(x_67, 0, x_43);
lean::cnstr_set(x_67, 1, x_62);
lean::cnstr_set(x_67, 2, x_47);
if (lean::is_scalar(x_42)) {
 x_68 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_68 = x_42;
}
lean::cnstr_set(x_68, 0, x_67);
if (lean::is_scalar(x_66)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_66;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_64);
if (lean::is_scalar(x_61)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_61;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
default:
{
obj* x_72; obj* x_73; 
lean::dec(x_2);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_3);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_preresolve___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_preresolve___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_preresolve(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_preresolve___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_preresolve___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_preresolve(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("MODULE");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("MODULE");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint32 x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_ngen");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("fixme");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(0, 1, 4);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
}
}
obj* l_Lean_Elaborator_mkState(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::box(0);
x_4 = lean::box(0);
x_5 = l_Lean_Elaborator_mkState___closed__1;
x_6 = l_Lean_Elaborator_mkState___closed__2;
x_7 = l_Lean_Elaborator_mkState___closed__3;
x_8 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 3, x_7);
lean::cnstr_set(x_8, 4, x_7);
lean::cnstr_set(x_8, 5, x_4);
lean::cnstr_set(x_8, 6, x_3);
lean::cnstr_set(x_8, 7, x_3);
lean::cnstr_set(x_8, 8, x_2);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_Lean_Expander_builtinTransformers;
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_nat_obj(0ul);
x_18 = l_Lean_MessageLog_empty;
x_19 = l_Lean_Elaborator_mkState___closed__4;
x_20 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_3);
lean::cnstr_set(x_20, 2, x_17);
lean::cnstr_set(x_20, 3, x_3);
lean::cnstr_set(x_20, 4, x_9);
lean::cnstr_set(x_20, 5, x_18);
lean::cnstr_set(x_20, 6, x_12);
lean::cnstr_set(x_20, 7, x_16);
lean::cnstr_set(x_20, 8, x_1);
lean::cnstr_set(x_20, 9, x_19);
lean::cnstr_set(x_20, 10, x_17);
return x_20;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::mk_nat_obj(0ul);
x_14 = l_Lean_FileMap_toPosition(x_9, x_13);
x_15 = 2;
x_16 = l_String_splitAux___main___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set(x_17, 4, x_1);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_15);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_0, 0);
x_21 = l_Lean_Parser_Syntax_getPos(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::mk_nat_obj(0ul);
x_23 = l_Lean_FileMap_toPosition(x_9, x_22);
x_24 = 2;
x_25 = l_String_splitAux___main___closed__1;
x_26 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_12);
lean::cnstr_set(x_26, 3, x_25);
lean::cnstr_set(x_26, 4, x_1);
lean::cnstr_set_scalar(x_26, sizeof(void*)*5, x_24);
x_27 = x_26;
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = l_Lean_FileMap_toPosition(x_9, x_29);
x_33 = 2;
x_34 = l_String_splitAux___main___closed__1;
x_35 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_35, 0, x_7);
lean::cnstr_set(x_35, 1, x_32);
lean::cnstr_set(x_35, 2, x_12);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set(x_35, 4, x_1);
lean::cnstr_set_scalar(x_35, sizeof(void*)*5, x_33);
x_36 = x_35;
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::mk_nat_obj(0ul);
x_15 = l_Lean_FileMap_toPosition(x_10, x_14);
x_16 = 2;
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_17);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_16);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_Lean_Parser_Syntax_getPos(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_23 = lean::mk_nat_obj(0ul);
x_24 = l_Lean_FileMap_toPosition(x_10, x_23);
x_25 = 2;
x_26 = l_String_splitAux___main___closed__1;
x_27 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_27, 0, x_8);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_13);
lean::cnstr_set(x_27, 3, x_26);
lean::cnstr_set(x_27, 4, x_1);
lean::cnstr_set_scalar(x_27, sizeof(void*)*5, x_25);
x_28 = x_27;
x_29 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_30; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
lean::dec(x_22);
x_33 = l_Lean_FileMap_toPosition(x_10, x_30);
x_34 = 2;
x_35 = l_String_splitAux___main___closed__1;
x_36 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_36, 0, x_8);
lean::cnstr_set(x_36, 1, x_33);
lean::cnstr_set(x_36, 2, x_13);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set(x_36, 4, x_1);
lean::cnstr_set_scalar(x_36, sizeof(void*)*5, x_34);
x_37 = x_36;
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3(obj* x_0, obj* x_1) {
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
obj* _init_l_Lean_Elaborator_processCommand___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not a command: ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_processCommand___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_Lean_Elaborator_processCommand___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_1);
x_5 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_1);
x_8 = l_Lean_Parser_Syntax_format___main(x_1);
x_9 = l_Lean_Options_empty;
x_10 = l_Lean_Format_pretty(x_8, x_9);
x_11 = l_Lean_Elaborator_processCommand___lambda__1___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(x_7, x_12, x_0, x_2, x_3);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_7);
return x_14;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_20 = x_5;
} else {
 lean::inc(x_18);
 lean::dec(x_5);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_Lean_Elaborator_elaborators;
x_25 = l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3(x_24, x_21);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
if (lean::is_scalar(x_20)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_20;
}
lean::cnstr_set(x_26, 0, x_1);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_21);
x_29 = l_Lean_Elaborator_processCommand___lambda__1___closed__2;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(x_26, x_30, x_0, x_2, x_3);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_26);
return x_32;
}
else
{
obj* x_38; obj* x_42; 
lean::dec(x_20);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_25, 0);
lean::inc(x_38);
lean::dec(x_25);
lean::inc(x_2);
x_42 = l_Lean_Elaborator_preresolve___main(x_1, x_0, x_2, x_3);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_48 = x_42;
} else {
 lean::inc(x_46);
 lean::dec(x_42);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_58; 
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
lean::dec(x_50);
x_58 = lean::apply_4(x_38, x_53, x_0, x_2, x_55);
return x_58;
}
}
}
}
}
obj* _init_l_Lean_Elaborator_processCommand___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_processCommand___lambda__1), 4, 0);
return x_0;
}
}
obj* l_Lean_Elaborator_processCommand(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_35; obj* x_36; obj* x_37; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
x_11 = lean::cnstr_get(x_1, 4);
x_13 = lean::cnstr_get(x_1, 6);
x_15 = lean::cnstr_get(x_1, 7);
x_17 = lean::cnstr_get(x_1, 8);
x_19 = lean::cnstr_get(x_1, 9);
x_21 = lean::cnstr_get(x_1, 10);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 5);
 x_23 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_1);
 x_23 = lean::box(0);
}
x_24 = l_Lean_MessageLog_empty;
lean::inc(x_21);
lean::inc(x_19);
lean::inc(x_17);
lean::inc(x_15);
lean::inc(x_13);
lean::inc(x_11);
lean::inc(x_9);
lean::inc(x_7);
lean::inc(x_5);
lean::inc(x_3);
if (lean::is_scalar(x_23)) {
 x_35 = lean::alloc_cnstr(0, 11, 0);
} else {
 x_35 = x_23;
}
lean::cnstr_set(x_35, 0, x_3);
lean::cnstr_set(x_35, 1, x_5);
lean::cnstr_set(x_35, 2, x_7);
lean::cnstr_set(x_35, 3, x_9);
lean::cnstr_set(x_35, 4, x_11);
lean::cnstr_set(x_35, 5, x_24);
lean::cnstr_set(x_35, 6, x_13);
lean::cnstr_set(x_35, 7, x_15);
lean::cnstr_set(x_35, 8, x_17);
lean::cnstr_set(x_35, 9, x_19);
lean::cnstr_set(x_35, 10, x_21);
x_36 = l_Lean_Elaborator_processCommand___closed__1;
x_37 = lean::fixpoint3(x_36, x_2, x_0, x_35);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
lean::dec(x_37);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_24);
x_42 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_42, 0, x_3);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_7);
lean::cnstr_set(x_42, 3, x_9);
lean::cnstr_set(x_42, 4, x_11);
lean::cnstr_set(x_42, 5, x_41);
lean::cnstr_set(x_42, 6, x_13);
lean::cnstr_set(x_42, 7, x_15);
lean::cnstr_set(x_42, 8, x_17);
lean::cnstr_set(x_42, 9, x_19);
lean::cnstr_set(x_42, 10, x_21);
return x_42;
}
else
{
obj* x_53; obj* x_56; 
lean::dec(x_7);
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_13);
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_21);
x_53 = lean::cnstr_get(x_37, 0);
lean::inc(x_53);
lean::dec(x_37);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
return x_56;
}
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_lean_parser_module(obj*);
obj* initialize_init_lean_expander(obj*);
obj* initialize_init_lean_expr(obj*);
obj* initialize_init_lean_options(obj*);
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expander(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_options(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
 l_Lean_Elaborator_ElaboratorM_Monad = _init_l_Lean_Elaborator_ElaboratorM_Monad();
lean::mark_persistent(l_Lean_Elaborator_ElaboratorM_Monad);
 l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec = _init_l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec();
lean::mark_persistent(l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec);
 l_Lean_Elaborator_ElaboratorM_MonadReader = _init_l_Lean_Elaborator_ElaboratorM_MonadReader();
lean::mark_persistent(l_Lean_Elaborator_ElaboratorM_MonadReader);
 l_Lean_Elaborator_ElaboratorM_MonadState = _init_l_Lean_Elaborator_ElaboratorM_MonadState();
lean::mark_persistent(l_Lean_Elaborator_ElaboratorM_MonadState);
 l_Lean_Elaborator_ElaboratorM_MonadExcept = _init_l_Lean_Elaborator_ElaboratorM_MonadExcept();
lean::mark_persistent(l_Lean_Elaborator_ElaboratorM_MonadExcept);
 l_Lean_Elaborator_elaboratorInh___closed__1 = _init_l_Lean_Elaborator_elaboratorInh___closed__1();
lean::mark_persistent(l_Lean_Elaborator_elaboratorInh___closed__1);
 l_Lean_Elaborator_currentScope___closed__1 = _init_l_Lean_Elaborator_currentScope___closed__1();
lean::mark_persistent(l_Lean_Elaborator_currentScope___closed__1);
 l_Lean_Elaborator_modifyCurrentScope___closed__1 = _init_l_Lean_Elaborator_modifyCurrentScope___closed__1();
lean::mark_persistent(l_Lean_Elaborator_modifyCurrentScope___closed__1);
 l_Lean_Elaborator_levelGetAppArgs___main___closed__1 = _init_l_Lean_Elaborator_levelGetAppArgs___main___closed__1();
lean::mark_persistent(l_Lean_Elaborator_levelGetAppArgs___main___closed__1);
 l_Lean_Elaborator_toLevel___main___closed__1 = _init_l_Lean_Elaborator_toLevel___main___closed__1();
lean::mark_persistent(l_Lean_Elaborator_toLevel___main___closed__1);
 l_Lean_Elaborator_toLevel___main___closed__2 = _init_l_Lean_Elaborator_toLevel___main___closed__2();
lean::mark_persistent(l_Lean_Elaborator_toLevel___main___closed__2);
 l_Lean_Elaborator_toLevel___main___closed__3 = _init_l_Lean_Elaborator_toLevel___main___closed__3();
lean::mark_persistent(l_Lean_Elaborator_toLevel___main___closed__3);
 l_Lean_Elaborator_toLevel___main___closed__4 = _init_l_Lean_Elaborator_toLevel___main___closed__4();
lean::mark_persistent(l_Lean_Elaborator_toLevel___main___closed__4);
 l_Lean_Elaborator_Expr_mkAnnotation___closed__1 = _init_l_Lean_Elaborator_Expr_mkAnnotation___closed__1();
lean::mark_persistent(l_Lean_Elaborator_Expr_mkAnnotation___closed__1);
 l_Lean_Elaborator_dummy = _init_l_Lean_Elaborator_dummy();
lean::mark_persistent(l_Lean_Elaborator_dummy);
 l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1();
lean::mark_persistent(l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1);
 l_Lean_Elaborator_mkEqns___closed__1 = _init_l_Lean_Elaborator_mkEqns___closed__1();
lean::mark_persistent(l_Lean_Elaborator_mkEqns___closed__1);
 l_Lean_Elaborator_mkEqns___closed__2 = _init_l_Lean_Elaborator_mkEqns___closed__2();
lean::mark_persistent(l_Lean_Elaborator_mkEqns___closed__2);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2);
 l_Lean_Elaborator_toPexpr___main___closed__1 = _init_l_Lean_Elaborator_toPexpr___main___closed__1();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__1);
 l_Lean_Elaborator_toPexpr___main___closed__2 = _init_l_Lean_Elaborator_toPexpr___main___closed__2();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__2);
 l_Lean_Elaborator_toPexpr___main___closed__3 = _init_l_Lean_Elaborator_toPexpr___main___closed__3();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__3);
 l_Lean_Elaborator_toPexpr___main___closed__4 = _init_l_Lean_Elaborator_toPexpr___main___closed__4();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__4);
 l_Lean_Elaborator_toPexpr___main___closed__5 = _init_l_Lean_Elaborator_toPexpr___main___closed__5();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__5);
 l_Lean_Elaborator_toPexpr___main___closed__6 = _init_l_Lean_Elaborator_toPexpr___main___closed__6();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__6);
 l_Lean_Elaborator_toPexpr___main___closed__7 = _init_l_Lean_Elaborator_toPexpr___main___closed__7();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__7);
 l_Lean_Elaborator_toPexpr___main___closed__8 = _init_l_Lean_Elaborator_toPexpr___main___closed__8();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__8);
 l_Lean_Elaborator_toPexpr___main___closed__9 = _init_l_Lean_Elaborator_toPexpr___main___closed__9();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__9);
 l_Lean_Elaborator_toPexpr___main___closed__10 = _init_l_Lean_Elaborator_toPexpr___main___closed__10();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__10);
 l_Lean_Elaborator_toPexpr___main___closed__11 = _init_l_Lean_Elaborator_toPexpr___main___closed__11();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__11);
 l_Lean_Elaborator_toPexpr___main___closed__12 = _init_l_Lean_Elaborator_toPexpr___main___closed__12();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__12);
 l_Lean_Elaborator_toPexpr___main___closed__13 = _init_l_Lean_Elaborator_toPexpr___main___closed__13();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__13);
 l_Lean_Elaborator_toPexpr___main___closed__14 = _init_l_Lean_Elaborator_toPexpr___main___closed__14();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__14);
 l_Lean_Elaborator_toPexpr___main___closed__15 = _init_l_Lean_Elaborator_toPexpr___main___closed__15();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__15);
 l_Lean_Elaborator_toPexpr___main___closed__16 = _init_l_Lean_Elaborator_toPexpr___main___closed__16();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__16);
 l_Lean_Elaborator_toPexpr___main___closed__17 = _init_l_Lean_Elaborator_toPexpr___main___closed__17();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__17);
 l_Lean_Elaborator_toPexpr___main___closed__18 = _init_l_Lean_Elaborator_toPexpr___main___closed__18();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__18);
 l_Lean_Elaborator_toPexpr___main___closed__19 = _init_l_Lean_Elaborator_toPexpr___main___closed__19();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__19);
 l_Lean_Elaborator_toPexpr___main___closed__20 = _init_l_Lean_Elaborator_toPexpr___main___closed__20();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__20);
 l_Lean_Elaborator_toPexpr___main___closed__21 = _init_l_Lean_Elaborator_toPexpr___main___closed__21();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__21);
 l_Lean_Elaborator_toPexpr___main___closed__22 = _init_l_Lean_Elaborator_toPexpr___main___closed__22();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__22);
 l_Lean_Elaborator_toPexpr___main___closed__23 = _init_l_Lean_Elaborator_toPexpr___main___closed__23();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__23);
 l_Lean_Elaborator_toPexpr___main___closed__24 = _init_l_Lean_Elaborator_toPexpr___main___closed__24();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__24);
 l_Lean_Elaborator_toPexpr___main___closed__25 = _init_l_Lean_Elaborator_toPexpr___main___closed__25();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__25);
 l_Lean_Elaborator_toPexpr___main___closed__26 = _init_l_Lean_Elaborator_toPexpr___main___closed__26();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__26);
 l_Lean_Elaborator_toPexpr___main___closed__27 = _init_l_Lean_Elaborator_toPexpr___main___closed__27();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__27);
 l_Lean_Elaborator_toPexpr___main___closed__28 = _init_l_Lean_Elaborator_toPexpr___main___closed__28();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__28);
 l_Lean_Elaborator_toPexpr___main___closed__29 = _init_l_Lean_Elaborator_toPexpr___main___closed__29();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__29);
 l_Lean_Elaborator_toPexpr___main___closed__30 = _init_l_Lean_Elaborator_toPexpr___main___closed__30();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__30);
 l_Lean_Elaborator_toPexpr___main___closed__31 = _init_l_Lean_Elaborator_toPexpr___main___closed__31();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__31);
 l_Lean_Elaborator_toPexpr___main___closed__32 = _init_l_Lean_Elaborator_toPexpr___main___closed__32();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__32);
 l_Lean_Elaborator_toPexpr___main___closed__33 = _init_l_Lean_Elaborator_toPexpr___main___closed__33();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__33);
 l_Lean_Elaborator_toPexpr___main___closed__34 = _init_l_Lean_Elaborator_toPexpr___main___closed__34();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__34);
 l_Lean_Elaborator_toPexpr___main___closed__35 = _init_l_Lean_Elaborator_toPexpr___main___closed__35();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__35);
 l_Lean_Elaborator_toPexpr___main___closed__36 = _init_l_Lean_Elaborator_toPexpr___main___closed__36();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__36);
 l_Lean_Elaborator_toPexpr___main___closed__37 = _init_l_Lean_Elaborator_toPexpr___main___closed__37();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__37);
 l_Lean_Elaborator_toPexpr___main___closed__38 = _init_l_Lean_Elaborator_toPexpr___main___closed__38();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__38);
 l_Lean_Elaborator_toPexpr___main___closed__39 = _init_l_Lean_Elaborator_toPexpr___main___closed__39();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__39);
 l_Lean_Elaborator_toPexpr___main___closed__40 = _init_l_Lean_Elaborator_toPexpr___main___closed__40();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__40);
 l_Lean_Elaborator_toPexpr___main___closed__41 = _init_l_Lean_Elaborator_toPexpr___main___closed__41();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__41);
 l_Lean_Elaborator_toPexpr___main___closed__42 = _init_l_Lean_Elaborator_toPexpr___main___closed__42();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__42);
 l_Lean_Elaborator_toPexpr___main___closed__43 = _init_l_Lean_Elaborator_toPexpr___main___closed__43();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__43);
 l_Lean_Elaborator_toPexpr___main___closed__44 = _init_l_Lean_Elaborator_toPexpr___main___closed__44();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__44);
 l_Lean_Elaborator_toPexpr___main___closed__45 = _init_l_Lean_Elaborator_toPexpr___main___closed__45();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__45);
 l_Lean_Elaborator_toPexpr___main___closed__46 = _init_l_Lean_Elaborator_toPexpr___main___closed__46();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__46);
 l_Lean_Elaborator_declModifiersToPexpr___closed__1 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__1();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__1);
 l_Lean_Elaborator_declModifiersToPexpr___closed__2 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__2();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__2);
 l_Lean_Elaborator_declModifiersToPexpr___closed__3 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__3();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__3);
 l_Lean_Elaborator_declModifiersToPexpr___closed__4 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__4();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__4);
 l_Lean_Elaborator_declModifiersToPexpr___closed__5 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__5();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__5);
 l_Lean_Elaborator_declModifiersToPexpr___closed__6 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__6();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__6);
 l_Lean_Elaborator_declModifiersToPexpr___closed__7 = _init_l_Lean_Elaborator_declModifiersToPexpr___closed__7();
lean::mark_persistent(l_Lean_Elaborator_declModifiersToPexpr___closed__7);
 l_Lean_Elaborator_elabDefLike___closed__1 = _init_l_Lean_Elaborator_elabDefLike___closed__1();
lean::mark_persistent(l_Lean_Elaborator_elabDefLike___closed__1);
 l_Lean_Elaborator_elabDefLike___closed__2 = _init_l_Lean_Elaborator_elabDefLike___closed__2();
lean::mark_persistent(l_Lean_Elaborator_elabDefLike___closed__2);
 l_Lean_Elaborator_inferModToPexpr___closed__1 = _init_l_Lean_Elaborator_inferModToPexpr___closed__1();
lean::mark_persistent(l_Lean_Elaborator_inferModToPexpr___closed__1);
 l_Lean_Elaborator_inferModToPexpr___closed__2 = _init_l_Lean_Elaborator_inferModToPexpr___closed__2();
lean::mark_persistent(l_Lean_Elaborator_inferModToPexpr___closed__2);
 l_Lean_Elaborator_inferModToPexpr___closed__3 = _init_l_Lean_Elaborator_inferModToPexpr___closed__3();
lean::mark_persistent(l_Lean_Elaborator_inferModToPexpr___closed__3);
 l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_declaration_elaborate___spec__2___closed__1);
 l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1 = _init_l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__1);
 l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2 = _init_l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___lambda__3___closed__2);
 l_Lean_Elaborator_declaration_elaborate___closed__1 = _init_l_Lean_Elaborator_declaration_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___closed__1);
 l_Lean_Elaborator_declaration_elaborate___closed__2 = _init_l_Lean_Elaborator_declaration_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___closed__2);
 l_Lean_Elaborator_declaration_elaborate___closed__3 = _init_l_Lean_Elaborator_declaration_elaborate___closed__3();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___closed__3);
 l_Lean_Elaborator_declaration_elaborate___closed__4 = _init_l_Lean_Elaborator_declaration_elaborate___closed__4();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___closed__4);
 l_Lean_Elaborator_declaration_elaborate___closed__5 = _init_l_Lean_Elaborator_declaration_elaborate___closed__5();
lean::mark_persistent(l_Lean_Elaborator_declaration_elaborate___closed__5);
 l_Lean_Elaborator_variables_elaborate___closed__1 = _init_l_Lean_Elaborator_variables_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_variables_elaborate___closed__1);
 l_Lean_Elaborator_variables_elaborate___closed__2 = _init_l_Lean_Elaborator_variables_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_variables_elaborate___closed__2);
 l_Lean_Elaborator_Module_header_elaborate___closed__1 = _init_l_Lean_Elaborator_Module_header_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_Module_header_elaborate___closed__1);
 l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1 = _init_l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1();
lean::mark_persistent(l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2);
 l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3 = _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3);
 l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4 = _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4);
 l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5 = _init_l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5);
 l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1 = _init_l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1();
lean::mark_persistent(l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1);
 l_Lean_Elaborator_postprocessNotationSpec___closed__1 = _init_l_Lean_Elaborator_postprocessNotationSpec___closed__1();
lean::mark_persistent(l_Lean_Elaborator_postprocessNotationSpec___closed__1);
 l_Lean_Elaborator_notation_elaborateAux___closed__1 = _init_l_Lean_Elaborator_notation_elaborateAux___closed__1();
lean::mark_persistent(l_Lean_Elaborator_notation_elaborateAux___closed__1);
 l_Lean_Elaborator_mkNotationKind___rarg___closed__1 = _init_l_Lean_Elaborator_mkNotationKind___rarg___closed__1();
lean::mark_persistent(l_Lean_Elaborator_mkNotationKind___rarg___closed__1);
 l_Lean_Elaborator_notation_elaborate___closed__1 = _init_l_Lean_Elaborator_notation_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_notation_elaborate___closed__1);
 l_Lean_Elaborator_notation_elaborate___closed__2 = _init_l_Lean_Elaborator_notation_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_notation_elaborate___closed__2);
 l_Lean_Elaborator_universe_elaborate___closed__1 = _init_l_Lean_Elaborator_universe_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_universe_elaborate___closed__1);
 l_Lean_Elaborator_universe_elaborate___closed__2 = _init_l_Lean_Elaborator_universe_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_universe_elaborate___closed__2);
 l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2);
 l_Lean_Elaborator_attribute_elaborate___closed__1 = _init_l_Lean_Elaborator_attribute_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_attribute_elaborate___closed__1);
 l_Lean_Elaborator_attribute_elaborate___closed__2 = _init_l_Lean_Elaborator_attribute_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_attribute_elaborate___closed__2);
 l_Lean_Elaborator_check_elaborate___closed__1 = _init_l_Lean_Elaborator_check_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_check_elaborate___closed__1);
 l_Lean_Elaborator_initQuot_elaborate___closed__1 = _init_l_Lean_Elaborator_initQuot_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_initQuot_elaborate___closed__1);
 l_Lean_Elaborator_noKind_elaborate___closed__1 = _init_l_Lean_Elaborator_noKind_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_noKind_elaborate___closed__1);
 l_Lean_Elaborator_end_elaborate___closed__1 = _init_l_Lean_Elaborator_end_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_end_elaborate___closed__1);
 l_Lean_Elaborator_end_elaborate___closed__2 = _init_l_Lean_Elaborator_end_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_end_elaborate___closed__2);
 l_Lean_Elaborator_end_elaborate___closed__3 = _init_l_Lean_Elaborator_end_elaborate___closed__3();
lean::mark_persistent(l_Lean_Elaborator_end_elaborate___closed__3);
 l_Lean_Elaborator_end_elaborate___closed__4 = _init_l_Lean_Elaborator_end_elaborate___closed__4();
lean::mark_persistent(l_Lean_Elaborator_end_elaborate___closed__4);
 l_Lean_Elaborator_section_elaborate___closed__1 = _init_l_Lean_Elaborator_section_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_section_elaborate___closed__1);
 l_Lean_Elaborator_section_elaborate___closed__2 = _init_l_Lean_Elaborator_section_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_section_elaborate___closed__2);
 l_Lean_Elaborator_namespace_elaborate___closed__1 = _init_l_Lean_Elaborator_namespace_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_namespace_elaborate___closed__1);
 l_Lean_Elaborator_eoi_elaborate___closed__1 = _init_l_Lean_Elaborator_eoi_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_eoi_elaborate___closed__1);
 l_Lean_Elaborator_elaborators = _init_l_Lean_Elaborator_elaborators();
lean::mark_persistent(l_Lean_Elaborator_elaborators);
 l_Lean_Elaborator_resolveContext___main___closed__1 = _init_l_Lean_Elaborator_resolveContext___main___closed__1();
lean::mark_persistent(l_Lean_Elaborator_resolveContext___main___closed__1);
 l_Lean_Elaborator_mkState___closed__1 = _init_l_Lean_Elaborator_mkState___closed__1();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__1);
 l_Lean_Elaborator_mkState___closed__2 = _init_l_Lean_Elaborator_mkState___closed__2();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__2);
 l_Lean_Elaborator_mkState___closed__3 = _init_l_Lean_Elaborator_mkState___closed__3();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__3);
 l_Lean_Elaborator_mkState___closed__4 = _init_l_Lean_Elaborator_mkState___closed__4();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__4);
 l_Lean_Elaborator_processCommand___lambda__1___closed__1 = _init_l_Lean_Elaborator_processCommand___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__1___closed__1);
 l_Lean_Elaborator_processCommand___lambda__1___closed__2 = _init_l_Lean_Elaborator_processCommand___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__1___closed__2);
 l_Lean_Elaborator_processCommand___closed__1 = _init_l_Lean_Elaborator_processCommand___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___closed__1);
return w;
}
