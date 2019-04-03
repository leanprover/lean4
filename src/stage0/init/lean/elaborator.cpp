// Lean compiler output
// Module: init.lean.elaborator
// Imports: init.lean.parser.module init.lean.expander init.lean.expr init.lean.options
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2;
obj* l_Lean_Elaborator_postprocessNotationSpec___closed__1;
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
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(obj*);
obj* l_Lean_Elaborator_processCommand(obj*, obj*, obj*);
obj* l_Id_map___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__1;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_MonadExcept;
obj* l_Lean_Elaborator_toPexpr___main___closed__6;
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__21;
obj* l_Lean_Elaborator_matchSpec(obj*, obj*);
obj* l_Lean_Elaborator_matchOpenSpec(obj*, obj*);
obj* l_RBTree_toList___at_Lean_Elaborator_oldElabCommand___spec__1(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Elaborator_toPexpr___main___closed__22;
obj* l_Lean_Elaborator_ElaboratorM_MonadState;
obj* l_Lean_Elaborator_elaborators;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2;
obj* l_StateT_Monad___rarg(obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__2;
obj* l_Lean_Elaborator_variables_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__37;
extern "C" obj* level_mk_mvar(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg(obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__3;
obj* l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__9;
extern obj* l_Lean_Parser_command_attribute;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__30;
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
extern obj* l_Lean_Parser_command_variables;
obj* l_Lean_Elaborator_elabDefLike(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__4;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(obj*, obj*, obj*, obj*);
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_mangleIdent___spec__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__3;
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___lambda__1(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__28;
extern obj* l_Lean_Parser_Term_have_HasView;
obj* l_Lean_Expr_mkCapp(obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__19;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___boxed(obj*);
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
obj* l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__45;
extern obj* l_Lean_Options_empty;
obj* l_Lean_Elaborator_section_elaborate___closed__2;
obj* l_Lean_Elaborator_universe_elaborate___closed__2;
obj* l_Lean_Elaborator_toPexpr___main___closed__1;
extern obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Elaborator_check_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___rarg___boxed(obj*);
obj* l_monadStateTrans___rarg(obj*, obj*);
obj* l_Lean_Elaborator_namesToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___boxed(obj*, obj*);
obj* l_Lean_Name_quickLt___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Lean_Elaborator_mkState___closed__4;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj*);
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_section;
obj* l_Lean_Elaborator_toPexpr___main___closed__14;
obj* l_ExceptT_MonadExcept___rarg(obj*);
extern obj* l_Lean_Parser_command_attribute_HasView;
obj* l_Lean_Elaborator_toPexpr___main___closed__32;
extern obj* l_Lean_Parser_command_reserveNotation_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj*, obj*);
extern obj* l_Lean_Parser_command_export_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__1;
obj* l_Lean_Elaborator_notation_elaborateAux(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderIdent_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__18;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__6;
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__10;
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__3(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__44;
obj* l_Lean_Elaborator_levelAdd___main(obj*, obj*);
extern obj* l_Lean_Parser_command_end_HasView;
obj* l_Lean_Elaborator_attribute_elaborate___closed__2;
obj* l_Lean_Elaborator_elaboratorInh___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4;
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj*, obj*);
obj* l_fix1___rarg___lambda__1___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_end;
extern obj* l_Lean_Parser_Term_sort_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__27;
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1;
extern "C" obj* level_mk_param(obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_command_export;
obj* l_Lean_Elaborator_end_elaborate___closed__4;
obj* l_Lean_Elaborator_mangleIdent(obj*);
obj* l_Lean_Elaborator_universe_elaborate___lambda__1(obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace___main(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2(obj*);
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__12;
extern obj* l_Lean_Parser_Term_show_HasView;
obj* l_List_join___main___rarg(obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__29;
extern obj* l_Lean_Parser_Term_structInstItem_HasView;
extern obj* l_Lean_Parser_command_setOption_HasView;
obj* l_Lean_Elaborator_Expr_mkAnnotation___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
obj* l_Lean_Elaborator_toPexpr(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__20;
extern obj* l_Lean_Parser_command_initQuot;
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2;
obj* l_Lean_Elaborator_matchSpec___closed__1;
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
obj* l_Lean_Elaborator_Declaration_elaborate___closed__3;
obj* l_Lean_Elaborator_end_elaborate___closed__3;
obj* l_Lean_Elaborator_toPexpr___main___closed__33;
obj* l_Lean_Elaborator_notation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkEqns___closed__1;
obj* l_Id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
extern obj* l_Lean_Expander_builtinTransformers;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___boxed(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__4;
extern obj* l_Char_HasRepr___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__2(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Elaborator_toPexpr___main___closed__39;
extern obj* l_Lean_Parser_Term_lambda_HasView;
obj* l_RBNode_ins___main___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__36;
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3;
obj* l_Lean_Elaborator_isOpenNamespace___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Module_header_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj*, obj*);
extern obj* l_Lean_Parser_command_setOption;
obj* l_Lean_Expander_mkNotationTransformer(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Elaborator_matchPrecedence___main___boxed(obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Module_eoi;
obj* l_Lean_Elaborator_attrsToPexpr(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4___boxed(obj*, obj*);
obj* l_Lean_Elaborator_elaborateCommand___boxed(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_identUnivParamsToPexpr___spec__1(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1(uint8, obj*);
obj* l_Lean_Elaborator_inferModToPexpr(obj*);
obj* l_Lean_Elaborator_Expr_mkAnnotation(obj*, obj*);
obj* l_StateT_MonadExcept___rarg(obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate___closed__1;
obj* l_Lean_Elaborator_currentScope___closed__1;
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(obj*);
obj* l_Lean_Elaborator_setOption_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate___closed__1;
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___boxed(obj*);
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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_Declaration;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find(obj*, obj*);
obj* l_Lean_Elaborator_preresolve(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Expander_expandBracketedBinder___main___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__13;
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__1;
obj* l_Lean_Elaborator_mkEqns___closed__2;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Elaborator_processCommand___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1;
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_open;
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_Id_pure___boxed(obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation_HasView;
extern obj* l_Lean_Parser_command_section_HasView;
obj* l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Term_app_HasView;
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate___lambda__1(obj*, obj*);
uint8 l_Lean_Elaborator_matchPrecedence(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__2;
extern obj* l_Lean_Parser_Term_projection_HasView;
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
extern obj* l_Lean_Parser_maxPrec;
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1(obj*, obj*);
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
obj* l_Lean_Elaborator_toLevel___main___closed__5;
extern obj* l_Lean_Parser_command_universe;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__7;
extern "C" obj* level_mk_succ(obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__43;
extern obj* l_Lean_Expander_bindingAnnotationUpdate;
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace_HasView;
obj* l_Lean_Elaborator_setOption_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__1;
obj* l_Lean_Elaborator_levelGetAppArgs___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___closed__1;
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__1;
obj* l_Lean_Elaborator_modifyCurrentScope___closed__1;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(obj*);
obj* l_Lean_Elaborator_getNamespace___boxed(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__5;
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__24;
obj* l_Id_bind___boxed(obj*, obj*);
uint8 l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_Lean_environment_contains___boxed(obj*, obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Term_borrowed_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__26;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___lambda__1(obj*, obj*);
extern "C" uint8 lean_environment_contains(obj*, obj*);
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
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__35;
obj* l_Lean_Elaborator_toPexpr___main___closed__7;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Elaborator_Module_header_elaborate___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_updateParserConfig(obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadReader;
obj* l_Lean_Elaborator_toPexpr___main___closed__41;
obj* l_Lean_Elaborator_toPexpr___main___closed__25;
obj* l_Lean_Elaborator_attribute_elaborate___closed__1;
extern obj* l_List_mmap___main___rarg___closed__1;
obj* l_RBNode_find___main___at_Lean_Elaborator_processCommand___spec__3(obj*, obj*);
obj* l_Lean_Elaborator_matchPrecedence___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(obj*, obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_kind___main(obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5;
obj* l_Lean_Elaborator_variables_elaborate___closed__1;
obj* l_Lean_Elaborator_modifyCurrentScope(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_export_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__5;
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_Monad;
obj* l_Lean_Elaborator_levelAdd(obj*, obj*);
obj* l_Lean_Elaborator_eoi_elaborate(obj*, obj*, obj*, obj*);
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
extern obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Elaborator_toLevel___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_currentScope(obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___boxed(obj*);
extern obj* l_Lean_Parser_Term_inaccessible_HasView;
obj* l_Lean_Elaborator_precToNat___main(obj*);
obj* l_Lean_Elaborator_include_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__1;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_match_HasView;
obj* l_Lean_Parser_Term_getLeading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig___boxed(obj*);
obj* l_Lean_Expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__1;
extern obj* l_Lean_Parser_command_Declaration_HasView;
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(obj*);
extern obj* l_Lean_Expander_noExpansion___closed__1;
extern obj* l_Lean_Parser_Term_sort_HasView;
obj* l_Lean_Elaborator_resolveContext(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__23;
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Elaborator_Declaration_elaborate___closed__2;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__2;
extern obj* l_Lean_Parser_command_reserveNotation;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___closed__1;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj*, obj*);
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1___boxed(obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1(obj*, uint8, obj*, obj*);
uint8 l_Lean_Elaborator_matchPrecedence___main(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__2;
obj* l_Lean_Elaborator_initQuot_elaborate___closed__1;
obj* l_Lean_Parser_Syntax_toFormat___main(obj*);
obj* l_StateT_MonadState___rarg(obj*);
obj* l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1___boxed(obj*, obj*);
extern obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___closed__1;
obj* l_Lean_Elaborator_getNamespace(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_let_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_toNat___main(obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_Parser_Term_binders_Parser(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_environment_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean_environment_contains(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; uint8 x_18; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_add(x_6, x_8);
lean::inc(x_3);
lean::inc(x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_3);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_3);
x_18 = l_RBNode_isRed___main___rarg(x_4);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = l_RBNode_ins___main___rarg(x_0, x_4, x_2, x_17);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_9);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = l_RBNode_ins___main___rarg(x_0, x_4, x_2, x_17);
x_22 = l_RBNode_setBlack___main___rarg(x_21);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_9);
return x_23;
}
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
x_10 = l_ExceptT_Monad___rarg(x_9);
x_11 = l_StateT_Monad___rarg(x_10);
x_12 = l_ReaderT_Monad___rarg(x_11);
x_13 = l_ReaderT_Monad___rarg(x_12);
return x_13;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
x_10 = l_ExceptT_Monad___rarg(x_9);
x_11 = l_StateT_Monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___rarg___boxed), 2, 1);
lean::closure_set(x_13, 0, x_12);
return x_13;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_MonadState() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_10 = l_ExceptT_Monad___rarg(x_9);
lean::inc(x_10);
x_12 = l_StateT_Monad___rarg(x_10);
lean::inc(x_12);
x_14 = l_ReaderT_Monad___rarg(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___boxed), 4, 3);
lean::closure_set(x_16, 0, lean::box(0));
lean::closure_set(x_16, 1, lean::box(0));
lean::closure_set(x_16, 2, x_12);
x_17 = l_StateT_MonadState___rarg(x_10);
x_18 = l_monadStateTrans___rarg(x_16, x_17);
x_19 = l_monadStateTrans___rarg(x_15, x_18);
return x_19;
}
}
obj* _init_l_Lean_Elaborator_ElaboratorM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_11 = l_ExceptT_Monad___rarg(x_9);
x_12 = l_ExceptT_MonadExcept___rarg(x_9);
x_13 = l_StateT_MonadExcept___rarg(x_11, lean::box(0), x_12);
x_14 = l_ReaderT_MonadExcept___rarg(x_13);
x_15 = l_ReaderT_MonadExcept___rarg(x_14);
return x_15;
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
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_2);
x_12 = lean::cnstr_get(x_4, 0);
x_14 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_16 = x_4;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_4);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_3, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_3, 3);
lean::inc(x_23);
x_25 = lean::apply_1(x_0, x_12);
if (lean::is_scalar(x_16)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_16;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_14);
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
lean::dec(x_3);
x_40 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_40, 0, x_17);
lean::cnstr_set(x_40, 1, x_19);
lean::cnstr_set(x_40, 2, x_21);
lean::cnstr_set(x_40, 3, x_23);
lean::cnstr_set(x_40, 4, x_26);
lean::cnstr_set(x_40, 5, x_27);
lean::cnstr_set(x_40, 6, x_29);
lean::cnstr_set(x_40, 7, x_31);
lean::cnstr_set(x_40, 8, x_33);
lean::cnstr_set(x_40, 9, x_35);
lean::cnstr_set(x_40, 10, x_37);
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
x_8 = l_Lean_Parser_Syntax_toFormat___main(x_0);
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
x_27 = l_Lean_Parser_Syntax_toFormat___main(x_0);
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
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_1, x_2, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
x_7 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_9 = x_5;
} else {
 lean::inc(x_7);
 lean::dec(x_5);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_11, 0);
x_16 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = lean::apply_1(x_0, x_14);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toLevel___main), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(x_0, x_5);
x_9 = level_mk_max(x_3, x_8);
return x_9;
}
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5(x_0, x_5);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Name_quickLt___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toLevel___main___closed__5() {
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
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_24; obj* x_28; 
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
lean::dec(x_6);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_17, 1);
lean::inc(x_24);
lean::dec(x_17);
lean::inc(x_2);
x_28 = l_Lean_Elaborator_currentScope(x_1, x_2, x_19);
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_22);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
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
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; 
x_38 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 x_40 = x_28;
} else {
 lean::inc(x_38);
 lean::dec(x_28);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 lean::cnstr_set(x_38, 1, lean::box(0));
 x_45 = x_38;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
lean::inc(x_22);
x_47 = l_Lean_Parser_Syntax_kind___main(x_22);
if (lean::obj_tag(x_47) == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
lean::inc(x_0);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_0);
x_55 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_56 = l_Lean_Options_empty;
x_57 = l_Lean_Format_pretty(x_55, x_56);
x_58 = l_Lean_Elaborator_toLevel___main___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_54, x_59, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_54);
return x_61;
}
else
{
obj* x_65; obj* x_67; obj* x_68; uint8 x_69; 
x_65 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 x_67 = x_47;
} else {
 lean::inc(x_65);
 lean::dec(x_47);
 x_67 = lean::box(0);
}
x_68 = l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
x_69 = lean_name_dec_eq(x_65, x_68);
if (x_69 == 0)
{
obj* x_73; uint8 x_74; 
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
x_73 = l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
x_74 = lean_name_dec_eq(x_65, x_73);
lean::dec(x_65);
if (x_74 == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_22);
lean::dec(x_24);
lean::inc(x_0);
if (lean::is_scalar(x_67)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_67;
}
lean::cnstr_set(x_79, 0, x_0);
x_80 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_81 = l_Lean_Options_empty;
x_82 = l_Lean_Format_pretty(x_80, x_81);
x_83 = l_Lean_Elaborator_toLevel___main___closed__1;
x_84 = lean::string_append(x_83, x_82);
lean::dec(x_82);
x_86 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_79, x_84, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_79);
return x_86;
}
else
{
obj* x_90; obj* x_91; obj* x_94; 
x_90 = l_Lean_Parser_Level_trailing_HasView;
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
lean::dec(x_90);
x_94 = lean::apply_1(x_91, x_22);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_94);
lean::dec(x_24);
if (lean::is_scalar(x_67)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_67;
}
lean::cnstr_set(x_97, 0, x_0);
x_98 = l_Lean_Elaborator_toLevel___main___closed__2;
x_99 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_97, x_98, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_97);
return x_99;
}
else
{
if (lean::obj_tag(x_24) == 0)
{
obj* x_105; obj* x_108; obj* x_110; 
lean::dec(x_0);
lean::dec(x_67);
x_105 = lean::cnstr_get(x_94, 0);
lean::inc(x_105);
lean::dec(x_94);
x_108 = lean::cnstr_get(x_105, 0);
lean::inc(x_108);
x_110 = l_Lean_Elaborator_toLevel___main(x_108, x_1, x_2, x_43);
if (lean::obj_tag(x_110) == 0)
{
obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_105);
x_112 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_114 = x_110;
} else {
 lean::inc(x_112);
 lean::dec(x_110);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
return x_115;
}
else
{
obj* x_116; obj* x_118; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_127; obj* x_128; obj* x_131; obj* x_132; 
x_116 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_118 = x_110;
} else {
 lean::inc(x_116);
 lean::dec(x_110);
 x_118 = lean::box(0);
}
x_119 = lean::cnstr_get(x_116, 0);
x_121 = lean::cnstr_get(x_116, 1);
if (lean::is_exclusive(x_116)) {
 x_123 = x_116;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_105, 2);
lean::inc(x_124);
lean::dec(x_105);
x_127 = l_Lean_Parser_number_View_toNat___main(x_124);
x_128 = l_Lean_Elaborator_levelAdd___main(x_119, x_127);
lean::dec(x_127);
lean::dec(x_119);
if (lean::is_scalar(x_123)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_123;
}
lean::cnstr_set(x_131, 0, x_128);
lean::cnstr_set(x_131, 1, x_121);
if (lean::is_scalar(x_118)) {
 x_132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_132 = x_118;
}
lean::cnstr_set(x_132, 0, x_131);
return x_132;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_94);
lean::dec(x_24);
if (lean::is_scalar(x_67)) {
 x_135 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_135 = x_67;
}
lean::cnstr_set(x_135, 0, x_0);
x_136 = l_Lean_Elaborator_toLevel___main___closed__2;
x_137 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_135, x_136, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_135);
return x_137;
}
}
}
}
else
{
obj* x_142; obj* x_143; obj* x_146; 
lean::dec(x_65);
x_142 = l_Lean_Parser_Level_leading_HasView;
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
lean::dec(x_142);
x_146 = lean::apply_1(x_143, x_22);
switch (lean::obj_tag(x_146)) {
case 0:
{
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
lean::dec(x_146);
if (lean::obj_tag(x_24) == 0)
{
obj* x_151; obj* x_152; obj* x_153; 
if (lean::is_scalar(x_67)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_67;
}
lean::cnstr_set(x_151, 0, x_0);
x_152 = l_Lean_Elaborator_toLevel___main___closed__2;
x_153 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_151, x_152, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_151);
return x_153;
}
else
{
obj* x_159; obj* x_161; obj* x_166; 
lean::dec(x_0);
lean::dec(x_67);
x_159 = lean::cnstr_get(x_24, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_24, 1);
lean::inc(x_161);
lean::dec(x_24);
lean::inc(x_2);
lean::inc(x_1);
x_166 = l_Lean_Elaborator_toLevel___main(x_159, x_1, x_2, x_43);
if (lean::obj_tag(x_166) == 0)
{
obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_161);
lean::dec(x_1);
lean::dec(x_2);
x_170 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 x_172 = x_166;
} else {
 lean::inc(x_170);
 lean::dec(x_166);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
return x_173;
}
else
{
obj* x_174; obj* x_177; obj* x_179; obj* x_182; 
x_174 = lean::cnstr_get(x_166, 0);
lean::inc(x_174);
lean::dec(x_166);
x_177 = lean::cnstr_get(x_174, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_174, 1);
lean::inc(x_179);
lean::dec(x_174);
x_182 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_161, x_1, x_2, x_179);
if (lean::obj_tag(x_182) == 0)
{
obj* x_184; obj* x_186; obj* x_187; 
lean::dec(x_177);
x_184 = lean::cnstr_get(x_182, 0);
if (lean::is_exclusive(x_182)) {
 x_186 = x_182;
} else {
 lean::inc(x_184);
 lean::dec(x_182);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_184);
return x_187;
}
else
{
obj* x_188; obj* x_190; obj* x_191; obj* x_193; obj* x_195; obj* x_196; obj* x_198; obj* x_199; 
x_188 = lean::cnstr_get(x_182, 0);
if (lean::is_exclusive(x_182)) {
 x_190 = x_182;
} else {
 lean::inc(x_188);
 lean::dec(x_182);
 x_190 = lean::box(0);
}
x_191 = lean::cnstr_get(x_188, 0);
x_193 = lean::cnstr_get(x_188, 1);
if (lean::is_exclusive(x_188)) {
 x_195 = x_188;
} else {
 lean::inc(x_191);
 lean::inc(x_193);
 lean::dec(x_188);
 x_195 = lean::box(0);
}
x_196 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(x_177, x_191);
lean::dec(x_177);
if (lean::is_scalar(x_195)) {
 x_198 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_198 = x_195;
}
lean::cnstr_set(x_198, 0, x_196);
lean::cnstr_set(x_198, 1, x_193);
if (lean::is_scalar(x_190)) {
 x_199 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_199 = x_190;
}
lean::cnstr_set(x_199, 0, x_198);
return x_199;
}
}
}
}
case 1:
{
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
lean::dec(x_146);
if (lean::obj_tag(x_24) == 0)
{
obj* x_204; obj* x_205; obj* x_206; 
if (lean::is_scalar(x_67)) {
 x_204 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_204 = x_67;
}
lean::cnstr_set(x_204, 0, x_0);
x_205 = l_Lean_Elaborator_toLevel___main___closed__2;
x_206 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_204, x_205, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_204);
return x_206;
}
else
{
obj* x_212; obj* x_214; obj* x_219; 
lean::dec(x_0);
lean::dec(x_67);
x_212 = lean::cnstr_get(x_24, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_24, 1);
lean::inc(x_214);
lean::dec(x_24);
lean::inc(x_2);
lean::inc(x_1);
x_219 = l_Lean_Elaborator_toLevel___main(x_212, x_1, x_2, x_43);
if (lean::obj_tag(x_219) == 0)
{
obj* x_223; obj* x_225; obj* x_226; 
lean::dec(x_214);
lean::dec(x_1);
lean::dec(x_2);
x_223 = lean::cnstr_get(x_219, 0);
if (lean::is_exclusive(x_219)) {
 x_225 = x_219;
} else {
 lean::inc(x_223);
 lean::dec(x_219);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_223);
return x_226;
}
else
{
obj* x_227; obj* x_230; obj* x_232; obj* x_235; 
x_227 = lean::cnstr_get(x_219, 0);
lean::inc(x_227);
lean::dec(x_219);
x_230 = lean::cnstr_get(x_227, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_227, 1);
lean::inc(x_232);
lean::dec(x_227);
x_235 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_214, x_1, x_2, x_232);
if (lean::obj_tag(x_235) == 0)
{
obj* x_237; obj* x_239; obj* x_240; 
lean::dec(x_230);
x_237 = lean::cnstr_get(x_235, 0);
if (lean::is_exclusive(x_235)) {
 x_239 = x_235;
} else {
 lean::inc(x_237);
 lean::dec(x_235);
 x_239 = lean::box(0);
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_237);
return x_240;
}
else
{
obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_249; obj* x_251; obj* x_252; 
x_241 = lean::cnstr_get(x_235, 0);
if (lean::is_exclusive(x_235)) {
 x_243 = x_235;
} else {
 lean::inc(x_241);
 lean::dec(x_235);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_241, 0);
x_246 = lean::cnstr_get(x_241, 1);
if (lean::is_exclusive(x_241)) {
 x_248 = x_241;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::dec(x_241);
 x_248 = lean::box(0);
}
x_249 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5(x_230, x_244);
lean::dec(x_230);
if (lean::is_scalar(x_248)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_248;
}
lean::cnstr_set(x_251, 0, x_249);
lean::cnstr_set(x_251, 1, x_246);
if (lean::is_scalar(x_243)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_243;
}
lean::cnstr_set(x_252, 0, x_251);
return x_252;
}
}
}
}
case 2:
{
lean::dec(x_41);
lean::dec(x_146);
if (lean::obj_tag(x_24) == 0)
{
obj* x_259; obj* x_260; obj* x_261; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_67);
x_259 = l_Lean_Elaborator_toLevel___main___closed__3;
if (lean::is_scalar(x_45)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_45;
}
lean::cnstr_set(x_260, 0, x_259);
lean::cnstr_set(x_260, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_261 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_261 = x_40;
}
lean::cnstr_set(x_261, 0, x_260);
return x_261;
}
else
{
obj* x_265; obj* x_266; obj* x_267; 
lean::dec(x_24);
lean::dec(x_40);
lean::dec(x_45);
if (lean::is_scalar(x_67)) {
 x_265 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_265 = x_67;
}
lean::cnstr_set(x_265, 0, x_0);
x_266 = l_Lean_Elaborator_toLevel___main___closed__2;
x_267 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_265, x_266, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_265);
return x_267;
}
}
case 3:
{
obj* x_276; obj* x_277; obj* x_278; 
lean::dec(x_24);
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
lean::dec(x_146);
if (lean::is_scalar(x_67)) {
 x_276 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_276 = x_67;
}
lean::cnstr_set(x_276, 0, x_0);
x_277 = l_Lean_Elaborator_toLevel___main___closed__2;
x_278 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_276, x_277, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_276);
return x_278;
}
case 4:
{
lean::dec(x_41);
if (lean::obj_tag(x_24) == 0)
{
obj* x_287; obj* x_290; obj* x_291; obj* x_293; obj* x_294; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_67);
x_287 = lean::cnstr_get(x_146, 0);
lean::inc(x_287);
lean::dec(x_146);
x_290 = l_Lean_Parser_number_View_toNat___main(x_287);
x_291 = l_Lean_Level_ofNat___main(x_290);
lean::dec(x_290);
if (lean::is_scalar(x_45)) {
 x_293 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_293 = x_45;
}
lean::cnstr_set(x_293, 0, x_291);
lean::cnstr_set(x_293, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_294 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_294 = x_40;
}
lean::cnstr_set(x_294, 0, x_293);
return x_294;
}
else
{
obj* x_299; obj* x_300; obj* x_301; 
lean::dec(x_24);
lean::dec(x_40);
lean::dec(x_45);
lean::dec(x_146);
if (lean::is_scalar(x_67)) {
 x_299 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_299 = x_67;
}
lean::cnstr_set(x_299, 0, x_0);
x_300 = l_Lean_Elaborator_toLevel___main___closed__2;
x_301 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_299, x_300, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_299);
return x_301;
}
}
default:
{
if (lean::obj_tag(x_24) == 0)
{
obj* x_305; obj* x_308; obj* x_309; obj* x_312; obj* x_314; 
x_305 = lean::cnstr_get(x_146, 0);
lean::inc(x_305);
lean::dec(x_146);
x_308 = l_Lean_Elaborator_mangleIdent(x_305);
x_309 = lean::cnstr_get(x_41, 3);
lean::inc(x_309);
lean::dec(x_41);
x_312 = l_Lean_Elaborator_toLevel___main___closed__4;
lean::inc(x_308);
x_314 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_312, x_309, x_308);
if (lean::obj_tag(x_314) == 0)
{
obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_40);
lean::dec(x_45);
if (lean::is_scalar(x_67)) {
 x_317 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_317 = x_67;
}
lean::cnstr_set(x_317, 0, x_0);
x_318 = l_Lean_Name_toString___closed__1;
x_319 = l_Lean_Name_toStringWithSep___main(x_318, x_308);
x_320 = l_Lean_Elaborator_toLevel___main___closed__5;
x_321 = lean::string_append(x_320, x_319);
lean::dec(x_319);
x_323 = l_Char_HasRepr___closed__1;
x_324 = lean::string_append(x_321, x_323);
x_325 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_317, x_324, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_317);
return x_325;
}
else
{
obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_314);
lean::dec(x_67);
x_334 = level_mk_param(x_308);
if (lean::is_scalar(x_45)) {
 x_335 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_335 = x_45;
}
lean::cnstr_set(x_335, 0, x_334);
lean::cnstr_set(x_335, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_336 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_336 = x_40;
}
lean::cnstr_set(x_336, 0, x_335);
return x_336;
}
}
else
{
obj* x_342; obj* x_343; obj* x_344; 
lean::dec(x_24);
lean::dec(x_40);
lean::dec(x_41);
lean::dec(x_45);
lean::dec(x_146);
if (lean::is_scalar(x_67)) {
 x_342 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_342 = x_67;
}
lean::cnstr_set(x_342, 0, x_0);
x_343 = l_Lean_Elaborator_toLevel___main___closed__2;
x_344 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_342, x_343, x_1, x_2, x_43);
lean::dec(x_43);
lean::dec(x_1);
lean::dec(x_342);
return x_344;
}
}
}
}
}
}
}
}
}
obj* l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__5(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_16; obj* x_20; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_6, 1);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_0);
x_20 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(x_0, x_8);
x_21 = 4;
lean::inc(x_11);
x_23 = lean_expr_local(x_11, x_11, x_0, x_21);
x_24 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_25 = l_Lean_Elaborator_Expr_mkAnnotation(x_24, x_23);
x_26 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_25, x_14);
x_27 = lean_expr_mk_app(x_26, x_16);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_Lean_Elaborator_toPexpr___main(x_4, x_1, x_2, x_3);
return x_7;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___lambda__1), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_matchFn");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_4, x_1, x_2, x_3);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_14 = x_8;
} else {
 lean::inc(x_12);
 lean::dec(x_8);
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
obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_27; 
x_16 = lean::cnstr_get(x_8, 0);
lean::inc(x_16);
lean::dec(x_8);
x_19 = lean::cnstr_get(x_16, 0);
x_21 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_23 = x_16;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_0, 2);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_Lean_Elaborator_toPexpr___main(x_24, x_1, x_2, x_21);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_19);
lean::dec(x_23);
x_30 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_30);
 lean::dec(x_27);
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_34 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_36 = x_27;
} else {
 lean::inc(x_34);
 lean::dec(x_27);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_34, 0);
x_39 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 x_41 = x_34;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_34);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_19);
lean::cnstr_set(x_42, 1, x_37);
x_43 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1;
if (lean::is_scalar(x_23)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_23;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_39);
if (lean::is_scalar(x_36)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_36;
}
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toPexpr: unreachable");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
x_14 = l_Lean_Elaborator_toPexpr___main(x_12, x_2, x_3, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_18 = x_14;
} else {
 lean::inc(x_16);
 lean::dec(x_14);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_20 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_22 = x_14;
} else {
 lean::inc(x_20);
 lean::dec(x_14);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_20);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_9, 0);
lean::inc(x_28);
lean::dec(x_9);
x_31 = l_Lean_Elaborator_mangleIdent(x_28);
x_32 = lean::box(0);
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1;
x_34 = l_Lean_KVMap_setName(x_32, x_33, x_31);
x_35 = lean_expr_mk_mdata(x_34, x_23);
if (lean::is_scalar(x_27)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_27;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_25);
if (lean::is_scalar(x_22)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_22;
}
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_5);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_1);
x_40 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2;
x_41 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_39, x_40, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_39);
return x_41;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_1);
x_10 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2;
x_11 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_9, x_10, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_9);
return x_11;
}
else
{
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_1);
x_22 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2;
x_23 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_21, x_22, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_21);
return x_23;
}
else
{
obj* x_28; obj* x_31; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_31 = l_Lean_Elaborator_toPexpr___main(x_28, x_2, x_3, x_4);
return x_31;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toPexpr___main), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toLevel), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
lean::dec(x_1);
lean::dec(x_59);
if (lean::obj_tag(x_66) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_0);
lean::dec(x_2);
x_72 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_74 = x_66;
} else {
 lean::inc(x_72);
 lean::dec(x_66);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
return x_75;
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_84; 
x_76 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_78 = x_66;
} else {
 lean::inc(x_76);
 lean::dec(x_66);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_76, 0);
x_81 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_set(x_76, 0, lean::box(0));
 lean::cnstr_set(x_76, 1, lean::box(0));
 x_83 = x_76;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_76);
 x_83 = lean::box(0);
}
x_84 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_84) == 0)
{
obj* x_87; obj* x_88; 
lean::dec(x_2);
if (lean::is_scalar(x_83)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_83;
}
lean::cnstr_set(x_87, 0, x_79);
lean::cnstr_set(x_87, 1, x_81);
if (lean::is_scalar(x_78)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_78;
}
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
else
{
obj* x_89; obj* x_92; obj* x_95; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_89 = lean::cnstr_get(x_84, 0);
lean::inc(x_89);
lean::dec(x_84);
x_92 = lean::cnstr_get(x_2, 0);
lean::inc(x_92);
lean::dec(x_2);
x_95 = lean::cnstr_get(x_92, 2);
lean::inc(x_95);
lean::dec(x_92);
x_98 = l_Lean_FileMap_toPosition(x_95, x_89);
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
x_101 = lean::box(0);
x_102 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_103 = l_Lean_KVMap_setNat(x_101, x_102, x_99);
x_104 = lean::cnstr_get(x_98, 0);
lean::inc(x_104);
lean::dec(x_98);
x_107 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_108 = l_Lean_KVMap_setNat(x_103, x_107, x_104);
x_109 = lean_expr_mk_mdata(x_108, x_79);
if (lean::is_scalar(x_83)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_83;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_81);
if (lean::is_scalar(x_78)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_78;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_117; obj* x_118; obj* x_120; obj* x_123; 
x_112 = l_Lean_Parser_Term_match_HasView;
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
lean::dec(x_112);
lean::inc(x_0);
x_117 = lean::apply_1(x_113, x_0);
x_118 = lean::cnstr_get(x_117, 5);
lean::inc(x_118);
x_120 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(x_118);
lean::inc(x_2);
lean::inc(x_1);
x_123 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_120, x_1, x_2, x_3);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_117);
lean::dec(x_1);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
x_13 = x_129;
goto lbl_14;
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_138; obj* x_140; obj* x_144; 
x_130 = lean::cnstr_get(x_123, 0);
lean::inc(x_130);
lean::dec(x_123);
x_133 = lean::cnstr_get(x_130, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_130, 1);
lean::inc(x_135);
lean::dec(x_130);
x_138 = lean::cnstr_get(x_117, 2);
lean::inc(x_138);
x_140 = l_Lean_Expander_getOptType___main(x_138);
lean::dec(x_138);
lean::inc(x_2);
lean::inc(x_1);
x_144 = l_Lean_Elaborator_toPexpr___main(x_140, x_1, x_2, x_135);
if (lean::obj_tag(x_144) == 0)
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_117);
lean::dec(x_133);
lean::dec(x_1);
x_148 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_150 = x_144;
} else {
 lean::inc(x_148);
 lean::dec(x_144);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_13 = x_151;
goto lbl_14;
}
else
{
obj* x_152; obj* x_155; obj* x_157; obj* x_160; 
x_152 = lean::cnstr_get(x_144, 0);
lean::inc(x_152);
lean::dec(x_144);
x_155 = lean::cnstr_get(x_152, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_152, 1);
lean::inc(x_157);
lean::dec(x_152);
x_160 = l_Lean_Elaborator_mkEqns(x_155, x_133);
switch (lean::obj_tag(x_160)) {
case 10:
{
obj* x_161; obj* x_163; obj* x_166; obj* x_170; 
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_160, 1);
lean::inc(x_163);
lean::dec(x_160);
x_166 = lean::cnstr_get(x_117, 1);
lean::inc(x_166);
lean::dec(x_117);
lean::inc(x_2);
x_170 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_166, x_1, x_2, x_157);
if (lean::obj_tag(x_170) == 0)
{
obj* x_173; obj* x_175; obj* x_176; 
lean::dec(x_163);
lean::dec(x_161);
x_173 = lean::cnstr_get(x_170, 0);
if (lean::is_exclusive(x_170)) {
 x_175 = x_170;
} else {
 lean::inc(x_173);
 lean::dec(x_170);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_13 = x_176;
goto lbl_14;
}
else
{
obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_177 = lean::cnstr_get(x_170, 0);
if (lean::is_exclusive(x_170)) {
 x_179 = x_170;
} else {
 lean::inc(x_177);
 lean::dec(x_170);
 x_179 = lean::box(0);
}
x_180 = lean::cnstr_get(x_177, 0);
x_182 = lean::cnstr_get(x_177, 1);
if (lean::is_exclusive(x_177)) {
 x_184 = x_177;
} else {
 lean::inc(x_180);
 lean::inc(x_182);
 lean::dec(x_177);
 x_184 = lean::box(0);
}
x_185 = l_Lean_Elaborator_toPexpr___main___closed__22;
x_186 = 1;
x_187 = l_Lean_KVMap_setBool(x_161, x_185, x_186);
x_188 = lean_expr_mk_mdata(x_187, x_163);
x_189 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_188, x_180);
if (lean::is_scalar(x_184)) {
 x_190 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_190 = x_184;
}
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_182);
if (lean::is_scalar(x_179)) {
 x_191 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_191 = x_179;
}
lean::cnstr_set(x_191, 0, x_190);
x_13 = x_191;
goto lbl_14;
}
}
default:
{
obj* x_195; obj* x_196; obj* x_198; 
lean::dec(x_160);
lean::dec(x_117);
lean::inc(x_0);
x_195 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_195, 0, x_0);
x_196 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2;
lean::inc(x_2);
x_198 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_195, x_196, x_1, x_2, x_157);
lean::dec(x_157);
lean::dec(x_1);
lean::dec(x_195);
x_13 = x_198;
goto lbl_14;
}
}
}
}
}
}
else
{
obj* x_202; obj* x_203; obj* x_207; obj* x_208; obj* x_210; obj* x_211; obj* x_212; obj* x_214; obj* x_217; obj* x_218; 
x_202 = l_Lean_Parser_Term_structInst_HasView;
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
lean::dec(x_202);
lean::inc(x_0);
x_207 = lean::apply_1(x_203, x_0);
x_208 = lean::cnstr_get(x_207, 3);
lean::inc(x_208);
x_210 = lean::box(0);
x_211 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_208, x_210);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
x_217 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_214, x_210);
x_218 = lean::cnstr_get(x_217, 1);
lean::inc(x_218);
if (lean::obj_tag(x_218) == 0)
{
obj* x_220; obj* x_226; 
x_220 = lean::cnstr_get(x_217, 0);
lean::inc(x_220);
lean::dec(x_217);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_226 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_212, x_1, x_2, x_3);
if (lean::obj_tag(x_226) == 0)
{
obj* x_233; obj* x_235; obj* x_236; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_220);
lean::dec(x_207);
x_233 = lean::cnstr_get(x_226, 0);
if (lean::is_exclusive(x_226)) {
 x_235 = x_226;
} else {
 lean::inc(x_233);
 lean::dec(x_226);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
return x_236;
}
else
{
obj* x_237; obj* x_240; obj* x_242; obj* x_245; obj* x_250; 
x_237 = lean::cnstr_get(x_226, 0);
lean::inc(x_237);
lean::dec(x_226);
x_240 = lean::cnstr_get(x_237, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get(x_237, 1);
lean::inc(x_242);
lean::dec(x_237);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_250 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_220, x_1, x_2, x_242);
if (lean::obj_tag(x_250) == 0)
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_240);
lean::dec(x_207);
x_257 = lean::cnstr_get(x_250, 0);
if (lean::is_exclusive(x_250)) {
 x_259 = x_250;
} else {
 lean::inc(x_257);
 lean::dec(x_250);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_257);
return x_260;
}
else
{
obj* x_261; obj* x_264; 
x_261 = lean::cnstr_get(x_250, 0);
lean::inc(x_261);
lean::dec(x_250);
x_264 = lean::cnstr_get(x_207, 2);
lean::inc(x_264);
if (lean::obj_tag(x_264) == 0)
{
obj* x_267; obj* x_269; obj* x_271; obj* x_272; 
lean::dec(x_1);
x_267 = lean::cnstr_get(x_261, 0);
x_269 = lean::cnstr_get(x_261, 1);
if (lean::is_exclusive(x_261)) {
 x_271 = x_261;
} else {
 lean::inc(x_267);
 lean::inc(x_269);
 lean::dec(x_261);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_267);
lean::cnstr_set(x_272, 1, x_269);
x_245 = x_272;
goto lbl_246;
}
else
{
obj* x_273; obj* x_275; obj* x_278; obj* x_281; obj* x_285; 
x_273 = lean::cnstr_get(x_261, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_261, 1);
lean::inc(x_275);
lean::dec(x_261);
x_278 = lean::cnstr_get(x_264, 0);
lean::inc(x_278);
lean::dec(x_264);
x_281 = lean::cnstr_get(x_278, 0);
lean::inc(x_281);
lean::dec(x_278);
lean::inc(x_2);
x_285 = l_Lean_Elaborator_toPexpr___main(x_281, x_1, x_2, x_275);
if (lean::obj_tag(x_285) == 0)
{
obj* x_292; obj* x_294; obj* x_295; 
lean::dec(x_273);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_240);
lean::dec(x_207);
x_292 = lean::cnstr_get(x_285, 0);
if (lean::is_exclusive(x_285)) {
 x_294 = x_285;
} else {
 lean::inc(x_292);
 lean::dec(x_285);
 x_294 = lean::box(0);
}
if (lean::is_scalar(x_294)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_294;
}
lean::cnstr_set(x_295, 0, x_292);
return x_295;
}
else
{
obj* x_296; obj* x_299; obj* x_301; obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
x_296 = lean::cnstr_get(x_285, 0);
lean::inc(x_296);
lean::dec(x_285);
x_299 = lean::cnstr_get(x_296, 0);
x_301 = lean::cnstr_get(x_296, 1);
if (lean::is_exclusive(x_296)) {
 x_303 = x_296;
} else {
 lean::inc(x_299);
 lean::inc(x_301);
 lean::dec(x_296);
 x_303 = lean::box(0);
}
x_304 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_304, 0, x_299);
lean::cnstr_set(x_304, 1, x_210);
x_305 = l_List_append___rarg(x_273, x_304);
if (lean::is_scalar(x_303)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_303;
}
lean::cnstr_set(x_306, 0, x_305);
lean::cnstr_set(x_306, 1, x_301);
x_245 = x_306;
goto lbl_246;
}
}
}
lbl_246:
{
obj* x_307; obj* x_309; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; uint8 x_317; obj* x_318; obj* x_319; obj* x_322; obj* x_323; obj* x_324; 
x_307 = lean::cnstr_get(x_245, 0);
x_309 = lean::cnstr_get(x_245, 1);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_set(x_245, 0, lean::box(0));
 lean::cnstr_set(x_245, 1, lean::box(0));
 x_311 = x_245;
} else {
 lean::inc(x_307);
 lean::inc(x_309);
 lean::dec(x_245);
 x_311 = lean::box(0);
}
x_312 = lean::mk_nat_obj(0ul);
x_313 = l_List_lengthAux___main___rarg(x_240, x_312);
x_314 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_315 = l_Lean_KVMap_setNat(x_210, x_314, x_313);
x_316 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_317 = 0;
x_318 = l_Lean_KVMap_setBool(x_315, x_316, x_317);
x_319 = lean::cnstr_get(x_207, 1);
lean::inc(x_319);
lean::dec(x_207);
x_322 = l_List_append___rarg(x_240, x_307);
x_323 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_324 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_323, x_322);
if (lean::obj_tag(x_319) == 0)
{
obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
x_325 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_326 = lean::box(0);
x_327 = l_Lean_KVMap_setName(x_318, x_325, x_326);
x_328 = lean_expr_mk_mdata(x_327, x_324);
if (lean::is_scalar(x_311)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_311;
}
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_309);
x_15 = x_329;
goto lbl_16;
}
else
{
obj* x_330; obj* x_333; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; 
x_330 = lean::cnstr_get(x_319, 0);
lean::inc(x_330);
lean::dec(x_319);
x_333 = lean::cnstr_get(x_330, 0);
lean::inc(x_333);
lean::dec(x_330);
x_336 = l_Lean_Elaborator_mangleIdent(x_333);
x_337 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_338 = l_Lean_KVMap_setName(x_318, x_337, x_336);
x_339 = lean_expr_mk_mdata(x_338, x_324);
if (lean::is_scalar(x_311)) {
 x_340 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_340 = x_311;
}
lean::cnstr_set(x_340, 0, x_339);
lean::cnstr_set(x_340, 1, x_309);
x_15 = x_340;
goto lbl_16;
}
}
}
}
else
{
obj* x_341; obj* x_343; 
x_341 = lean::cnstr_get(x_218, 0);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_341, 0);
lean::inc(x_343);
lean::dec(x_341);
if (lean::obj_tag(x_343) == 0)
{
obj* x_346; obj* x_347; obj* x_350; obj* x_351; obj* x_354; obj* x_355; obj* x_356; obj* x_358; 
if (lean::is_exclusive(x_218)) {
 lean::cnstr_release(x_218, 0);
 lean::cnstr_release(x_218, 1);
 x_346 = x_218;
} else {
 lean::dec(x_218);
 x_346 = lean::box(0);
}
x_347 = lean::cnstr_get(x_217, 0);
lean::inc(x_347);
lean::dec(x_217);
x_350 = l_Lean_Parser_Term_structInstItem_HasView;
x_351 = lean::cnstr_get(x_350, 1);
lean::inc(x_351);
lean::dec(x_350);
x_354 = lean::apply_1(x_351, x_343);
x_355 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_355, 0, x_354);
x_356 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_358 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_355, x_356, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_355);
if (lean::obj_tag(x_358) == 0)
{
obj* x_369; obj* x_371; obj* x_372; 
lean::dec(x_346);
lean::dec(x_347);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_212);
lean::dec(x_207);
x_369 = lean::cnstr_get(x_358, 0);
if (lean::is_exclusive(x_358)) {
 x_371 = x_358;
} else {
 lean::inc(x_369);
 lean::dec(x_358);
 x_371 = lean::box(0);
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_369);
return x_372;
}
else
{
obj* x_373; obj* x_376; obj* x_378; obj* x_384; 
x_373 = lean::cnstr_get(x_358, 0);
lean::inc(x_373);
lean::dec(x_358);
x_376 = lean::cnstr_get(x_373, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_373, 1);
lean::inc(x_378);
lean::dec(x_373);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_384 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_212, x_1, x_2, x_378);
if (lean::obj_tag(x_384) == 0)
{
obj* x_393; obj* x_395; obj* x_396; 
lean::dec(x_346);
lean::dec(x_347);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_207);
x_393 = lean::cnstr_get(x_384, 0);
if (lean::is_exclusive(x_384)) {
 x_395 = x_384;
} else {
 lean::inc(x_393);
 lean::dec(x_384);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_393);
return x_396;
}
else
{
obj* x_397; obj* x_400; obj* x_402; obj* x_405; obj* x_410; 
x_397 = lean::cnstr_get(x_384, 0);
lean::inc(x_397);
lean::dec(x_384);
x_400 = lean::cnstr_get(x_397, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_397, 1);
lean::inc(x_402);
lean::dec(x_397);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_410 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_347, x_1, x_2, x_402);
if (lean::obj_tag(x_410) == 0)
{
obj* x_419; obj* x_421; obj* x_422; 
lean::dec(x_346);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_400);
lean::dec(x_207);
x_419 = lean::cnstr_get(x_410, 0);
if (lean::is_exclusive(x_410)) {
 x_421 = x_410;
} else {
 lean::inc(x_419);
 lean::dec(x_410);
 x_421 = lean::box(0);
}
if (lean::is_scalar(x_421)) {
 x_422 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_422 = x_421;
}
lean::cnstr_set(x_422, 0, x_419);
return x_422;
}
else
{
obj* x_423; obj* x_426; 
x_423 = lean::cnstr_get(x_410, 0);
lean::inc(x_423);
lean::dec(x_410);
x_426 = lean::cnstr_get(x_207, 2);
lean::inc(x_426);
if (lean::obj_tag(x_426) == 0)
{
obj* x_430; obj* x_432; obj* x_434; obj* x_435; 
lean::dec(x_346);
lean::dec(x_1);
x_430 = lean::cnstr_get(x_423, 0);
x_432 = lean::cnstr_get(x_423, 1);
if (lean::is_exclusive(x_423)) {
 x_434 = x_423;
} else {
 lean::inc(x_430);
 lean::inc(x_432);
 lean::dec(x_423);
 x_434 = lean::box(0);
}
if (lean::is_scalar(x_434)) {
 x_435 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_435 = x_434;
}
lean::cnstr_set(x_435, 0, x_430);
lean::cnstr_set(x_435, 1, x_432);
x_405 = x_435;
goto lbl_406;
}
else
{
obj* x_436; obj* x_438; obj* x_441; obj* x_444; obj* x_448; 
x_436 = lean::cnstr_get(x_423, 0);
lean::inc(x_436);
x_438 = lean::cnstr_get(x_423, 1);
lean::inc(x_438);
lean::dec(x_423);
x_441 = lean::cnstr_get(x_426, 0);
lean::inc(x_441);
lean::dec(x_426);
x_444 = lean::cnstr_get(x_441, 0);
lean::inc(x_444);
lean::dec(x_441);
lean::inc(x_2);
x_448 = l_Lean_Elaborator_toPexpr___main(x_444, x_1, x_2, x_438);
if (lean::obj_tag(x_448) == 0)
{
obj* x_457; obj* x_459; obj* x_460; 
lean::dec(x_346);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_400);
lean::dec(x_436);
lean::dec(x_207);
x_457 = lean::cnstr_get(x_448, 0);
if (lean::is_exclusive(x_448)) {
 x_459 = x_448;
} else {
 lean::inc(x_457);
 lean::dec(x_448);
 x_459 = lean::box(0);
}
if (lean::is_scalar(x_459)) {
 x_460 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_460 = x_459;
}
lean::cnstr_set(x_460, 0, x_457);
return x_460;
}
else
{
obj* x_461; obj* x_464; obj* x_466; obj* x_468; obj* x_469; obj* x_470; obj* x_471; 
x_461 = lean::cnstr_get(x_448, 0);
lean::inc(x_461);
lean::dec(x_448);
x_464 = lean::cnstr_get(x_461, 0);
x_466 = lean::cnstr_get(x_461, 1);
if (lean::is_exclusive(x_461)) {
 x_468 = x_461;
} else {
 lean::inc(x_464);
 lean::inc(x_466);
 lean::dec(x_461);
 x_468 = lean::box(0);
}
if (lean::is_scalar(x_346)) {
 x_469 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_469 = x_346;
}
lean::cnstr_set(x_469, 0, x_464);
lean::cnstr_set(x_469, 1, x_210);
x_470 = l_List_append___rarg(x_436, x_469);
if (lean::is_scalar(x_468)) {
 x_471 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_471 = x_468;
}
lean::cnstr_set(x_471, 0, x_470);
lean::cnstr_set(x_471, 1, x_466);
x_405 = x_471;
goto lbl_406;
}
}
}
lbl_406:
{
obj* x_472; obj* x_474; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; uint8 x_482; obj* x_483; obj* x_484; obj* x_487; obj* x_488; obj* x_489; 
x_472 = lean::cnstr_get(x_405, 0);
x_474 = lean::cnstr_get(x_405, 1);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_set(x_405, 0, lean::box(0));
 lean::cnstr_set(x_405, 1, lean::box(0));
 x_476 = x_405;
} else {
 lean::inc(x_472);
 lean::inc(x_474);
 lean::dec(x_405);
 x_476 = lean::box(0);
}
x_477 = lean::mk_nat_obj(0ul);
x_478 = l_List_lengthAux___main___rarg(x_400, x_477);
x_479 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_480 = l_Lean_KVMap_setNat(x_210, x_479, x_478);
x_481 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_482 = lean::unbox(x_376);
x_483 = l_Lean_KVMap_setBool(x_480, x_481, x_482);
x_484 = lean::cnstr_get(x_207, 1);
lean::inc(x_484);
lean::dec(x_207);
x_487 = l_List_append___rarg(x_400, x_472);
x_488 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_489 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_488, x_487);
if (lean::obj_tag(x_484) == 0)
{
obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; 
x_490 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_491 = lean::box(0);
x_492 = l_Lean_KVMap_setName(x_483, x_490, x_491);
x_493 = lean_expr_mk_mdata(x_492, x_489);
if (lean::is_scalar(x_476)) {
 x_494 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_494 = x_476;
}
lean::cnstr_set(x_494, 0, x_493);
lean::cnstr_set(x_494, 1, x_474);
x_15 = x_494;
goto lbl_16;
}
else
{
obj* x_495; obj* x_498; obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; 
x_495 = lean::cnstr_get(x_484, 0);
lean::inc(x_495);
lean::dec(x_484);
x_498 = lean::cnstr_get(x_495, 0);
lean::inc(x_498);
lean::dec(x_495);
x_501 = l_Lean_Elaborator_mangleIdent(x_498);
x_502 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_503 = l_Lean_KVMap_setName(x_483, x_502, x_501);
x_504 = lean_expr_mk_mdata(x_503, x_489);
if (lean::is_scalar(x_476)) {
 x_505 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_505 = x_476;
}
lean::cnstr_set(x_505, 0, x_504);
lean::cnstr_set(x_505, 1, x_474);
x_15 = x_505;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_506; obj* x_508; 
x_506 = lean::cnstr_get(x_218, 1);
if (lean::is_exclusive(x_218)) {
 lean::cnstr_release(x_218, 0);
 lean::cnstr_set(x_218, 1, lean::box(0));
 x_508 = x_218;
} else {
 lean::inc(x_506);
 lean::dec(x_218);
 x_508 = lean::box(0);
}
if (lean::obj_tag(x_506) == 0)
{
obj* x_510; obj* x_516; 
lean::dec(x_343);
x_510 = lean::cnstr_get(x_217, 0);
lean::inc(x_510);
lean::dec(x_217);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_516 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_212, x_1, x_2, x_3);
if (lean::obj_tag(x_516) == 0)
{
obj* x_524; obj* x_526; obj* x_527; 
lean::dec(x_508);
lean::dec(x_510);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_207);
x_524 = lean::cnstr_get(x_516, 0);
if (lean::is_exclusive(x_516)) {
 x_526 = x_516;
} else {
 lean::inc(x_524);
 lean::dec(x_516);
 x_526 = lean::box(0);
}
if (lean::is_scalar(x_526)) {
 x_527 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_527 = x_526;
}
lean::cnstr_set(x_527, 0, x_524);
return x_527;
}
else
{
obj* x_528; obj* x_531; obj* x_533; obj* x_536; obj* x_541; 
x_528 = lean::cnstr_get(x_516, 0);
lean::inc(x_528);
lean::dec(x_516);
x_531 = lean::cnstr_get(x_528, 0);
lean::inc(x_531);
x_533 = lean::cnstr_get(x_528, 1);
lean::inc(x_533);
lean::dec(x_528);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_541 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_510, x_1, x_2, x_533);
if (lean::obj_tag(x_541) == 0)
{
obj* x_549; obj* x_551; obj* x_552; 
lean::dec(x_508);
lean::dec(x_531);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_207);
x_549 = lean::cnstr_get(x_541, 0);
if (lean::is_exclusive(x_541)) {
 x_551 = x_541;
} else {
 lean::inc(x_549);
 lean::dec(x_541);
 x_551 = lean::box(0);
}
if (lean::is_scalar(x_551)) {
 x_552 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_552 = x_551;
}
lean::cnstr_set(x_552, 0, x_549);
return x_552;
}
else
{
obj* x_553; obj* x_556; 
x_553 = lean::cnstr_get(x_541, 0);
lean::inc(x_553);
lean::dec(x_541);
x_556 = lean::cnstr_get(x_207, 2);
lean::inc(x_556);
if (lean::obj_tag(x_556) == 0)
{
obj* x_560; obj* x_562; obj* x_564; obj* x_565; 
lean::dec(x_508);
lean::dec(x_1);
x_560 = lean::cnstr_get(x_553, 0);
x_562 = lean::cnstr_get(x_553, 1);
if (lean::is_exclusive(x_553)) {
 x_564 = x_553;
} else {
 lean::inc(x_560);
 lean::inc(x_562);
 lean::dec(x_553);
 x_564 = lean::box(0);
}
if (lean::is_scalar(x_564)) {
 x_565 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_565 = x_564;
}
lean::cnstr_set(x_565, 0, x_560);
lean::cnstr_set(x_565, 1, x_562);
x_536 = x_565;
goto lbl_537;
}
else
{
obj* x_566; obj* x_568; obj* x_571; obj* x_574; obj* x_578; 
x_566 = lean::cnstr_get(x_553, 0);
lean::inc(x_566);
x_568 = lean::cnstr_get(x_553, 1);
lean::inc(x_568);
lean::dec(x_553);
x_571 = lean::cnstr_get(x_556, 0);
lean::inc(x_571);
lean::dec(x_556);
x_574 = lean::cnstr_get(x_571, 0);
lean::inc(x_574);
lean::dec(x_571);
lean::inc(x_2);
x_578 = l_Lean_Elaborator_toPexpr___main(x_574, x_1, x_2, x_568);
if (lean::obj_tag(x_578) == 0)
{
obj* x_586; obj* x_588; obj* x_589; 
lean::dec(x_566);
lean::dec(x_508);
lean::dec(x_531);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_207);
x_586 = lean::cnstr_get(x_578, 0);
if (lean::is_exclusive(x_578)) {
 x_588 = x_578;
} else {
 lean::inc(x_586);
 lean::dec(x_578);
 x_588 = lean::box(0);
}
if (lean::is_scalar(x_588)) {
 x_589 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_589 = x_588;
}
lean::cnstr_set(x_589, 0, x_586);
return x_589;
}
else
{
obj* x_590; obj* x_593; obj* x_595; obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
x_590 = lean::cnstr_get(x_578, 0);
lean::inc(x_590);
lean::dec(x_578);
x_593 = lean::cnstr_get(x_590, 0);
x_595 = lean::cnstr_get(x_590, 1);
if (lean::is_exclusive(x_590)) {
 x_597 = x_590;
} else {
 lean::inc(x_593);
 lean::inc(x_595);
 lean::dec(x_590);
 x_597 = lean::box(0);
}
if (lean::is_scalar(x_508)) {
 x_598 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_598 = x_508;
}
lean::cnstr_set(x_598, 0, x_593);
lean::cnstr_set(x_598, 1, x_210);
x_599 = l_List_append___rarg(x_566, x_598);
if (lean::is_scalar(x_597)) {
 x_600 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_600 = x_597;
}
lean::cnstr_set(x_600, 0, x_599);
lean::cnstr_set(x_600, 1, x_595);
x_536 = x_600;
goto lbl_537;
}
}
}
lbl_537:
{
obj* x_601; obj* x_603; obj* x_605; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; uint8 x_611; obj* x_612; obj* x_613; obj* x_616; obj* x_617; obj* x_618; 
x_601 = lean::cnstr_get(x_536, 0);
x_603 = lean::cnstr_get(x_536, 1);
if (lean::is_exclusive(x_536)) {
 lean::cnstr_set(x_536, 0, lean::box(0));
 lean::cnstr_set(x_536, 1, lean::box(0));
 x_605 = x_536;
} else {
 lean::inc(x_601);
 lean::inc(x_603);
 lean::dec(x_536);
 x_605 = lean::box(0);
}
x_606 = lean::mk_nat_obj(0ul);
x_607 = l_List_lengthAux___main___rarg(x_531, x_606);
x_608 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_609 = l_Lean_KVMap_setNat(x_210, x_608, x_607);
x_610 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_611 = 1;
x_612 = l_Lean_KVMap_setBool(x_609, x_610, x_611);
x_613 = lean::cnstr_get(x_207, 1);
lean::inc(x_613);
lean::dec(x_207);
x_616 = l_List_append___rarg(x_531, x_601);
x_617 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_618 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_617, x_616);
if (lean::obj_tag(x_613) == 0)
{
obj* x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; 
x_619 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_620 = lean::box(0);
x_621 = l_Lean_KVMap_setName(x_612, x_619, x_620);
x_622 = lean_expr_mk_mdata(x_621, x_618);
if (lean::is_scalar(x_605)) {
 x_623 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_623 = x_605;
}
lean::cnstr_set(x_623, 0, x_622);
lean::cnstr_set(x_623, 1, x_603);
x_15 = x_623;
goto lbl_16;
}
else
{
obj* x_624; obj* x_627; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; 
x_624 = lean::cnstr_get(x_613, 0);
lean::inc(x_624);
lean::dec(x_613);
x_627 = lean::cnstr_get(x_624, 0);
lean::inc(x_627);
lean::dec(x_624);
x_630 = l_Lean_Elaborator_mangleIdent(x_627);
x_631 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_632 = l_Lean_KVMap_setName(x_612, x_631, x_630);
x_633 = lean_expr_mk_mdata(x_632, x_618);
if (lean::is_scalar(x_605)) {
 x_634 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_634 = x_605;
}
lean::cnstr_set(x_634, 0, x_633);
lean::cnstr_set(x_634, 1, x_603);
x_15 = x_634;
goto lbl_16;
}
}
}
}
else
{
obj* x_636; obj* x_637; obj* x_640; obj* x_641; obj* x_644; obj* x_645; obj* x_646; obj* x_648; 
lean::dec(x_508);
if (lean::is_exclusive(x_506)) {
 lean::cnstr_release(x_506, 0);
 lean::cnstr_release(x_506, 1);
 x_636 = x_506;
} else {
 lean::dec(x_506);
 x_636 = lean::box(0);
}
x_637 = lean::cnstr_get(x_217, 0);
lean::inc(x_637);
lean::dec(x_217);
x_640 = l_Lean_Parser_Term_structInstItem_HasView;
x_641 = lean::cnstr_get(x_640, 1);
lean::inc(x_641);
lean::dec(x_640);
x_644 = lean::apply_1(x_641, x_343);
x_645 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_645, 0, x_644);
x_646 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_648 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_645, x_646, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_645);
if (lean::obj_tag(x_648) == 0)
{
obj* x_659; obj* x_661; obj* x_662; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_636);
lean::dec(x_637);
lean::dec(x_212);
lean::dec(x_207);
x_659 = lean::cnstr_get(x_648, 0);
if (lean::is_exclusive(x_648)) {
 x_661 = x_648;
} else {
 lean::inc(x_659);
 lean::dec(x_648);
 x_661 = lean::box(0);
}
if (lean::is_scalar(x_661)) {
 x_662 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_662 = x_661;
}
lean::cnstr_set(x_662, 0, x_659);
return x_662;
}
else
{
obj* x_663; obj* x_666; obj* x_668; obj* x_674; 
x_663 = lean::cnstr_get(x_648, 0);
lean::inc(x_663);
lean::dec(x_648);
x_666 = lean::cnstr_get(x_663, 0);
lean::inc(x_666);
x_668 = lean::cnstr_get(x_663, 1);
lean::inc(x_668);
lean::dec(x_663);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_674 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_212, x_1, x_2, x_668);
if (lean::obj_tag(x_674) == 0)
{
obj* x_683; obj* x_685; obj* x_686; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_666);
lean::dec(x_2);
lean::dec(x_636);
lean::dec(x_637);
lean::dec(x_207);
x_683 = lean::cnstr_get(x_674, 0);
if (lean::is_exclusive(x_674)) {
 x_685 = x_674;
} else {
 lean::inc(x_683);
 lean::dec(x_674);
 x_685 = lean::box(0);
}
if (lean::is_scalar(x_685)) {
 x_686 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_686 = x_685;
}
lean::cnstr_set(x_686, 0, x_683);
return x_686;
}
else
{
obj* x_687; obj* x_690; obj* x_692; obj* x_695; obj* x_700; 
x_687 = lean::cnstr_get(x_674, 0);
lean::inc(x_687);
lean::dec(x_674);
x_690 = lean::cnstr_get(x_687, 0);
lean::inc(x_690);
x_692 = lean::cnstr_get(x_687, 1);
lean::inc(x_692);
lean::dec(x_687);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_700 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_637, x_1, x_2, x_692);
if (lean::obj_tag(x_700) == 0)
{
obj* x_709; obj* x_711; obj* x_712; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_666);
lean::dec(x_2);
lean::dec(x_690);
lean::dec(x_636);
lean::dec(x_207);
x_709 = lean::cnstr_get(x_700, 0);
if (lean::is_exclusive(x_700)) {
 x_711 = x_700;
} else {
 lean::inc(x_709);
 lean::dec(x_700);
 x_711 = lean::box(0);
}
if (lean::is_scalar(x_711)) {
 x_712 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_712 = x_711;
}
lean::cnstr_set(x_712, 0, x_709);
return x_712;
}
else
{
obj* x_713; obj* x_716; 
x_713 = lean::cnstr_get(x_700, 0);
lean::inc(x_713);
lean::dec(x_700);
x_716 = lean::cnstr_get(x_207, 2);
lean::inc(x_716);
if (lean::obj_tag(x_716) == 0)
{
obj* x_720; obj* x_722; obj* x_724; obj* x_725; 
lean::dec(x_1);
lean::dec(x_636);
x_720 = lean::cnstr_get(x_713, 0);
x_722 = lean::cnstr_get(x_713, 1);
if (lean::is_exclusive(x_713)) {
 x_724 = x_713;
} else {
 lean::inc(x_720);
 lean::inc(x_722);
 lean::dec(x_713);
 x_724 = lean::box(0);
}
if (lean::is_scalar(x_724)) {
 x_725 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_725 = x_724;
}
lean::cnstr_set(x_725, 0, x_720);
lean::cnstr_set(x_725, 1, x_722);
x_695 = x_725;
goto lbl_696;
}
else
{
obj* x_726; obj* x_728; obj* x_731; obj* x_734; obj* x_738; 
x_726 = lean::cnstr_get(x_713, 0);
lean::inc(x_726);
x_728 = lean::cnstr_get(x_713, 1);
lean::inc(x_728);
lean::dec(x_713);
x_731 = lean::cnstr_get(x_716, 0);
lean::inc(x_731);
lean::dec(x_716);
x_734 = lean::cnstr_get(x_731, 0);
lean::inc(x_734);
lean::dec(x_731);
lean::inc(x_2);
x_738 = l_Lean_Elaborator_toPexpr___main(x_734, x_1, x_2, x_728);
if (lean::obj_tag(x_738) == 0)
{
obj* x_747; obj* x_749; obj* x_750; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_666);
lean::dec(x_2);
lean::dec(x_690);
lean::dec(x_636);
lean::dec(x_726);
lean::dec(x_207);
x_747 = lean::cnstr_get(x_738, 0);
if (lean::is_exclusive(x_738)) {
 x_749 = x_738;
} else {
 lean::inc(x_747);
 lean::dec(x_738);
 x_749 = lean::box(0);
}
if (lean::is_scalar(x_749)) {
 x_750 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_750 = x_749;
}
lean::cnstr_set(x_750, 0, x_747);
return x_750;
}
else
{
obj* x_751; obj* x_754; obj* x_756; obj* x_758; obj* x_759; obj* x_760; obj* x_761; 
x_751 = lean::cnstr_get(x_738, 0);
lean::inc(x_751);
lean::dec(x_738);
x_754 = lean::cnstr_get(x_751, 0);
x_756 = lean::cnstr_get(x_751, 1);
if (lean::is_exclusive(x_751)) {
 x_758 = x_751;
} else {
 lean::inc(x_754);
 lean::inc(x_756);
 lean::dec(x_751);
 x_758 = lean::box(0);
}
if (lean::is_scalar(x_636)) {
 x_759 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_759 = x_636;
}
lean::cnstr_set(x_759, 0, x_754);
lean::cnstr_set(x_759, 1, x_210);
x_760 = l_List_append___rarg(x_726, x_759);
if (lean::is_scalar(x_758)) {
 x_761 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_761 = x_758;
}
lean::cnstr_set(x_761, 0, x_760);
lean::cnstr_set(x_761, 1, x_756);
x_695 = x_761;
goto lbl_696;
}
}
}
lbl_696:
{
obj* x_762; obj* x_764; obj* x_766; obj* x_767; obj* x_768; obj* x_769; obj* x_770; obj* x_771; uint8 x_772; obj* x_773; obj* x_774; obj* x_777; obj* x_778; obj* x_779; 
x_762 = lean::cnstr_get(x_695, 0);
x_764 = lean::cnstr_get(x_695, 1);
if (lean::is_exclusive(x_695)) {
 lean::cnstr_set(x_695, 0, lean::box(0));
 lean::cnstr_set(x_695, 1, lean::box(0));
 x_766 = x_695;
} else {
 lean::inc(x_762);
 lean::inc(x_764);
 lean::dec(x_695);
 x_766 = lean::box(0);
}
x_767 = lean::mk_nat_obj(0ul);
x_768 = l_List_lengthAux___main___rarg(x_690, x_767);
x_769 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_770 = l_Lean_KVMap_setNat(x_210, x_769, x_768);
x_771 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_772 = lean::unbox(x_666);
x_773 = l_Lean_KVMap_setBool(x_770, x_771, x_772);
x_774 = lean::cnstr_get(x_207, 1);
lean::inc(x_774);
lean::dec(x_207);
x_777 = l_List_append___rarg(x_690, x_762);
x_778 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_779 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_778, x_777);
if (lean::obj_tag(x_774) == 0)
{
obj* x_780; obj* x_781; obj* x_782; obj* x_783; obj* x_784; 
x_780 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_781 = lean::box(0);
x_782 = l_Lean_KVMap_setName(x_773, x_780, x_781);
x_783 = lean_expr_mk_mdata(x_782, x_779);
if (lean::is_scalar(x_766)) {
 x_784 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_784 = x_766;
}
lean::cnstr_set(x_784, 0, x_783);
lean::cnstr_set(x_784, 1, x_764);
x_15 = x_784;
goto lbl_16;
}
else
{
obj* x_785; obj* x_788; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; 
x_785 = lean::cnstr_get(x_774, 0);
lean::inc(x_785);
lean::dec(x_774);
x_788 = lean::cnstr_get(x_785, 0);
lean::inc(x_788);
lean::dec(x_785);
x_791 = l_Lean_Elaborator_mangleIdent(x_788);
x_792 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_793 = l_Lean_KVMap_setName(x_773, x_792, x_791);
x_794 = lean_expr_mk_mdata(x_793, x_779);
if (lean::is_scalar(x_766)) {
 x_795 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_795 = x_766;
}
lean::cnstr_set(x_795, 0, x_794);
lean::cnstr_set(x_795, 1, x_764);
x_15 = x_795;
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
obj* x_799; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_10);
x_799 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_799) == 0)
{
obj* x_805; obj* x_807; obj* x_808; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_805 = lean::cnstr_get(x_799, 0);
if (lean::is_exclusive(x_799)) {
 x_807 = x_799;
} else {
 lean::inc(x_805);
 lean::dec(x_799);
 x_807 = lean::box(0);
}
if (lean::is_scalar(x_807)) {
 x_808 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_808 = x_807;
}
lean::cnstr_set(x_808, 0, x_805);
return x_808;
}
else
{
obj* x_809; obj* x_812; obj* x_814; obj* x_816; obj* x_817; 
x_809 = lean::cnstr_get(x_799, 0);
lean::inc(x_809);
lean::dec(x_799);
x_812 = lean::cnstr_get(x_809, 0);
x_814 = lean::cnstr_get(x_809, 1);
if (lean::is_exclusive(x_809)) {
 lean::cnstr_set(x_809, 0, lean::box(0));
 lean::cnstr_set(x_809, 1, lean::box(0));
 x_816 = x_809;
} else {
 lean::inc(x_812);
 lean::inc(x_814);
 lean::dec(x_809);
 x_816 = lean::box(0);
}
x_817 = l_List_reverse___rarg(x_812);
if (lean::obj_tag(x_817) == 0)
{
obj* x_821; obj* x_822; obj* x_824; 
lean::dec(x_816);
lean::dec(x_10);
lean::inc(x_0);
x_821 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_821, 0, x_0);
x_822 = l_Lean_Elaborator_toPexpr___main___closed__28;
lean::inc(x_2);
x_824 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_821, x_822, x_1, x_2, x_814);
lean::dec(x_814);
lean::dec(x_1);
lean::dec(x_821);
if (lean::obj_tag(x_824) == 0)
{
obj* x_831; obj* x_833; obj* x_834; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_831 = lean::cnstr_get(x_824, 0);
if (lean::is_exclusive(x_824)) {
 x_833 = x_824;
} else {
 lean::inc(x_831);
 lean::dec(x_824);
 x_833 = lean::box(0);
}
if (lean::is_scalar(x_833)) {
 x_834 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_834 = x_833;
}
lean::cnstr_set(x_834, 0, x_831);
return x_834;
}
else
{
obj* x_835; 
x_835 = lean::cnstr_get(x_824, 0);
lean::inc(x_835);
lean::dec(x_824);
x_15 = x_835;
goto lbl_16;
}
}
else
{
obj* x_839; obj* x_841; obj* x_844; obj* x_845; obj* x_847; obj* x_848; obj* x_849; obj* x_850; obj* x_851; obj* x_853; obj* x_854; 
lean::dec(x_1);
x_839 = lean::cnstr_get(x_817, 0);
lean::inc(x_839);
x_841 = lean::cnstr_get(x_817, 1);
lean::inc(x_841);
lean::dec(x_817);
x_844 = lean::mk_nat_obj(0ul);
x_845 = l_List_lengthAux___main___rarg(x_10, x_844);
lean::dec(x_10);
x_847 = lean::box(0);
x_848 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_849 = l_Lean_KVMap_setNat(x_847, x_848, x_845);
x_850 = l_List_reverse___rarg(x_841);
x_851 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_839, x_850);
lean::dec(x_839);
x_853 = lean_expr_mk_mdata(x_849, x_851);
if (lean::is_scalar(x_816)) {
 x_854 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_854 = x_816;
}
lean::cnstr_set(x_854, 0, x_853);
lean::cnstr_set(x_854, 1, x_814);
x_15 = x_854;
goto lbl_16;
}
}
}
}
else
{
obj* x_858; obj* x_859; obj* x_863; obj* x_864; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_858 = l_Lean_Parser_stringLit_HasView;
x_859 = lean::cnstr_get(x_858, 0);
lean::inc(x_859);
lean::dec(x_858);
lean::inc(x_0);
x_863 = lean::apply_1(x_859, x_0);
x_864 = l_Lean_Parser_stringLit_View_value(x_863);
if (lean::obj_tag(x_864) == 0)
{
obj* x_865; 
x_865 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_865) == 0)
{
obj* x_868; obj* x_869; obj* x_870; 
lean::dec(x_2);
x_868 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_869 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_869, 0, x_868);
lean::cnstr_set(x_869, 1, x_3);
x_870 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_870, 0, x_869);
return x_870;
}
else
{
obj* x_871; obj* x_874; obj* x_877; obj* x_880; obj* x_881; obj* x_883; obj* x_884; obj* x_885; obj* x_886; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; obj* x_894; 
x_871 = lean::cnstr_get(x_865, 0);
lean::inc(x_871);
lean::dec(x_865);
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
x_891 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_892 = lean_expr_mk_mdata(x_890, x_891);
x_893 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_893, 0, x_892);
lean::cnstr_set(x_893, 1, x_3);
x_894 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_894, 0, x_893);
return x_894;
}
}
else
{
obj* x_895; obj* x_898; obj* x_899; obj* x_900; 
x_895 = lean::cnstr_get(x_864, 0);
lean::inc(x_895);
lean::dec(x_864);
x_898 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_898, 0, x_895);
x_899 = lean_expr_mk_lit(x_898);
x_900 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_900) == 0)
{
obj* x_903; obj* x_904; 
lean::dec(x_2);
x_903 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_903, 0, x_899);
lean::cnstr_set(x_903, 1, x_3);
x_904 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_904, 0, x_903);
return x_904;
}
else
{
obj* x_905; obj* x_908; obj* x_911; obj* x_914; obj* x_915; obj* x_917; obj* x_918; obj* x_919; obj* x_920; obj* x_923; obj* x_924; obj* x_925; obj* x_926; obj* x_927; 
x_905 = lean::cnstr_get(x_900, 0);
lean::inc(x_905);
lean::dec(x_900);
x_908 = lean::cnstr_get(x_2, 0);
lean::inc(x_908);
lean::dec(x_2);
x_911 = lean::cnstr_get(x_908, 2);
lean::inc(x_911);
lean::dec(x_908);
x_914 = l_Lean_FileMap_toPosition(x_911, x_905);
x_915 = lean::cnstr_get(x_914, 1);
lean::inc(x_915);
x_917 = lean::box(0);
x_918 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_919 = l_Lean_KVMap_setNat(x_917, x_918, x_915);
x_920 = lean::cnstr_get(x_914, 0);
lean::inc(x_920);
lean::dec(x_914);
x_923 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_924 = l_Lean_KVMap_setNat(x_919, x_923, x_920);
x_925 = lean_expr_mk_mdata(x_924, x_899);
x_926 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_926, 0, x_925);
lean::cnstr_set(x_926, 1, x_3);
x_927 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_927, 0, x_926);
return x_927;
}
}
}
}
else
{
obj* x_931; obj* x_932; obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_931 = l_Lean_Parser_number_HasView;
x_932 = lean::cnstr_get(x_931, 0);
lean::inc(x_932);
lean::dec(x_931);
lean::inc(x_0);
x_936 = lean::apply_1(x_932, x_0);
x_937 = l_Lean_Parser_number_View_toNat___main(x_936);
x_938 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_938, 0, x_937);
x_939 = lean_expr_mk_lit(x_938);
x_940 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_940) == 0)
{
obj* x_943; obj* x_944; 
lean::dec(x_2);
x_943 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_943, 0, x_939);
lean::cnstr_set(x_943, 1, x_3);
x_944 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_944, 0, x_943);
return x_944;
}
else
{
obj* x_945; obj* x_948; obj* x_951; obj* x_954; obj* x_955; obj* x_957; obj* x_958; obj* x_959; obj* x_960; obj* x_963; obj* x_964; obj* x_965; obj* x_966; obj* x_967; 
x_945 = lean::cnstr_get(x_940, 0);
lean::inc(x_945);
lean::dec(x_940);
x_948 = lean::cnstr_get(x_2, 0);
lean::inc(x_948);
lean::dec(x_2);
x_951 = lean::cnstr_get(x_948, 2);
lean::inc(x_951);
lean::dec(x_948);
x_954 = l_Lean_FileMap_toPosition(x_951, x_945);
x_955 = lean::cnstr_get(x_954, 1);
lean::inc(x_955);
x_957 = lean::box(0);
x_958 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_959 = l_Lean_KVMap_setNat(x_957, x_958, x_955);
x_960 = lean::cnstr_get(x_954, 0);
lean::inc(x_960);
lean::dec(x_954);
x_963 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_964 = l_Lean_KVMap_setNat(x_959, x_963, x_960);
x_965 = lean_expr_mk_mdata(x_964, x_939);
x_966 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_966, 0, x_965);
lean::cnstr_set(x_966, 1, x_3);
x_967 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_967, 0, x_966);
return x_967;
}
}
}
else
{
obj* x_970; obj* x_971; obj* x_975; obj* x_976; obj* x_980; 
lean::dec(x_8);
lean::dec(x_10);
x_970 = l_Lean_Parser_Term_borrowed_HasView;
x_971 = lean::cnstr_get(x_970, 0);
lean::inc(x_971);
lean::dec(x_970);
lean::inc(x_0);
x_975 = lean::apply_1(x_971, x_0);
x_976 = lean::cnstr_get(x_975, 1);
lean::inc(x_976);
lean::dec(x_975);
lean::inc(x_2);
x_980 = l_Lean_Elaborator_toPexpr___main(x_976, x_1, x_2, x_3);
if (lean::obj_tag(x_980) == 0)
{
obj* x_983; obj* x_985; obj* x_986; 
lean::dec(x_0);
lean::dec(x_2);
x_983 = lean::cnstr_get(x_980, 0);
if (lean::is_exclusive(x_980)) {
 x_985 = x_980;
} else {
 lean::inc(x_983);
 lean::dec(x_980);
 x_985 = lean::box(0);
}
if (lean::is_scalar(x_985)) {
 x_986 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_986 = x_985;
}
lean::cnstr_set(x_986, 0, x_983);
return x_986;
}
else
{
obj* x_987; obj* x_989; obj* x_990; obj* x_992; obj* x_994; obj* x_995; obj* x_996; obj* x_997; 
x_987 = lean::cnstr_get(x_980, 0);
if (lean::is_exclusive(x_980)) {
 lean::cnstr_set(x_980, 0, lean::box(0));
 x_989 = x_980;
} else {
 lean::inc(x_987);
 lean::dec(x_980);
 x_989 = lean::box(0);
}
x_990 = lean::cnstr_get(x_987, 0);
x_992 = lean::cnstr_get(x_987, 1);
if (lean::is_exclusive(x_987)) {
 lean::cnstr_set(x_987, 0, lean::box(0));
 lean::cnstr_set(x_987, 1, lean::box(0));
 x_994 = x_987;
} else {
 lean::inc(x_990);
 lean::inc(x_992);
 lean::dec(x_987);
 x_994 = lean::box(0);
}
x_995 = l_Lean_Elaborator_toPexpr___main___closed__31;
x_996 = l_Lean_Elaborator_Expr_mkAnnotation(x_995, x_990);
x_997 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_997) == 0)
{
obj* x_1000; obj* x_1001; 
lean::dec(x_2);
if (lean::is_scalar(x_994)) {
 x_1000 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1000 = x_994;
}
lean::cnstr_set(x_1000, 0, x_996);
lean::cnstr_set(x_1000, 1, x_992);
if (lean::is_scalar(x_989)) {
 x_1001 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1001 = x_989;
}
lean::cnstr_set(x_1001, 0, x_1000);
return x_1001;
}
else
{
obj* x_1002; obj* x_1005; obj* x_1008; obj* x_1011; obj* x_1012; obj* x_1014; obj* x_1015; obj* x_1016; obj* x_1017; obj* x_1020; obj* x_1021; obj* x_1022; obj* x_1023; obj* x_1024; 
x_1002 = lean::cnstr_get(x_997, 0);
lean::inc(x_1002);
lean::dec(x_997);
x_1005 = lean::cnstr_get(x_2, 0);
lean::inc(x_1005);
lean::dec(x_2);
x_1008 = lean::cnstr_get(x_1005, 2);
lean::inc(x_1008);
lean::dec(x_1005);
x_1011 = l_Lean_FileMap_toPosition(x_1008, x_1002);
x_1012 = lean::cnstr_get(x_1011, 1);
lean::inc(x_1012);
x_1014 = lean::box(0);
x_1015 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1016 = l_Lean_KVMap_setNat(x_1014, x_1015, x_1012);
x_1017 = lean::cnstr_get(x_1011, 0);
lean::inc(x_1017);
lean::dec(x_1011);
x_1020 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1021 = l_Lean_KVMap_setNat(x_1016, x_1020, x_1017);
x_1022 = lean_expr_mk_mdata(x_1021, x_996);
if (lean::is_scalar(x_994)) {
 x_1023 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1023 = x_994;
}
lean::cnstr_set(x_1023, 0, x_1022);
lean::cnstr_set(x_1023, 1, x_992);
if (lean::is_scalar(x_989)) {
 x_1024 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1024 = x_989;
}
lean::cnstr_set(x_1024, 0, x_1023);
return x_1024;
}
}
}
}
else
{
obj* x_1027; obj* x_1028; obj* x_1032; obj* x_1033; obj* x_1037; 
lean::dec(x_8);
lean::dec(x_10);
x_1027 = l_Lean_Parser_Term_inaccessible_HasView;
x_1028 = lean::cnstr_get(x_1027, 0);
lean::inc(x_1028);
lean::dec(x_1027);
lean::inc(x_0);
x_1032 = lean::apply_1(x_1028, x_0);
x_1033 = lean::cnstr_get(x_1032, 1);
lean::inc(x_1033);
lean::dec(x_1032);
lean::inc(x_2);
x_1037 = l_Lean_Elaborator_toPexpr___main(x_1033, x_1, x_2, x_3);
if (lean::obj_tag(x_1037) == 0)
{
obj* x_1040; obj* x_1042; obj* x_1043; 
lean::dec(x_0);
lean::dec(x_2);
x_1040 = lean::cnstr_get(x_1037, 0);
if (lean::is_exclusive(x_1037)) {
 x_1042 = x_1037;
} else {
 lean::inc(x_1040);
 lean::dec(x_1037);
 x_1042 = lean::box(0);
}
if (lean::is_scalar(x_1042)) {
 x_1043 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1043 = x_1042;
}
lean::cnstr_set(x_1043, 0, x_1040);
return x_1043;
}
else
{
obj* x_1044; obj* x_1046; obj* x_1047; obj* x_1049; obj* x_1051; obj* x_1052; obj* x_1053; obj* x_1054; 
x_1044 = lean::cnstr_get(x_1037, 0);
if (lean::is_exclusive(x_1037)) {
 lean::cnstr_set(x_1037, 0, lean::box(0));
 x_1046 = x_1037;
} else {
 lean::inc(x_1044);
 lean::dec(x_1037);
 x_1046 = lean::box(0);
}
x_1047 = lean::cnstr_get(x_1044, 0);
x_1049 = lean::cnstr_get(x_1044, 1);
if (lean::is_exclusive(x_1044)) {
 lean::cnstr_set(x_1044, 0, lean::box(0));
 lean::cnstr_set(x_1044, 1, lean::box(0));
 x_1051 = x_1044;
} else {
 lean::inc(x_1047);
 lean::inc(x_1049);
 lean::dec(x_1044);
 x_1051 = lean::box(0);
}
x_1052 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_1053 = l_Lean_Elaborator_Expr_mkAnnotation(x_1052, x_1047);
x_1054 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1054) == 0)
{
obj* x_1057; obj* x_1058; 
lean::dec(x_2);
if (lean::is_scalar(x_1051)) {
 x_1057 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1057 = x_1051;
}
lean::cnstr_set(x_1057, 0, x_1053);
lean::cnstr_set(x_1057, 1, x_1049);
if (lean::is_scalar(x_1046)) {
 x_1058 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1058 = x_1046;
}
lean::cnstr_set(x_1058, 0, x_1057);
return x_1058;
}
else
{
obj* x_1059; obj* x_1062; obj* x_1065; obj* x_1068; obj* x_1069; obj* x_1071; obj* x_1072; obj* x_1073; obj* x_1074; obj* x_1077; obj* x_1078; obj* x_1079; obj* x_1080; obj* x_1081; 
x_1059 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1059);
lean::dec(x_1054);
x_1062 = lean::cnstr_get(x_2, 0);
lean::inc(x_1062);
lean::dec(x_2);
x_1065 = lean::cnstr_get(x_1062, 2);
lean::inc(x_1065);
lean::dec(x_1062);
x_1068 = l_Lean_FileMap_toPosition(x_1065, x_1059);
x_1069 = lean::cnstr_get(x_1068, 1);
lean::inc(x_1069);
x_1071 = lean::box(0);
x_1072 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1073 = l_Lean_KVMap_setNat(x_1071, x_1072, x_1069);
x_1074 = lean::cnstr_get(x_1068, 0);
lean::inc(x_1074);
lean::dec(x_1068);
x_1077 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1078 = l_Lean_KVMap_setNat(x_1073, x_1077, x_1074);
x_1079 = lean_expr_mk_mdata(x_1078, x_1053);
if (lean::is_scalar(x_1051)) {
 x_1080 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1080 = x_1051;
}
lean::cnstr_set(x_1080, 0, x_1079);
lean::cnstr_set(x_1080, 1, x_1049);
if (lean::is_scalar(x_1046)) {
 x_1081 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1081 = x_1046;
}
lean::cnstr_set(x_1081, 0, x_1080);
return x_1081;
}
}
}
}
else
{
obj* x_1084; obj* x_1085; obj* x_1089; obj* x_1090; obj* x_1092; obj* x_1093; obj* x_1096; obj* x_1099; 
lean::dec(x_8);
lean::dec(x_10);
x_1084 = l_Lean_Parser_Term_explicit_HasView;
x_1085 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1085);
lean::dec(x_1084);
lean::inc(x_0);
x_1089 = lean::apply_1(x_1085, x_0);
x_1090 = lean::cnstr_get(x_1089, 0);
lean::inc(x_1090);
x_1092 = l_Lean_Parser_identUnivs_HasView;
x_1093 = lean::cnstr_get(x_1092, 1);
lean::inc(x_1093);
lean::dec(x_1092);
x_1096 = lean::cnstr_get(x_1089, 1);
lean::inc(x_1096);
lean::dec(x_1089);
x_1099 = lean::apply_1(x_1093, x_1096);
if (lean::obj_tag(x_1090) == 0)
{
obj* x_1102; 
lean::dec(x_1090);
lean::inc(x_2);
x_1102 = l_Lean_Elaborator_toPexpr___main(x_1099, x_1, x_2, x_3);
if (lean::obj_tag(x_1102) == 0)
{
obj* x_1105; obj* x_1107; obj* x_1108; 
lean::dec(x_0);
lean::dec(x_2);
x_1105 = lean::cnstr_get(x_1102, 0);
if (lean::is_exclusive(x_1102)) {
 x_1107 = x_1102;
} else {
 lean::inc(x_1105);
 lean::dec(x_1102);
 x_1107 = lean::box(0);
}
if (lean::is_scalar(x_1107)) {
 x_1108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1108 = x_1107;
}
lean::cnstr_set(x_1108, 0, x_1105);
return x_1108;
}
else
{
obj* x_1109; obj* x_1111; obj* x_1112; obj* x_1114; obj* x_1116; obj* x_1117; obj* x_1118; obj* x_1119; 
x_1109 = lean::cnstr_get(x_1102, 0);
if (lean::is_exclusive(x_1102)) {
 lean::cnstr_set(x_1102, 0, lean::box(0));
 x_1111 = x_1102;
} else {
 lean::inc(x_1109);
 lean::dec(x_1102);
 x_1111 = lean::box(0);
}
x_1112 = lean::cnstr_get(x_1109, 0);
x_1114 = lean::cnstr_get(x_1109, 1);
if (lean::is_exclusive(x_1109)) {
 lean::cnstr_set(x_1109, 0, lean::box(0));
 lean::cnstr_set(x_1109, 1, lean::box(0));
 x_1116 = x_1109;
} else {
 lean::inc(x_1112);
 lean::inc(x_1114);
 lean::dec(x_1109);
 x_1116 = lean::box(0);
}
x_1117 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_1118 = l_Lean_Elaborator_Expr_mkAnnotation(x_1117, x_1112);
x_1119 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1119) == 0)
{
obj* x_1122; obj* x_1123; 
lean::dec(x_2);
if (lean::is_scalar(x_1116)) {
 x_1122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1122 = x_1116;
}
lean::cnstr_set(x_1122, 0, x_1118);
lean::cnstr_set(x_1122, 1, x_1114);
if (lean::is_scalar(x_1111)) {
 x_1123 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1123 = x_1111;
}
lean::cnstr_set(x_1123, 0, x_1122);
return x_1123;
}
else
{
obj* x_1124; obj* x_1127; obj* x_1130; obj* x_1133; obj* x_1134; obj* x_1136; obj* x_1137; obj* x_1138; obj* x_1139; obj* x_1142; obj* x_1143; obj* x_1144; obj* x_1145; obj* x_1146; 
x_1124 = lean::cnstr_get(x_1119, 0);
lean::inc(x_1124);
lean::dec(x_1119);
x_1127 = lean::cnstr_get(x_2, 0);
lean::inc(x_1127);
lean::dec(x_2);
x_1130 = lean::cnstr_get(x_1127, 2);
lean::inc(x_1130);
lean::dec(x_1127);
x_1133 = l_Lean_FileMap_toPosition(x_1130, x_1124);
x_1134 = lean::cnstr_get(x_1133, 1);
lean::inc(x_1134);
x_1136 = lean::box(0);
x_1137 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1138 = l_Lean_KVMap_setNat(x_1136, x_1137, x_1134);
x_1139 = lean::cnstr_get(x_1133, 0);
lean::inc(x_1139);
lean::dec(x_1133);
x_1142 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1143 = l_Lean_KVMap_setNat(x_1138, x_1142, x_1139);
x_1144 = lean_expr_mk_mdata(x_1143, x_1118);
if (lean::is_scalar(x_1116)) {
 x_1145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1145 = x_1116;
}
lean::cnstr_set(x_1145, 0, x_1144);
lean::cnstr_set(x_1145, 1, x_1114);
if (lean::is_scalar(x_1111)) {
 x_1146 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1146 = x_1111;
}
lean::cnstr_set(x_1146, 0, x_1145);
return x_1146;
}
}
}
else
{
obj* x_1149; 
lean::dec(x_1090);
lean::inc(x_2);
x_1149 = l_Lean_Elaborator_toPexpr___main(x_1099, x_1, x_2, x_3);
if (lean::obj_tag(x_1149) == 0)
{
obj* x_1152; obj* x_1154; obj* x_1155; 
lean::dec(x_0);
lean::dec(x_2);
x_1152 = lean::cnstr_get(x_1149, 0);
if (lean::is_exclusive(x_1149)) {
 x_1154 = x_1149;
} else {
 lean::inc(x_1152);
 lean::dec(x_1149);
 x_1154 = lean::box(0);
}
if (lean::is_scalar(x_1154)) {
 x_1155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1155 = x_1154;
}
lean::cnstr_set(x_1155, 0, x_1152);
return x_1155;
}
else
{
obj* x_1156; obj* x_1158; obj* x_1159; obj* x_1161; obj* x_1163; obj* x_1164; obj* x_1165; obj* x_1166; 
x_1156 = lean::cnstr_get(x_1149, 0);
if (lean::is_exclusive(x_1149)) {
 lean::cnstr_set(x_1149, 0, lean::box(0));
 x_1158 = x_1149;
} else {
 lean::inc(x_1156);
 lean::dec(x_1149);
 x_1158 = lean::box(0);
}
x_1159 = lean::cnstr_get(x_1156, 0);
x_1161 = lean::cnstr_get(x_1156, 1);
if (lean::is_exclusive(x_1156)) {
 lean::cnstr_set(x_1156, 0, lean::box(0));
 lean::cnstr_set(x_1156, 1, lean::box(0));
 x_1163 = x_1156;
} else {
 lean::inc(x_1159);
 lean::inc(x_1161);
 lean::dec(x_1156);
 x_1163 = lean::box(0);
}
x_1164 = l_Lean_Elaborator_toPexpr___main___closed__33;
x_1165 = l_Lean_Elaborator_Expr_mkAnnotation(x_1164, x_1159);
x_1166 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1166) == 0)
{
obj* x_1169; obj* x_1170; 
lean::dec(x_2);
if (lean::is_scalar(x_1163)) {
 x_1169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1169 = x_1163;
}
lean::cnstr_set(x_1169, 0, x_1165);
lean::cnstr_set(x_1169, 1, x_1161);
if (lean::is_scalar(x_1158)) {
 x_1170 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1170 = x_1158;
}
lean::cnstr_set(x_1170, 0, x_1169);
return x_1170;
}
else
{
obj* x_1171; obj* x_1174; obj* x_1177; obj* x_1180; obj* x_1181; obj* x_1183; obj* x_1184; obj* x_1185; obj* x_1186; obj* x_1189; obj* x_1190; obj* x_1191; obj* x_1192; obj* x_1193; 
x_1171 = lean::cnstr_get(x_1166, 0);
lean::inc(x_1171);
lean::dec(x_1166);
x_1174 = lean::cnstr_get(x_2, 0);
lean::inc(x_1174);
lean::dec(x_2);
x_1177 = lean::cnstr_get(x_1174, 2);
lean::inc(x_1177);
lean::dec(x_1174);
x_1180 = l_Lean_FileMap_toPosition(x_1177, x_1171);
x_1181 = lean::cnstr_get(x_1180, 1);
lean::inc(x_1181);
x_1183 = lean::box(0);
x_1184 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1185 = l_Lean_KVMap_setNat(x_1183, x_1184, x_1181);
x_1186 = lean::cnstr_get(x_1180, 0);
lean::inc(x_1186);
lean::dec(x_1180);
x_1189 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1190 = l_Lean_KVMap_setNat(x_1185, x_1189, x_1186);
x_1191 = lean_expr_mk_mdata(x_1190, x_1165);
if (lean::is_scalar(x_1163)) {
 x_1192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1192 = x_1163;
}
lean::cnstr_set(x_1192, 0, x_1191);
lean::cnstr_set(x_1192, 1, x_1161);
if (lean::is_scalar(x_1158)) {
 x_1193 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1193 = x_1158;
}
lean::cnstr_set(x_1193, 0, x_1192);
return x_1193;
}
}
}
}
}
else
{
obj* x_1196; obj* x_1197; obj* x_1201; obj* x_1202; 
lean::dec(x_8);
lean::dec(x_10);
x_1196 = l_Lean_Parser_Term_projection_HasView;
x_1197 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1197);
lean::dec(x_1196);
lean::inc(x_0);
x_1201 = lean::apply_1(x_1197, x_0);
x_1202 = lean::cnstr_get(x_1201, 2);
lean::inc(x_1202);
if (lean::obj_tag(x_1202) == 0)
{
obj* x_1204; obj* x_1207; obj* x_1211; 
x_1204 = lean::cnstr_get(x_1201, 0);
lean::inc(x_1204);
lean::dec(x_1201);
x_1207 = lean::cnstr_get(x_1202, 0);
lean::inc(x_1207);
lean::dec(x_1202);
lean::inc(x_2);
x_1211 = l_Lean_Elaborator_toPexpr___main(x_1204, x_1, x_2, x_3);
if (lean::obj_tag(x_1211) == 0)
{
obj* x_1215; obj* x_1217; obj* x_1218; 
lean::dec(x_1207);
lean::dec(x_0);
lean::dec(x_2);
x_1215 = lean::cnstr_get(x_1211, 0);
if (lean::is_exclusive(x_1211)) {
 x_1217 = x_1211;
} else {
 lean::inc(x_1215);
 lean::dec(x_1211);
 x_1217 = lean::box(0);
}
if (lean::is_scalar(x_1217)) {
 x_1218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1218 = x_1217;
}
lean::cnstr_set(x_1218, 0, x_1215);
return x_1218;
}
else
{
obj* x_1219; obj* x_1221; obj* x_1222; obj* x_1224; obj* x_1226; obj* x_1227; obj* x_1230; obj* x_1231; obj* x_1232; obj* x_1233; obj* x_1234; obj* x_1235; 
x_1219 = lean::cnstr_get(x_1211, 0);
if (lean::is_exclusive(x_1211)) {
 lean::cnstr_set(x_1211, 0, lean::box(0));
 x_1221 = x_1211;
} else {
 lean::inc(x_1219);
 lean::dec(x_1211);
 x_1221 = lean::box(0);
}
x_1222 = lean::cnstr_get(x_1219, 0);
x_1224 = lean::cnstr_get(x_1219, 1);
if (lean::is_exclusive(x_1219)) {
 lean::cnstr_set(x_1219, 0, lean::box(0));
 lean::cnstr_set(x_1219, 1, lean::box(0));
 x_1226 = x_1219;
} else {
 lean::inc(x_1222);
 lean::inc(x_1224);
 lean::dec(x_1219);
 x_1226 = lean::box(0);
}
x_1227 = lean::cnstr_get(x_1207, 2);
lean::inc(x_1227);
lean::dec(x_1207);
x_1230 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1230, 0, x_1227);
x_1231 = lean::box(0);
x_1232 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1233 = l_Lean_KVMap_insertCore___main(x_1231, x_1232, x_1230);
x_1234 = lean_expr_mk_mdata(x_1233, x_1222);
x_1235 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1235) == 0)
{
obj* x_1238; obj* x_1239; 
lean::dec(x_2);
if (lean::is_scalar(x_1226)) {
 x_1238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1238 = x_1226;
}
lean::cnstr_set(x_1238, 0, x_1234);
lean::cnstr_set(x_1238, 1, x_1224);
if (lean::is_scalar(x_1221)) {
 x_1239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1239 = x_1221;
}
lean::cnstr_set(x_1239, 0, x_1238);
return x_1239;
}
else
{
obj* x_1240; obj* x_1243; obj* x_1246; obj* x_1249; obj* x_1250; obj* x_1252; obj* x_1253; obj* x_1254; obj* x_1257; obj* x_1258; obj* x_1259; obj* x_1260; obj* x_1261; 
x_1240 = lean::cnstr_get(x_1235, 0);
lean::inc(x_1240);
lean::dec(x_1235);
x_1243 = lean::cnstr_get(x_2, 0);
lean::inc(x_1243);
lean::dec(x_2);
x_1246 = lean::cnstr_get(x_1243, 2);
lean::inc(x_1246);
lean::dec(x_1243);
x_1249 = l_Lean_FileMap_toPosition(x_1246, x_1240);
x_1250 = lean::cnstr_get(x_1249, 1);
lean::inc(x_1250);
x_1252 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1253 = l_Lean_KVMap_setNat(x_1231, x_1252, x_1250);
x_1254 = lean::cnstr_get(x_1249, 0);
lean::inc(x_1254);
lean::dec(x_1249);
x_1257 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1258 = l_Lean_KVMap_setNat(x_1253, x_1257, x_1254);
x_1259 = lean_expr_mk_mdata(x_1258, x_1234);
if (lean::is_scalar(x_1226)) {
 x_1260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1260 = x_1226;
}
lean::cnstr_set(x_1260, 0, x_1259);
lean::cnstr_set(x_1260, 1, x_1224);
if (lean::is_scalar(x_1221)) {
 x_1261 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1261 = x_1221;
}
lean::cnstr_set(x_1261, 0, x_1260);
return x_1261;
}
}
}
else
{
obj* x_1262; obj* x_1265; obj* x_1269; 
x_1262 = lean::cnstr_get(x_1201, 0);
lean::inc(x_1262);
lean::dec(x_1201);
x_1265 = lean::cnstr_get(x_1202, 0);
lean::inc(x_1265);
lean::dec(x_1202);
lean::inc(x_2);
x_1269 = l_Lean_Elaborator_toPexpr___main(x_1262, x_1, x_2, x_3);
if (lean::obj_tag(x_1269) == 0)
{
obj* x_1273; obj* x_1275; obj* x_1276; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1265);
x_1273 = lean::cnstr_get(x_1269, 0);
if (lean::is_exclusive(x_1269)) {
 x_1275 = x_1269;
} else {
 lean::inc(x_1273);
 lean::dec(x_1269);
 x_1275 = lean::box(0);
}
if (lean::is_scalar(x_1275)) {
 x_1276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1276 = x_1275;
}
lean::cnstr_set(x_1276, 0, x_1273);
return x_1276;
}
else
{
obj* x_1277; obj* x_1279; obj* x_1280; obj* x_1282; obj* x_1284; obj* x_1285; obj* x_1286; obj* x_1287; obj* x_1288; obj* x_1289; obj* x_1290; obj* x_1291; 
x_1277 = lean::cnstr_get(x_1269, 0);
if (lean::is_exclusive(x_1269)) {
 lean::cnstr_set(x_1269, 0, lean::box(0));
 x_1279 = x_1269;
} else {
 lean::inc(x_1277);
 lean::dec(x_1269);
 x_1279 = lean::box(0);
}
x_1280 = lean::cnstr_get(x_1277, 0);
x_1282 = lean::cnstr_get(x_1277, 1);
if (lean::is_exclusive(x_1277)) {
 lean::cnstr_set(x_1277, 0, lean::box(0));
 lean::cnstr_set(x_1277, 1, lean::box(0));
 x_1284 = x_1277;
} else {
 lean::inc(x_1280);
 lean::inc(x_1282);
 lean::dec(x_1277);
 x_1284 = lean::box(0);
}
x_1285 = l_Lean_Parser_number_View_toNat___main(x_1265);
x_1286 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1286, 0, x_1285);
x_1287 = lean::box(0);
x_1288 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1289 = l_Lean_KVMap_insertCore___main(x_1287, x_1288, x_1286);
x_1290 = lean_expr_mk_mdata(x_1289, x_1280);
x_1291 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1291) == 0)
{
obj* x_1294; obj* x_1295; 
lean::dec(x_2);
if (lean::is_scalar(x_1284)) {
 x_1294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1294 = x_1284;
}
lean::cnstr_set(x_1294, 0, x_1290);
lean::cnstr_set(x_1294, 1, x_1282);
if (lean::is_scalar(x_1279)) {
 x_1295 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1295 = x_1279;
}
lean::cnstr_set(x_1295, 0, x_1294);
return x_1295;
}
else
{
obj* x_1296; obj* x_1299; obj* x_1302; obj* x_1305; obj* x_1306; obj* x_1308; obj* x_1309; obj* x_1310; obj* x_1313; obj* x_1314; obj* x_1315; obj* x_1316; obj* x_1317; 
x_1296 = lean::cnstr_get(x_1291, 0);
lean::inc(x_1296);
lean::dec(x_1291);
x_1299 = lean::cnstr_get(x_2, 0);
lean::inc(x_1299);
lean::dec(x_2);
x_1302 = lean::cnstr_get(x_1299, 2);
lean::inc(x_1302);
lean::dec(x_1299);
x_1305 = l_Lean_FileMap_toPosition(x_1302, x_1296);
x_1306 = lean::cnstr_get(x_1305, 1);
lean::inc(x_1306);
x_1308 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1309 = l_Lean_KVMap_setNat(x_1287, x_1308, x_1306);
x_1310 = lean::cnstr_get(x_1305, 0);
lean::inc(x_1310);
lean::dec(x_1305);
x_1313 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1314 = l_Lean_KVMap_setNat(x_1309, x_1313, x_1310);
x_1315 = lean_expr_mk_mdata(x_1314, x_1290);
if (lean::is_scalar(x_1284)) {
 x_1316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1316 = x_1284;
}
lean::cnstr_set(x_1316, 0, x_1315);
lean::cnstr_set(x_1316, 1, x_1282);
if (lean::is_scalar(x_1279)) {
 x_1317 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1317 = x_1279;
}
lean::cnstr_set(x_1317, 0, x_1316);
return x_1317;
}
}
}
}
}
else
{
obj* x_1319; obj* x_1320; obj* x_1324; obj* x_1325; 
lean::dec(x_10);
x_1319 = l_Lean_Parser_Term_let_HasView;
x_1320 = lean::cnstr_get(x_1319, 0);
lean::inc(x_1320);
lean::dec(x_1319);
lean::inc(x_0);
x_1324 = lean::apply_1(x_1320, x_0);
x_1325 = lean::cnstr_get(x_1324, 1);
lean::inc(x_1325);
if (lean::obj_tag(x_1325) == 0)
{
obj* x_1327; obj* x_1330; 
x_1327 = lean::cnstr_get(x_1325, 0);
lean::inc(x_1327);
lean::dec(x_1325);
x_1330 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1330);
if (lean::obj_tag(x_1330) == 0)
{
obj* x_1332; 
x_1332 = lean::cnstr_get(x_1327, 2);
lean::inc(x_1332);
if (lean::obj_tag(x_1332) == 0)
{
obj* x_1337; obj* x_1338; obj* x_1340; 
lean::dec(x_1327);
lean::dec(x_1324);
lean::inc(x_0);
x_1337 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1337, 0, x_0);
x_1338 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1340 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1337, x_1338, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_1337);
if (lean::obj_tag(x_1340) == 0)
{
obj* x_1347; obj* x_1349; obj* x_1350; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1347 = lean::cnstr_get(x_1340, 0);
if (lean::is_exclusive(x_1340)) {
 x_1349 = x_1340;
} else {
 lean::inc(x_1347);
 lean::dec(x_1340);
 x_1349 = lean::box(0);
}
if (lean::is_scalar(x_1349)) {
 x_1350 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1350 = x_1349;
}
lean::cnstr_set(x_1350, 0, x_1347);
return x_1350;
}
else
{
obj* x_1351; 
x_1351 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1351);
lean::dec(x_1340);
x_15 = x_1351;
goto lbl_16;
}
}
else
{
obj* x_1354; obj* x_1357; obj* x_1360; obj* x_1365; 
x_1354 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1354);
lean::dec(x_1327);
x_1357 = lean::cnstr_get(x_1332, 0);
lean::inc(x_1357);
lean::dec(x_1332);
x_1360 = lean::cnstr_get(x_1357, 1);
lean::inc(x_1360);
lean::dec(x_1357);
lean::inc(x_2);
lean::inc(x_1);
x_1365 = l_Lean_Elaborator_toPexpr___main(x_1360, x_1, x_2, x_3);
if (lean::obj_tag(x_1365) == 0)
{
obj* x_1372; obj* x_1374; obj* x_1375; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1354);
lean::dec(x_1324);
x_1372 = lean::cnstr_get(x_1365, 0);
if (lean::is_exclusive(x_1365)) {
 x_1374 = x_1365;
} else {
 lean::inc(x_1372);
 lean::dec(x_1365);
 x_1374 = lean::box(0);
}
if (lean::is_scalar(x_1374)) {
 x_1375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1375 = x_1374;
}
lean::cnstr_set(x_1375, 0, x_1372);
return x_1375;
}
else
{
obj* x_1376; obj* x_1379; obj* x_1381; obj* x_1384; obj* x_1388; 
x_1376 = lean::cnstr_get(x_1365, 0);
lean::inc(x_1376);
lean::dec(x_1365);
x_1379 = lean::cnstr_get(x_1376, 0);
lean::inc(x_1379);
x_1381 = lean::cnstr_get(x_1376, 1);
lean::inc(x_1381);
lean::dec(x_1376);
x_1384 = lean::cnstr_get(x_1324, 3);
lean::inc(x_1384);
lean::inc(x_2);
lean::inc(x_1);
x_1388 = l_Lean_Elaborator_toPexpr___main(x_1384, x_1, x_2, x_1381);
if (lean::obj_tag(x_1388) == 0)
{
obj* x_1396; obj* x_1398; obj* x_1399; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1354);
lean::dec(x_1379);
lean::dec(x_1324);
x_1396 = lean::cnstr_get(x_1388, 0);
if (lean::is_exclusive(x_1388)) {
 x_1398 = x_1388;
} else {
 lean::inc(x_1396);
 lean::dec(x_1388);
 x_1398 = lean::box(0);
}
if (lean::is_scalar(x_1398)) {
 x_1399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1399 = x_1398;
}
lean::cnstr_set(x_1399, 0, x_1396);
return x_1399;
}
else
{
obj* x_1400; obj* x_1403; obj* x_1405; obj* x_1408; obj* x_1412; 
x_1400 = lean::cnstr_get(x_1388, 0);
lean::inc(x_1400);
lean::dec(x_1388);
x_1403 = lean::cnstr_get(x_1400, 0);
lean::inc(x_1403);
x_1405 = lean::cnstr_get(x_1400, 1);
lean::inc(x_1405);
lean::dec(x_1400);
x_1408 = lean::cnstr_get(x_1324, 5);
lean::inc(x_1408);
lean::dec(x_1324);
lean::inc(x_2);
x_1412 = l_Lean_Elaborator_toPexpr___main(x_1408, x_1, x_2, x_1405);
if (lean::obj_tag(x_1412) == 0)
{
obj* x_1419; obj* x_1421; obj* x_1422; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1354);
lean::dec(x_1379);
lean::dec(x_1403);
x_1419 = lean::cnstr_get(x_1412, 0);
if (lean::is_exclusive(x_1412)) {
 x_1421 = x_1412;
} else {
 lean::inc(x_1419);
 lean::dec(x_1412);
 x_1421 = lean::box(0);
}
if (lean::is_scalar(x_1421)) {
 x_1422 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1422 = x_1421;
}
lean::cnstr_set(x_1422, 0, x_1419);
return x_1422;
}
else
{
obj* x_1423; obj* x_1426; obj* x_1428; obj* x_1430; obj* x_1431; obj* x_1432; obj* x_1433; 
x_1423 = lean::cnstr_get(x_1412, 0);
lean::inc(x_1423);
lean::dec(x_1412);
x_1426 = lean::cnstr_get(x_1423, 0);
x_1428 = lean::cnstr_get(x_1423, 1);
if (lean::is_exclusive(x_1423)) {
 x_1430 = x_1423;
} else {
 lean::inc(x_1426);
 lean::inc(x_1428);
 lean::dec(x_1423);
 x_1430 = lean::box(0);
}
x_1431 = l_Lean_Elaborator_mangleIdent(x_1354);
x_1432 = lean_expr_mk_let(x_1431, x_1379, x_1403, x_1426);
if (lean::is_scalar(x_1430)) {
 x_1433 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1433 = x_1430;
}
lean::cnstr_set(x_1433, 0, x_1432);
lean::cnstr_set(x_1433, 1, x_1428);
x_15 = x_1433;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1438; obj* x_1439; obj* x_1441; 
lean::dec(x_1330);
lean::dec(x_1327);
lean::dec(x_1324);
lean::inc(x_0);
x_1438 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1438, 0, x_0);
x_1439 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1441 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1438, x_1439, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_1438);
if (lean::obj_tag(x_1441) == 0)
{
obj* x_1448; obj* x_1450; obj* x_1451; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1448 = lean::cnstr_get(x_1441, 0);
if (lean::is_exclusive(x_1441)) {
 x_1450 = x_1441;
} else {
 lean::inc(x_1448);
 lean::dec(x_1441);
 x_1450 = lean::box(0);
}
if (lean::is_scalar(x_1450)) {
 x_1451 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1451 = x_1450;
}
lean::cnstr_set(x_1451, 0, x_1448);
return x_1451;
}
else
{
obj* x_1452; 
x_1452 = lean::cnstr_get(x_1441, 0);
lean::inc(x_1452);
lean::dec(x_1441);
x_15 = x_1452;
goto lbl_16;
}
}
}
else
{
obj* x_1458; obj* x_1459; obj* x_1461; 
lean::dec(x_1324);
lean::dec(x_1325);
lean::inc(x_0);
x_1458 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1458, 0, x_0);
x_1459 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1461 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1458, x_1459, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_1458);
if (lean::obj_tag(x_1461) == 0)
{
obj* x_1468; obj* x_1470; obj* x_1471; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1468 = lean::cnstr_get(x_1461, 0);
if (lean::is_exclusive(x_1461)) {
 x_1470 = x_1461;
} else {
 lean::inc(x_1468);
 lean::dec(x_1461);
 x_1470 = lean::box(0);
}
if (lean::is_scalar(x_1470)) {
 x_1471 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1471 = x_1470;
}
lean::cnstr_set(x_1471, 0, x_1468);
return x_1471;
}
else
{
obj* x_1472; 
x_1472 = lean::cnstr_get(x_1461, 0);
lean::inc(x_1472);
lean::dec(x_1461);
x_15 = x_1472;
goto lbl_16;
}
}
}
}
else
{
obj* x_1477; obj* x_1478; obj* x_1482; obj* x_1483; obj* x_1487; 
lean::dec(x_8);
lean::dec(x_10);
x_1477 = l_Lean_Parser_Term_show_HasView;
x_1478 = lean::cnstr_get(x_1477, 0);
lean::inc(x_1478);
lean::dec(x_1477);
lean::inc(x_0);
x_1482 = lean::apply_1(x_1478, x_0);
x_1483 = lean::cnstr_get(x_1482, 1);
lean::inc(x_1483);
lean::inc(x_2);
lean::inc(x_1);
x_1487 = l_Lean_Elaborator_toPexpr___main(x_1483, x_1, x_2, x_3);
if (lean::obj_tag(x_1487) == 0)
{
obj* x_1492; obj* x_1494; obj* x_1495; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1482);
x_1492 = lean::cnstr_get(x_1487, 0);
if (lean::is_exclusive(x_1487)) {
 x_1494 = x_1487;
} else {
 lean::inc(x_1492);
 lean::dec(x_1487);
 x_1494 = lean::box(0);
}
if (lean::is_scalar(x_1494)) {
 x_1495 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1495 = x_1494;
}
lean::cnstr_set(x_1495, 0, x_1492);
return x_1495;
}
else
{
obj* x_1496; obj* x_1499; obj* x_1501; obj* x_1504; obj* x_1507; obj* x_1511; 
x_1496 = lean::cnstr_get(x_1487, 0);
lean::inc(x_1496);
lean::dec(x_1487);
x_1499 = lean::cnstr_get(x_1496, 0);
lean::inc(x_1499);
x_1501 = lean::cnstr_get(x_1496, 1);
lean::inc(x_1501);
lean::dec(x_1496);
x_1504 = lean::cnstr_get(x_1482, 3);
lean::inc(x_1504);
lean::dec(x_1482);
x_1507 = lean::cnstr_get(x_1504, 1);
lean::inc(x_1507);
lean::dec(x_1504);
lean::inc(x_2);
x_1511 = l_Lean_Elaborator_toPexpr___main(x_1507, x_1, x_2, x_1501);
if (lean::obj_tag(x_1511) == 0)
{
obj* x_1515; obj* x_1517; obj* x_1518; 
lean::dec(x_1499);
lean::dec(x_0);
lean::dec(x_2);
x_1515 = lean::cnstr_get(x_1511, 0);
if (lean::is_exclusive(x_1511)) {
 x_1517 = x_1511;
} else {
 lean::inc(x_1515);
 lean::dec(x_1511);
 x_1517 = lean::box(0);
}
if (lean::is_scalar(x_1517)) {
 x_1518 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1518 = x_1517;
}
lean::cnstr_set(x_1518, 0, x_1515);
return x_1518;
}
else
{
obj* x_1519; obj* x_1521; obj* x_1522; obj* x_1524; obj* x_1526; obj* x_1527; uint8 x_1528; obj* x_1529; obj* x_1530; obj* x_1531; obj* x_1532; obj* x_1533; obj* x_1534; 
x_1519 = lean::cnstr_get(x_1511, 0);
if (lean::is_exclusive(x_1511)) {
 lean::cnstr_set(x_1511, 0, lean::box(0));
 x_1521 = x_1511;
} else {
 lean::inc(x_1519);
 lean::dec(x_1511);
 x_1521 = lean::box(0);
}
x_1522 = lean::cnstr_get(x_1519, 0);
x_1524 = lean::cnstr_get(x_1519, 1);
if (lean::is_exclusive(x_1519)) {
 lean::cnstr_set(x_1519, 0, lean::box(0));
 lean::cnstr_set(x_1519, 1, lean::box(0));
 x_1526 = x_1519;
} else {
 lean::inc(x_1522);
 lean::inc(x_1524);
 lean::dec(x_1519);
 x_1526 = lean::box(0);
}
x_1527 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1528 = 0;
x_1529 = l_Lean_Elaborator_toPexpr___main___closed__37;
x_1530 = lean_expr_mk_lambda(x_1527, x_1528, x_1499, x_1529);
x_1531 = lean_expr_mk_app(x_1530, x_1522);
x_1532 = l_Lean_Elaborator_toPexpr___main___closed__38;
x_1533 = l_Lean_Elaborator_Expr_mkAnnotation(x_1532, x_1531);
x_1534 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1534) == 0)
{
obj* x_1537; obj* x_1538; 
lean::dec(x_2);
if (lean::is_scalar(x_1526)) {
 x_1537 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1537 = x_1526;
}
lean::cnstr_set(x_1537, 0, x_1533);
lean::cnstr_set(x_1537, 1, x_1524);
if (lean::is_scalar(x_1521)) {
 x_1538 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1538 = x_1521;
}
lean::cnstr_set(x_1538, 0, x_1537);
return x_1538;
}
else
{
obj* x_1539; obj* x_1542; obj* x_1545; obj* x_1548; obj* x_1549; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1554; obj* x_1557; obj* x_1558; obj* x_1559; obj* x_1560; obj* x_1561; 
x_1539 = lean::cnstr_get(x_1534, 0);
lean::inc(x_1539);
lean::dec(x_1534);
x_1542 = lean::cnstr_get(x_2, 0);
lean::inc(x_1542);
lean::dec(x_2);
x_1545 = lean::cnstr_get(x_1542, 2);
lean::inc(x_1545);
lean::dec(x_1542);
x_1548 = l_Lean_FileMap_toPosition(x_1545, x_1539);
x_1549 = lean::cnstr_get(x_1548, 1);
lean::inc(x_1549);
x_1551 = lean::box(0);
x_1552 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1553 = l_Lean_KVMap_setNat(x_1551, x_1552, x_1549);
x_1554 = lean::cnstr_get(x_1548, 0);
lean::inc(x_1554);
lean::dec(x_1548);
x_1557 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1558 = l_Lean_KVMap_setNat(x_1553, x_1557, x_1554);
x_1559 = lean_expr_mk_mdata(x_1558, x_1533);
if (lean::is_scalar(x_1526)) {
 x_1560 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1560 = x_1526;
}
lean::cnstr_set(x_1560, 0, x_1559);
lean::cnstr_set(x_1560, 1, x_1524);
if (lean::is_scalar(x_1521)) {
 x_1561 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1561 = x_1521;
}
lean::cnstr_set(x_1561, 0, x_1560);
return x_1561;
}
}
}
}
}
else
{
obj* x_1563; obj* x_1564; obj* x_1568; obj* x_1569; 
lean::dec(x_10);
x_1563 = l_Lean_Parser_Term_have_HasView;
x_1564 = lean::cnstr_get(x_1563, 0);
lean::inc(x_1564);
lean::dec(x_1563);
lean::inc(x_0);
x_1568 = lean::apply_1(x_1564, x_0);
x_1569 = lean::cnstr_get(x_1568, 1);
lean::inc(x_1569);
if (lean::obj_tag(x_1569) == 0)
{
obj* x_1571; obj* x_1573; obj* x_1577; 
x_1571 = lean::cnstr_get(x_1568, 2);
lean::inc(x_1571);
x_1573 = lean::cnstr_get(x_1568, 5);
lean::inc(x_1573);
lean::inc(x_2);
lean::inc(x_1);
x_1577 = l_Lean_Elaborator_toPexpr___main(x_1571, x_1, x_2, x_3);
if (lean::obj_tag(x_1577) == 0)
{
obj* x_1584; obj* x_1586; obj* x_1587; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1568);
lean::dec(x_1573);
x_1584 = lean::cnstr_get(x_1577, 0);
if (lean::is_exclusive(x_1577)) {
 x_1586 = x_1577;
} else {
 lean::inc(x_1584);
 lean::dec(x_1577);
 x_1586 = lean::box(0);
}
if (lean::is_scalar(x_1586)) {
 x_1587 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1587 = x_1586;
}
lean::cnstr_set(x_1587, 0, x_1584);
return x_1587;
}
else
{
obj* x_1588; obj* x_1591; obj* x_1593; obj* x_1598; 
x_1588 = lean::cnstr_get(x_1577, 0);
lean::inc(x_1588);
lean::dec(x_1577);
x_1591 = lean::cnstr_get(x_1588, 0);
lean::inc(x_1591);
x_1593 = lean::cnstr_get(x_1588, 1);
lean::inc(x_1593);
lean::dec(x_1588);
lean::inc(x_2);
lean::inc(x_1);
x_1598 = l_Lean_Elaborator_toPexpr___main(x_1573, x_1, x_2, x_1593);
if (lean::obj_tag(x_1598) == 0)
{
obj* x_1605; obj* x_1607; obj* x_1608; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1568);
lean::dec(x_1591);
x_1605 = lean::cnstr_get(x_1598, 0);
if (lean::is_exclusive(x_1598)) {
 x_1607 = x_1598;
} else {
 lean::inc(x_1605);
 lean::dec(x_1598);
 x_1607 = lean::box(0);
}
if (lean::is_scalar(x_1607)) {
 x_1608 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1608 = x_1607;
}
lean::cnstr_set(x_1608, 0, x_1605);
return x_1608;
}
else
{
obj* x_1609; obj* x_1612; obj* x_1614; obj* x_1617; uint8 x_1618; obj* x_1619; obj* x_1620; 
x_1609 = lean::cnstr_get(x_1598, 0);
lean::inc(x_1609);
lean::dec(x_1598);
x_1612 = lean::cnstr_get(x_1609, 0);
lean::inc(x_1612);
x_1614 = lean::cnstr_get(x_1609, 1);
lean::inc(x_1614);
lean::dec(x_1609);
x_1617 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1618 = 0;
x_1619 = lean_expr_mk_lambda(x_1617, x_1618, x_1591, x_1612);
x_1620 = lean::cnstr_get(x_1568, 3);
lean::inc(x_1620);
lean::dec(x_1568);
if (lean::obj_tag(x_1620) == 0)
{
obj* x_1623; obj* x_1626; obj* x_1630; 
x_1623 = lean::cnstr_get(x_1620, 0);
lean::inc(x_1623);
lean::dec(x_1620);
x_1626 = lean::cnstr_get(x_1623, 1);
lean::inc(x_1626);
lean::dec(x_1623);
lean::inc(x_2);
x_1630 = l_Lean_Elaborator_toPexpr___main(x_1626, x_1, x_2, x_1614);
if (lean::obj_tag(x_1630) == 0)
{
obj* x_1635; obj* x_1637; obj* x_1638; 
lean::dec(x_1619);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1635 = lean::cnstr_get(x_1630, 0);
if (lean::is_exclusive(x_1630)) {
 x_1637 = x_1630;
} else {
 lean::inc(x_1635);
 lean::dec(x_1630);
 x_1637 = lean::box(0);
}
if (lean::is_scalar(x_1637)) {
 x_1638 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1638 = x_1637;
}
lean::cnstr_set(x_1638, 0, x_1635);
return x_1638;
}
else
{
obj* x_1639; obj* x_1642; obj* x_1644; obj* x_1646; obj* x_1647; obj* x_1648; obj* x_1649; obj* x_1650; 
x_1639 = lean::cnstr_get(x_1630, 0);
lean::inc(x_1639);
lean::dec(x_1630);
x_1642 = lean::cnstr_get(x_1639, 0);
x_1644 = lean::cnstr_get(x_1639, 1);
if (lean::is_exclusive(x_1639)) {
 x_1646 = x_1639;
} else {
 lean::inc(x_1642);
 lean::inc(x_1644);
 lean::dec(x_1639);
 x_1646 = lean::box(0);
}
x_1647 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1648 = l_Lean_Elaborator_Expr_mkAnnotation(x_1647, x_1619);
x_1649 = lean_expr_mk_app(x_1648, x_1642);
if (lean::is_scalar(x_1646)) {
 x_1650 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1650 = x_1646;
}
lean::cnstr_set(x_1650, 0, x_1649);
lean::cnstr_set(x_1650, 1, x_1644);
x_15 = x_1650;
goto lbl_16;
}
}
else
{
obj* x_1651; obj* x_1654; obj* x_1657; obj* x_1661; 
x_1651 = lean::cnstr_get(x_1620, 0);
lean::inc(x_1651);
lean::dec(x_1620);
x_1654 = lean::cnstr_get(x_1651, 1);
lean::inc(x_1654);
lean::dec(x_1651);
x_1657 = lean::cnstr_get(x_1654, 1);
lean::inc(x_1657);
lean::dec(x_1654);
lean::inc(x_2);
x_1661 = l_Lean_Elaborator_toPexpr___main(x_1657, x_1, x_2, x_1614);
if (lean::obj_tag(x_1661) == 0)
{
obj* x_1666; obj* x_1668; obj* x_1669; 
lean::dec(x_1619);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1666 = lean::cnstr_get(x_1661, 0);
if (lean::is_exclusive(x_1661)) {
 x_1668 = x_1661;
} else {
 lean::inc(x_1666);
 lean::dec(x_1661);
 x_1668 = lean::box(0);
}
if (lean::is_scalar(x_1668)) {
 x_1669 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1669 = x_1668;
}
lean::cnstr_set(x_1669, 0, x_1666);
return x_1669;
}
else
{
obj* x_1670; obj* x_1673; obj* x_1675; obj* x_1677; obj* x_1678; obj* x_1679; obj* x_1680; obj* x_1681; 
x_1670 = lean::cnstr_get(x_1661, 0);
lean::inc(x_1670);
lean::dec(x_1661);
x_1673 = lean::cnstr_get(x_1670, 0);
x_1675 = lean::cnstr_get(x_1670, 1);
if (lean::is_exclusive(x_1670)) {
 x_1677 = x_1670;
} else {
 lean::inc(x_1673);
 lean::inc(x_1675);
 lean::dec(x_1670);
 x_1677 = lean::box(0);
}
x_1678 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1679 = l_Lean_Elaborator_Expr_mkAnnotation(x_1678, x_1619);
x_1680 = lean_expr_mk_app(x_1679, x_1673);
if (lean::is_scalar(x_1677)) {
 x_1681 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1681 = x_1677;
}
lean::cnstr_set(x_1681, 0, x_1680);
lean::cnstr_set(x_1681, 1, x_1675);
x_15 = x_1681;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1682; obj* x_1684; obj* x_1686; obj* x_1691; 
x_1682 = lean::cnstr_get(x_1568, 2);
lean::inc(x_1682);
x_1684 = lean::cnstr_get(x_1568, 5);
lean::inc(x_1684);
x_1686 = lean::cnstr_get(x_1569, 0);
lean::inc(x_1686);
lean::dec(x_1569);
lean::inc(x_2);
lean::inc(x_1);
x_1691 = l_Lean_Elaborator_toPexpr___main(x_1682, x_1, x_2, x_3);
if (lean::obj_tag(x_1691) == 0)
{
obj* x_1699; obj* x_1701; obj* x_1702; 
lean::dec(x_1686);
lean::dec(x_1684);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1568);
x_1699 = lean::cnstr_get(x_1691, 0);
if (lean::is_exclusive(x_1691)) {
 x_1701 = x_1691;
} else {
 lean::inc(x_1699);
 lean::dec(x_1691);
 x_1701 = lean::box(0);
}
if (lean::is_scalar(x_1701)) {
 x_1702 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1702 = x_1701;
}
lean::cnstr_set(x_1702, 0, x_1699);
return x_1702;
}
else
{
obj* x_1703; obj* x_1706; obj* x_1708; obj* x_1713; 
x_1703 = lean::cnstr_get(x_1691, 0);
lean::inc(x_1703);
lean::dec(x_1691);
x_1706 = lean::cnstr_get(x_1703, 0);
lean::inc(x_1706);
x_1708 = lean::cnstr_get(x_1703, 1);
lean::inc(x_1708);
lean::dec(x_1703);
lean::inc(x_2);
lean::inc(x_1);
x_1713 = l_Lean_Elaborator_toPexpr___main(x_1684, x_1, x_2, x_1708);
if (lean::obj_tag(x_1713) == 0)
{
obj* x_1721; obj* x_1723; obj* x_1724; 
lean::dec(x_1686);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1568);
lean::dec(x_1706);
x_1721 = lean::cnstr_get(x_1713, 0);
if (lean::is_exclusive(x_1713)) {
 x_1723 = x_1713;
} else {
 lean::inc(x_1721);
 lean::dec(x_1713);
 x_1723 = lean::box(0);
}
if (lean::is_scalar(x_1723)) {
 x_1724 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1724 = x_1723;
}
lean::cnstr_set(x_1724, 0, x_1721);
return x_1724;
}
else
{
obj* x_1725; obj* x_1728; obj* x_1730; obj* x_1733; obj* x_1736; uint8 x_1737; obj* x_1738; obj* x_1739; 
x_1725 = lean::cnstr_get(x_1713, 0);
lean::inc(x_1725);
lean::dec(x_1713);
x_1728 = lean::cnstr_get(x_1725, 0);
lean::inc(x_1728);
x_1730 = lean::cnstr_get(x_1725, 1);
lean::inc(x_1730);
lean::dec(x_1725);
x_1733 = lean::cnstr_get(x_1686, 0);
lean::inc(x_1733);
lean::dec(x_1686);
x_1736 = l_Lean_Elaborator_mangleIdent(x_1733);
x_1737 = 0;
x_1738 = lean_expr_mk_lambda(x_1736, x_1737, x_1706, x_1728);
x_1739 = lean::cnstr_get(x_1568, 3);
lean::inc(x_1739);
lean::dec(x_1568);
if (lean::obj_tag(x_1739) == 0)
{
obj* x_1742; obj* x_1745; obj* x_1749; 
x_1742 = lean::cnstr_get(x_1739, 0);
lean::inc(x_1742);
lean::dec(x_1739);
x_1745 = lean::cnstr_get(x_1742, 1);
lean::inc(x_1745);
lean::dec(x_1742);
lean::inc(x_2);
x_1749 = l_Lean_Elaborator_toPexpr___main(x_1745, x_1, x_2, x_1730);
if (lean::obj_tag(x_1749) == 0)
{
obj* x_1754; obj* x_1756; obj* x_1757; 
lean::dec(x_1738);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1754 = lean::cnstr_get(x_1749, 0);
if (lean::is_exclusive(x_1749)) {
 x_1756 = x_1749;
} else {
 lean::inc(x_1754);
 lean::dec(x_1749);
 x_1756 = lean::box(0);
}
if (lean::is_scalar(x_1756)) {
 x_1757 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1757 = x_1756;
}
lean::cnstr_set(x_1757, 0, x_1754);
return x_1757;
}
else
{
obj* x_1758; obj* x_1761; obj* x_1763; obj* x_1765; obj* x_1766; obj* x_1767; obj* x_1768; obj* x_1769; 
x_1758 = lean::cnstr_get(x_1749, 0);
lean::inc(x_1758);
lean::dec(x_1749);
x_1761 = lean::cnstr_get(x_1758, 0);
x_1763 = lean::cnstr_get(x_1758, 1);
if (lean::is_exclusive(x_1758)) {
 x_1765 = x_1758;
} else {
 lean::inc(x_1761);
 lean::inc(x_1763);
 lean::dec(x_1758);
 x_1765 = lean::box(0);
}
x_1766 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1767 = l_Lean_Elaborator_Expr_mkAnnotation(x_1766, x_1738);
x_1768 = lean_expr_mk_app(x_1767, x_1761);
if (lean::is_scalar(x_1765)) {
 x_1769 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1769 = x_1765;
}
lean::cnstr_set(x_1769, 0, x_1768);
lean::cnstr_set(x_1769, 1, x_1763);
x_15 = x_1769;
goto lbl_16;
}
}
else
{
obj* x_1770; obj* x_1773; obj* x_1776; obj* x_1780; 
x_1770 = lean::cnstr_get(x_1739, 0);
lean::inc(x_1770);
lean::dec(x_1739);
x_1773 = lean::cnstr_get(x_1770, 1);
lean::inc(x_1773);
lean::dec(x_1770);
x_1776 = lean::cnstr_get(x_1773, 1);
lean::inc(x_1776);
lean::dec(x_1773);
lean::inc(x_2);
x_1780 = l_Lean_Elaborator_toPexpr___main(x_1776, x_1, x_2, x_1730);
if (lean::obj_tag(x_1780) == 0)
{
obj* x_1785; obj* x_1787; obj* x_1788; 
lean::dec(x_1738);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1785 = lean::cnstr_get(x_1780, 0);
if (lean::is_exclusive(x_1780)) {
 x_1787 = x_1780;
} else {
 lean::inc(x_1785);
 lean::dec(x_1780);
 x_1787 = lean::box(0);
}
if (lean::is_scalar(x_1787)) {
 x_1788 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1788 = x_1787;
}
lean::cnstr_set(x_1788, 0, x_1785);
return x_1788;
}
else
{
obj* x_1789; obj* x_1792; obj* x_1794; obj* x_1796; obj* x_1797; obj* x_1798; obj* x_1799; obj* x_1800; 
x_1789 = lean::cnstr_get(x_1780, 0);
lean::inc(x_1789);
lean::dec(x_1780);
x_1792 = lean::cnstr_get(x_1789, 0);
x_1794 = lean::cnstr_get(x_1789, 1);
if (lean::is_exclusive(x_1789)) {
 x_1796 = x_1789;
} else {
 lean::inc(x_1792);
 lean::inc(x_1794);
 lean::dec(x_1789);
 x_1796 = lean::box(0);
}
x_1797 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1798 = l_Lean_Elaborator_Expr_mkAnnotation(x_1797, x_1738);
x_1799 = lean_expr_mk_app(x_1798, x_1792);
if (lean::is_scalar(x_1796)) {
 x_1800 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1800 = x_1796;
}
lean::cnstr_set(x_1800, 0, x_1799);
lean::cnstr_set(x_1800, 1, x_1794);
x_15 = x_1800;
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
obj* x_1804; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_1804 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1804) == 0)
{
obj* x_1807; obj* x_1808; obj* x_1809; 
lean::dec(x_2);
x_1807 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1808 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1808, 0, x_1807);
lean::cnstr_set(x_1808, 1, x_3);
x_1809 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1809, 0, x_1808);
return x_1809;
}
else
{
obj* x_1810; obj* x_1813; obj* x_1816; obj* x_1819; obj* x_1820; obj* x_1822; obj* x_1823; obj* x_1824; obj* x_1825; obj* x_1828; obj* x_1829; obj* x_1830; obj* x_1831; obj* x_1832; obj* x_1833; 
x_1810 = lean::cnstr_get(x_1804, 0);
lean::inc(x_1810);
lean::dec(x_1804);
x_1813 = lean::cnstr_get(x_2, 0);
lean::inc(x_1813);
lean::dec(x_2);
x_1816 = lean::cnstr_get(x_1813, 2);
lean::inc(x_1816);
lean::dec(x_1813);
x_1819 = l_Lean_FileMap_toPosition(x_1816, x_1810);
x_1820 = lean::cnstr_get(x_1819, 1);
lean::inc(x_1820);
x_1822 = lean::box(0);
x_1823 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1824 = l_Lean_KVMap_setNat(x_1822, x_1823, x_1820);
x_1825 = lean::cnstr_get(x_1819, 0);
lean::inc(x_1825);
lean::dec(x_1819);
x_1828 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1829 = l_Lean_KVMap_setNat(x_1824, x_1828, x_1825);
x_1830 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1831 = lean_expr_mk_mdata(x_1829, x_1830);
x_1832 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1832, 0, x_1831);
lean::cnstr_set(x_1832, 1, x_3);
x_1833 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1833, 0, x_1832);
return x_1833;
}
}
}
else
{
obj* x_1836; obj* x_1837; obj* x_1841; obj* x_1842; obj* x_1845; obj* x_1846; obj* x_1847; obj* x_1849; 
lean::dec(x_8);
lean::dec(x_10);
x_1836 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_1837 = lean::cnstr_get(x_1836, 0);
lean::inc(x_1837);
lean::dec(x_1836);
lean::inc(x_0);
x_1841 = lean::apply_1(x_1837, x_0);
x_1842 = lean::cnstr_get(x_1841, 1);
lean::inc(x_1842);
lean::dec(x_1841);
x_1845 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_1842);
x_1846 = l_Lean_Expander_getOptType___main___closed__1;
x_1847 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_1846, x_1845);
lean::inc(x_2);
x_1849 = l_Lean_Elaborator_toPexpr___main(x_1847, x_1, x_2, x_3);
if (lean::obj_tag(x_1849) == 0)
{
obj* x_1852; obj* x_1854; obj* x_1855; 
lean::dec(x_0);
lean::dec(x_2);
x_1852 = lean::cnstr_get(x_1849, 0);
if (lean::is_exclusive(x_1849)) {
 x_1854 = x_1849;
} else {
 lean::inc(x_1852);
 lean::dec(x_1849);
 x_1854 = lean::box(0);
}
if (lean::is_scalar(x_1854)) {
 x_1855 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1855 = x_1854;
}
lean::cnstr_set(x_1855, 0, x_1852);
return x_1855;
}
else
{
obj* x_1856; obj* x_1858; obj* x_1859; obj* x_1861; obj* x_1863; obj* x_1864; obj* x_1865; obj* x_1866; 
x_1856 = lean::cnstr_get(x_1849, 0);
if (lean::is_exclusive(x_1849)) {
 lean::cnstr_set(x_1849, 0, lean::box(0));
 x_1858 = x_1849;
} else {
 lean::inc(x_1856);
 lean::dec(x_1849);
 x_1858 = lean::box(0);
}
x_1859 = lean::cnstr_get(x_1856, 0);
x_1861 = lean::cnstr_get(x_1856, 1);
if (lean::is_exclusive(x_1856)) {
 lean::cnstr_set(x_1856, 0, lean::box(0));
 lean::cnstr_set(x_1856, 1, lean::box(0));
 x_1863 = x_1856;
} else {
 lean::inc(x_1859);
 lean::inc(x_1861);
 lean::dec(x_1856);
 x_1863 = lean::box(0);
}
x_1864 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1865 = l_Lean_Elaborator_Expr_mkAnnotation(x_1864, x_1859);
x_1866 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1866) == 0)
{
obj* x_1869; obj* x_1870; 
lean::dec(x_2);
if (lean::is_scalar(x_1863)) {
 x_1869 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1869 = x_1863;
}
lean::cnstr_set(x_1869, 0, x_1865);
lean::cnstr_set(x_1869, 1, x_1861);
if (lean::is_scalar(x_1858)) {
 x_1870 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1870 = x_1858;
}
lean::cnstr_set(x_1870, 0, x_1869);
return x_1870;
}
else
{
obj* x_1871; obj* x_1874; obj* x_1877; obj* x_1880; obj* x_1881; obj* x_1883; obj* x_1884; obj* x_1885; obj* x_1886; obj* x_1889; obj* x_1890; obj* x_1891; obj* x_1892; obj* x_1893; 
x_1871 = lean::cnstr_get(x_1866, 0);
lean::inc(x_1871);
lean::dec(x_1866);
x_1874 = lean::cnstr_get(x_2, 0);
lean::inc(x_1874);
lean::dec(x_2);
x_1877 = lean::cnstr_get(x_1874, 2);
lean::inc(x_1877);
lean::dec(x_1874);
x_1880 = l_Lean_FileMap_toPosition(x_1877, x_1871);
x_1881 = lean::cnstr_get(x_1880, 1);
lean::inc(x_1881);
x_1883 = lean::box(0);
x_1884 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1885 = l_Lean_KVMap_setNat(x_1883, x_1884, x_1881);
x_1886 = lean::cnstr_get(x_1880, 0);
lean::inc(x_1886);
lean::dec(x_1880);
x_1889 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1890 = l_Lean_KVMap_setNat(x_1885, x_1889, x_1886);
x_1891 = lean_expr_mk_mdata(x_1890, x_1865);
if (lean::is_scalar(x_1863)) {
 x_1892 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1892 = x_1863;
}
lean::cnstr_set(x_1892, 0, x_1891);
lean::cnstr_set(x_1892, 1, x_1861);
if (lean::is_scalar(x_1858)) {
 x_1893 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1893 = x_1858;
}
lean::cnstr_set(x_1893, 0, x_1892);
return x_1893;
}
}
}
}
else
{
obj* x_1896; obj* x_1897; obj* x_1901; obj* x_1902; obj* x_1903; obj* x_1906; obj* x_1908; 
lean::dec(x_8);
lean::dec(x_10);
x_1896 = l_Lean_Parser_Term_sortApp_HasView;
x_1897 = lean::cnstr_get(x_1896, 0);
lean::inc(x_1897);
lean::dec(x_1896);
lean::inc(x_0);
x_1901 = lean::apply_1(x_1897, x_0);
x_1902 = l_Lean_Parser_Term_sort_HasView;
x_1903 = lean::cnstr_get(x_1902, 0);
lean::inc(x_1903);
lean::dec(x_1902);
x_1906 = lean::cnstr_get(x_1901, 0);
lean::inc(x_1906);
x_1908 = lean::apply_1(x_1903, x_1906);
if (lean::obj_tag(x_1908) == 0)
{
obj* x_1910; obj* x_1914; 
lean::dec(x_1908);
x_1910 = lean::cnstr_get(x_1901, 1);
lean::inc(x_1910);
lean::dec(x_1901);
lean::inc(x_2);
x_1914 = l_Lean_Elaborator_toLevel___main(x_1910, x_1, x_2, x_3);
if (lean::obj_tag(x_1914) == 0)
{
obj* x_1917; obj* x_1919; obj* x_1920; 
lean::dec(x_0);
lean::dec(x_2);
x_1917 = lean::cnstr_get(x_1914, 0);
if (lean::is_exclusive(x_1914)) {
 x_1919 = x_1914;
} else {
 lean::inc(x_1917);
 lean::dec(x_1914);
 x_1919 = lean::box(0);
}
if (lean::is_scalar(x_1919)) {
 x_1920 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1920 = x_1919;
}
lean::cnstr_set(x_1920, 0, x_1917);
return x_1920;
}
else
{
obj* x_1921; obj* x_1923; obj* x_1924; obj* x_1926; obj* x_1928; obj* x_1929; obj* x_1930; 
x_1921 = lean::cnstr_get(x_1914, 0);
if (lean::is_exclusive(x_1914)) {
 lean::cnstr_set(x_1914, 0, lean::box(0));
 x_1923 = x_1914;
} else {
 lean::inc(x_1921);
 lean::dec(x_1914);
 x_1923 = lean::box(0);
}
x_1924 = lean::cnstr_get(x_1921, 0);
x_1926 = lean::cnstr_get(x_1921, 1);
if (lean::is_exclusive(x_1921)) {
 lean::cnstr_set(x_1921, 0, lean::box(0));
 lean::cnstr_set(x_1921, 1, lean::box(0));
 x_1928 = x_1921;
} else {
 lean::inc(x_1924);
 lean::inc(x_1926);
 lean::dec(x_1921);
 x_1928 = lean::box(0);
}
x_1929 = lean_expr_mk_sort(x_1924);
x_1930 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1930) == 0)
{
obj* x_1933; obj* x_1934; 
lean::dec(x_2);
if (lean::is_scalar(x_1928)) {
 x_1933 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1933 = x_1928;
}
lean::cnstr_set(x_1933, 0, x_1929);
lean::cnstr_set(x_1933, 1, x_1926);
if (lean::is_scalar(x_1923)) {
 x_1934 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1934 = x_1923;
}
lean::cnstr_set(x_1934, 0, x_1933);
return x_1934;
}
else
{
obj* x_1935; obj* x_1938; obj* x_1941; obj* x_1944; obj* x_1945; obj* x_1947; obj* x_1948; obj* x_1949; obj* x_1950; obj* x_1953; obj* x_1954; obj* x_1955; obj* x_1956; obj* x_1957; 
x_1935 = lean::cnstr_get(x_1930, 0);
lean::inc(x_1935);
lean::dec(x_1930);
x_1938 = lean::cnstr_get(x_2, 0);
lean::inc(x_1938);
lean::dec(x_2);
x_1941 = lean::cnstr_get(x_1938, 2);
lean::inc(x_1941);
lean::dec(x_1938);
x_1944 = l_Lean_FileMap_toPosition(x_1941, x_1935);
x_1945 = lean::cnstr_get(x_1944, 1);
lean::inc(x_1945);
x_1947 = lean::box(0);
x_1948 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1949 = l_Lean_KVMap_setNat(x_1947, x_1948, x_1945);
x_1950 = lean::cnstr_get(x_1944, 0);
lean::inc(x_1950);
lean::dec(x_1944);
x_1953 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1954 = l_Lean_KVMap_setNat(x_1949, x_1953, x_1950);
x_1955 = lean_expr_mk_mdata(x_1954, x_1929);
if (lean::is_scalar(x_1928)) {
 x_1956 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1956 = x_1928;
}
lean::cnstr_set(x_1956, 0, x_1955);
lean::cnstr_set(x_1956, 1, x_1926);
if (lean::is_scalar(x_1923)) {
 x_1957 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1957 = x_1923;
}
lean::cnstr_set(x_1957, 0, x_1956);
return x_1957;
}
}
}
else
{
obj* x_1959; obj* x_1963; 
lean::dec(x_1908);
x_1959 = lean::cnstr_get(x_1901, 1);
lean::inc(x_1959);
lean::dec(x_1901);
lean::inc(x_2);
x_1963 = l_Lean_Elaborator_toLevel___main(x_1959, x_1, x_2, x_3);
if (lean::obj_tag(x_1963) == 0)
{
obj* x_1966; obj* x_1968; obj* x_1969; 
lean::dec(x_0);
lean::dec(x_2);
x_1966 = lean::cnstr_get(x_1963, 0);
if (lean::is_exclusive(x_1963)) {
 x_1968 = x_1963;
} else {
 lean::inc(x_1966);
 lean::dec(x_1963);
 x_1968 = lean::box(0);
}
if (lean::is_scalar(x_1968)) {
 x_1969 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1969 = x_1968;
}
lean::cnstr_set(x_1969, 0, x_1966);
return x_1969;
}
else
{
obj* x_1970; obj* x_1972; obj* x_1973; obj* x_1975; obj* x_1977; obj* x_1978; obj* x_1979; obj* x_1980; 
x_1970 = lean::cnstr_get(x_1963, 0);
if (lean::is_exclusive(x_1963)) {
 lean::cnstr_set(x_1963, 0, lean::box(0));
 x_1972 = x_1963;
} else {
 lean::inc(x_1970);
 lean::dec(x_1963);
 x_1972 = lean::box(0);
}
x_1973 = lean::cnstr_get(x_1970, 0);
x_1975 = lean::cnstr_get(x_1970, 1);
if (lean::is_exclusive(x_1970)) {
 lean::cnstr_set(x_1970, 0, lean::box(0));
 lean::cnstr_set(x_1970, 1, lean::box(0));
 x_1977 = x_1970;
} else {
 lean::inc(x_1973);
 lean::inc(x_1975);
 lean::dec(x_1970);
 x_1977 = lean::box(0);
}
x_1978 = level_mk_succ(x_1973);
x_1979 = lean_expr_mk_sort(x_1978);
x_1980 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1980) == 0)
{
obj* x_1983; obj* x_1984; 
lean::dec(x_2);
if (lean::is_scalar(x_1977)) {
 x_1983 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1983 = x_1977;
}
lean::cnstr_set(x_1983, 0, x_1979);
lean::cnstr_set(x_1983, 1, x_1975);
if (lean::is_scalar(x_1972)) {
 x_1984 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1984 = x_1972;
}
lean::cnstr_set(x_1984, 0, x_1983);
return x_1984;
}
else
{
obj* x_1985; obj* x_1988; obj* x_1991; obj* x_1994; obj* x_1995; obj* x_1997; obj* x_1998; obj* x_1999; obj* x_2000; obj* x_2003; obj* x_2004; obj* x_2005; obj* x_2006; obj* x_2007; 
x_1985 = lean::cnstr_get(x_1980, 0);
lean::inc(x_1985);
lean::dec(x_1980);
x_1988 = lean::cnstr_get(x_2, 0);
lean::inc(x_1988);
lean::dec(x_2);
x_1991 = lean::cnstr_get(x_1988, 2);
lean::inc(x_1991);
lean::dec(x_1988);
x_1994 = l_Lean_FileMap_toPosition(x_1991, x_1985);
x_1995 = lean::cnstr_get(x_1994, 1);
lean::inc(x_1995);
x_1997 = lean::box(0);
x_1998 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1999 = l_Lean_KVMap_setNat(x_1997, x_1998, x_1995);
x_2000 = lean::cnstr_get(x_1994, 0);
lean::inc(x_2000);
lean::dec(x_1994);
x_2003 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2004 = l_Lean_KVMap_setNat(x_1999, x_2003, x_2000);
x_2005 = lean_expr_mk_mdata(x_2004, x_1979);
if (lean::is_scalar(x_1977)) {
 x_2006 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2006 = x_1977;
}
lean::cnstr_set(x_2006, 0, x_2005);
lean::cnstr_set(x_2006, 1, x_1975);
if (lean::is_scalar(x_1972)) {
 x_2007 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2007 = x_1972;
}
lean::cnstr_set(x_2007, 0, x_2006);
return x_2007;
}
}
}
}
}
else
{
obj* x_2011; obj* x_2012; obj* x_2016; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_2011 = l_Lean_Parser_Term_sort_HasView;
x_2012 = lean::cnstr_get(x_2011, 0);
lean::inc(x_2012);
lean::dec(x_2011);
lean::inc(x_0);
x_2016 = lean::apply_1(x_2012, x_0);
if (lean::obj_tag(x_2016) == 0)
{
obj* x_2018; 
lean::dec(x_2016);
x_2018 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2018) == 0)
{
obj* x_2021; obj* x_2022; obj* x_2023; 
lean::dec(x_2);
x_2021 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_2022 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2022, 0, x_2021);
lean::cnstr_set(x_2022, 1, x_3);
x_2023 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2023, 0, x_2022);
return x_2023;
}
else
{
obj* x_2024; obj* x_2027; obj* x_2030; obj* x_2033; obj* x_2034; obj* x_2036; obj* x_2037; obj* x_2038; obj* x_2039; obj* x_2042; obj* x_2043; obj* x_2044; obj* x_2045; obj* x_2046; obj* x_2047; 
x_2024 = lean::cnstr_get(x_2018, 0);
lean::inc(x_2024);
lean::dec(x_2018);
x_2027 = lean::cnstr_get(x_2, 0);
lean::inc(x_2027);
lean::dec(x_2);
x_2030 = lean::cnstr_get(x_2027, 2);
lean::inc(x_2030);
lean::dec(x_2027);
x_2033 = l_Lean_FileMap_toPosition(x_2030, x_2024);
x_2034 = lean::cnstr_get(x_2033, 1);
lean::inc(x_2034);
x_2036 = lean::box(0);
x_2037 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2038 = l_Lean_KVMap_setNat(x_2036, x_2037, x_2034);
x_2039 = lean::cnstr_get(x_2033, 0);
lean::inc(x_2039);
lean::dec(x_2033);
x_2042 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2043 = l_Lean_KVMap_setNat(x_2038, x_2042, x_2039);
x_2044 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_2045 = lean_expr_mk_mdata(x_2043, x_2044);
x_2046 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2046, 0, x_2045);
lean::cnstr_set(x_2046, 1, x_3);
x_2047 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2047, 0, x_2046);
return x_2047;
}
}
else
{
obj* x_2049; 
lean::dec(x_2016);
x_2049 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2049) == 0)
{
obj* x_2052; obj* x_2053; obj* x_2054; 
lean::dec(x_2);
x_2052 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2053 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2053, 0, x_2052);
lean::cnstr_set(x_2053, 1, x_3);
x_2054 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2054, 0, x_2053);
return x_2054;
}
else
{
obj* x_2055; obj* x_2058; obj* x_2061; obj* x_2064; obj* x_2065; obj* x_2067; obj* x_2068; obj* x_2069; obj* x_2070; obj* x_2073; obj* x_2074; obj* x_2075; obj* x_2076; obj* x_2077; obj* x_2078; 
x_2055 = lean::cnstr_get(x_2049, 0);
lean::inc(x_2055);
lean::dec(x_2049);
x_2058 = lean::cnstr_get(x_2, 0);
lean::inc(x_2058);
lean::dec(x_2);
x_2061 = lean::cnstr_get(x_2058, 2);
lean::inc(x_2061);
lean::dec(x_2058);
x_2064 = l_Lean_FileMap_toPosition(x_2061, x_2055);
x_2065 = lean::cnstr_get(x_2064, 1);
lean::inc(x_2065);
x_2067 = lean::box(0);
x_2068 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2069 = l_Lean_KVMap_setNat(x_2067, x_2068, x_2065);
x_2070 = lean::cnstr_get(x_2064, 0);
lean::inc(x_2070);
lean::dec(x_2064);
x_2073 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2074 = l_Lean_KVMap_setNat(x_2069, x_2073, x_2070);
x_2075 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2076 = lean_expr_mk_mdata(x_2074, x_2075);
x_2077 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2077, 0, x_2076);
lean::cnstr_set(x_2077, 1, x_3);
x_2078 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2078, 0, x_2077);
return x_2078;
}
}
}
}
else
{
obj* x_2080; obj* x_2081; obj* x_2085; obj* x_2086; 
lean::dec(x_10);
x_2080 = l_Lean_Parser_Term_pi_HasView;
x_2081 = lean::cnstr_get(x_2080, 0);
lean::inc(x_2081);
lean::dec(x_2080);
lean::inc(x_0);
x_2085 = lean::apply_1(x_2081, x_0);
x_2086 = lean::cnstr_get(x_2085, 1);
lean::inc(x_2086);
if (lean::obj_tag(x_2086) == 0)
{
obj* x_2091; obj* x_2092; obj* x_2094; 
lean::dec(x_2086);
lean::dec(x_2085);
lean::inc(x_0);
x_2091 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2091, 0, x_0);
x_2092 = l_Lean_Elaborator_toPexpr___main___closed__43;
lean::inc(x_2);
x_2094 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2091, x_2092, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_2091);
if (lean::obj_tag(x_2094) == 0)
{
obj* x_2101; obj* x_2103; obj* x_2104; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2101 = lean::cnstr_get(x_2094, 0);
if (lean::is_exclusive(x_2094)) {
 x_2103 = x_2094;
} else {
 lean::inc(x_2101);
 lean::dec(x_2094);
 x_2103 = lean::box(0);
}
if (lean::is_scalar(x_2103)) {
 x_2104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2104 = x_2103;
}
lean::cnstr_set(x_2104, 0, x_2101);
return x_2104;
}
else
{
obj* x_2105; 
x_2105 = lean::cnstr_get(x_2094, 0);
lean::inc(x_2105);
lean::dec(x_2094);
x_15 = x_2105;
goto lbl_16;
}
}
else
{
obj* x_2108; obj* x_2111; obj* x_2112; obj* x_2114; obj* x_2117; obj* x_2119; obj* x_2124; 
x_2108 = lean::cnstr_get(x_2086, 0);
lean::inc(x_2108);
lean::dec(x_2086);
x_2111 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2108);
x_2112 = lean::cnstr_get(x_2111, 1);
lean::inc(x_2112);
x_2114 = lean::cnstr_get(x_2111, 0);
lean::inc(x_2114);
lean::dec(x_2111);
x_2117 = lean::cnstr_get(x_2112, 0);
lean::inc(x_2117);
x_2119 = lean::cnstr_get(x_2112, 1);
lean::inc(x_2119);
lean::dec(x_2112);
lean::inc(x_2);
lean::inc(x_1);
x_2124 = l_Lean_Elaborator_toPexpr___main(x_2119, x_1, x_2, x_3);
if (lean::obj_tag(x_2124) == 0)
{
obj* x_2132; obj* x_2134; obj* x_2135; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2085);
lean::dec(x_2114);
lean::dec(x_2117);
x_2132 = lean::cnstr_get(x_2124, 0);
if (lean::is_exclusive(x_2124)) {
 x_2134 = x_2124;
} else {
 lean::inc(x_2132);
 lean::dec(x_2124);
 x_2134 = lean::box(0);
}
if (lean::is_scalar(x_2134)) {
 x_2135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2135 = x_2134;
}
lean::cnstr_set(x_2135, 0, x_2132);
return x_2135;
}
else
{
obj* x_2136; obj* x_2139; obj* x_2141; obj* x_2144; obj* x_2148; 
x_2136 = lean::cnstr_get(x_2124, 0);
lean::inc(x_2136);
lean::dec(x_2124);
x_2139 = lean::cnstr_get(x_2136, 0);
lean::inc(x_2139);
x_2141 = lean::cnstr_get(x_2136, 1);
lean::inc(x_2141);
lean::dec(x_2136);
x_2144 = lean::cnstr_get(x_2085, 3);
lean::inc(x_2144);
lean::dec(x_2085);
lean::inc(x_2);
x_2148 = l_Lean_Elaborator_toPexpr___main(x_2144, x_1, x_2, x_2141);
if (lean::obj_tag(x_2148) == 0)
{
obj* x_2155; obj* x_2157; obj* x_2158; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2114);
lean::dec(x_2117);
lean::dec(x_2139);
x_2155 = lean::cnstr_get(x_2148, 0);
if (lean::is_exclusive(x_2148)) {
 x_2157 = x_2148;
} else {
 lean::inc(x_2155);
 lean::dec(x_2148);
 x_2157 = lean::box(0);
}
if (lean::is_scalar(x_2157)) {
 x_2158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2158 = x_2157;
}
lean::cnstr_set(x_2158, 0, x_2155);
return x_2158;
}
else
{
obj* x_2159; obj* x_2162; obj* x_2164; obj* x_2166; obj* x_2167; uint8 x_2168; obj* x_2169; obj* x_2170; 
x_2159 = lean::cnstr_get(x_2148, 0);
lean::inc(x_2159);
lean::dec(x_2148);
x_2162 = lean::cnstr_get(x_2159, 0);
x_2164 = lean::cnstr_get(x_2159, 1);
if (lean::is_exclusive(x_2159)) {
 x_2166 = x_2159;
} else {
 lean::inc(x_2162);
 lean::inc(x_2164);
 lean::dec(x_2159);
 x_2166 = lean::box(0);
}
x_2167 = l_Lean_Elaborator_mangleIdent(x_2117);
x_2168 = lean::unbox(x_2114);
x_2169 = lean_expr_mk_pi(x_2167, x_2168, x_2139, x_2162);
if (lean::is_scalar(x_2166)) {
 x_2170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2170 = x_2166;
}
lean::cnstr_set(x_2170, 0, x_2169);
lean::cnstr_set(x_2170, 1, x_2164);
x_15 = x_2170;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2172; obj* x_2173; obj* x_2177; obj* x_2178; 
lean::dec(x_10);
x_2172 = l_Lean_Parser_Term_lambda_HasView;
x_2173 = lean::cnstr_get(x_2172, 0);
lean::inc(x_2173);
lean::dec(x_2172);
lean::inc(x_0);
x_2177 = lean::apply_1(x_2173, x_0);
x_2178 = lean::cnstr_get(x_2177, 1);
lean::inc(x_2178);
if (lean::obj_tag(x_2178) == 0)
{
obj* x_2183; obj* x_2184; obj* x_2186; 
lean::dec(x_2177);
lean::dec(x_2178);
lean::inc(x_0);
x_2183 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2183, 0, x_0);
x_2184 = l_Lean_Elaborator_toPexpr___main___closed__44;
lean::inc(x_2);
x_2186 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2183, x_2184, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_2183);
if (lean::obj_tag(x_2186) == 0)
{
obj* x_2193; obj* x_2195; obj* x_2196; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2193 = lean::cnstr_get(x_2186, 0);
if (lean::is_exclusive(x_2186)) {
 x_2195 = x_2186;
} else {
 lean::inc(x_2193);
 lean::dec(x_2186);
 x_2195 = lean::box(0);
}
if (lean::is_scalar(x_2195)) {
 x_2196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2196 = x_2195;
}
lean::cnstr_set(x_2196, 0, x_2193);
return x_2196;
}
else
{
obj* x_2197; 
x_2197 = lean::cnstr_get(x_2186, 0);
lean::inc(x_2197);
lean::dec(x_2186);
x_15 = x_2197;
goto lbl_16;
}
}
else
{
obj* x_2200; obj* x_2203; obj* x_2204; obj* x_2206; obj* x_2209; obj* x_2211; obj* x_2216; 
x_2200 = lean::cnstr_get(x_2178, 0);
lean::inc(x_2200);
lean::dec(x_2178);
x_2203 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2200);
x_2204 = lean::cnstr_get(x_2203, 1);
lean::inc(x_2204);
x_2206 = lean::cnstr_get(x_2203, 0);
lean::inc(x_2206);
lean::dec(x_2203);
x_2209 = lean::cnstr_get(x_2204, 0);
lean::inc(x_2209);
x_2211 = lean::cnstr_get(x_2204, 1);
lean::inc(x_2211);
lean::dec(x_2204);
lean::inc(x_2);
lean::inc(x_1);
x_2216 = l_Lean_Elaborator_toPexpr___main(x_2211, x_1, x_2, x_3);
if (lean::obj_tag(x_2216) == 0)
{
obj* x_2224; obj* x_2226; obj* x_2227; 
lean::dec(x_2209);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2177);
lean::dec(x_2206);
x_2224 = lean::cnstr_get(x_2216, 0);
if (lean::is_exclusive(x_2216)) {
 x_2226 = x_2216;
} else {
 lean::inc(x_2224);
 lean::dec(x_2216);
 x_2226 = lean::box(0);
}
if (lean::is_scalar(x_2226)) {
 x_2227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2227 = x_2226;
}
lean::cnstr_set(x_2227, 0, x_2224);
return x_2227;
}
else
{
obj* x_2228; obj* x_2231; obj* x_2233; obj* x_2236; obj* x_2240; 
x_2228 = lean::cnstr_get(x_2216, 0);
lean::inc(x_2228);
lean::dec(x_2216);
x_2231 = lean::cnstr_get(x_2228, 0);
lean::inc(x_2231);
x_2233 = lean::cnstr_get(x_2228, 1);
lean::inc(x_2233);
lean::dec(x_2228);
x_2236 = lean::cnstr_get(x_2177, 3);
lean::inc(x_2236);
lean::dec(x_2177);
lean::inc(x_2);
x_2240 = l_Lean_Elaborator_toPexpr___main(x_2236, x_1, x_2, x_2233);
if (lean::obj_tag(x_2240) == 0)
{
obj* x_2247; obj* x_2249; obj* x_2250; 
lean::dec(x_2209);
lean::dec(x_2231);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2206);
x_2247 = lean::cnstr_get(x_2240, 0);
if (lean::is_exclusive(x_2240)) {
 x_2249 = x_2240;
} else {
 lean::inc(x_2247);
 lean::dec(x_2240);
 x_2249 = lean::box(0);
}
if (lean::is_scalar(x_2249)) {
 x_2250 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2250 = x_2249;
}
lean::cnstr_set(x_2250, 0, x_2247);
return x_2250;
}
else
{
obj* x_2251; obj* x_2254; obj* x_2256; obj* x_2258; obj* x_2259; uint8 x_2260; obj* x_2261; obj* x_2262; 
x_2251 = lean::cnstr_get(x_2240, 0);
lean::inc(x_2251);
lean::dec(x_2240);
x_2254 = lean::cnstr_get(x_2251, 0);
x_2256 = lean::cnstr_get(x_2251, 1);
if (lean::is_exclusive(x_2251)) {
 x_2258 = x_2251;
} else {
 lean::inc(x_2254);
 lean::inc(x_2256);
 lean::dec(x_2251);
 x_2258 = lean::box(0);
}
x_2259 = l_Lean_Elaborator_mangleIdent(x_2209);
x_2260 = lean::unbox(x_2206);
x_2261 = lean_expr_mk_lambda(x_2259, x_2260, x_2231, x_2254);
if (lean::is_scalar(x_2258)) {
 x_2262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2262 = x_2258;
}
lean::cnstr_set(x_2262, 0, x_2261);
lean::cnstr_set(x_2262, 1, x_2256);
x_15 = x_2262;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2265; obj* x_2266; obj* x_2269; obj* x_2270; obj* x_2274; 
lean::dec(x_8);
lean::dec(x_10);
x_2265 = l_Lean_Parser_Term_app_HasView;
x_2266 = lean::cnstr_get(x_2265, 0);
lean::inc(x_2266);
lean::dec(x_2265);
x_2269 = lean::apply_1(x_2266, x_0);
x_2270 = lean::cnstr_get(x_2269, 0);
lean::inc(x_2270);
lean::inc(x_2);
lean::inc(x_1);
x_2274 = l_Lean_Elaborator_toPexpr___main(x_2270, x_1, x_2, x_3);
if (lean::obj_tag(x_2274) == 0)
{
obj* x_2278; obj* x_2280; obj* x_2281; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_2269);
x_2278 = lean::cnstr_get(x_2274, 0);
if (lean::is_exclusive(x_2274)) {
 x_2280 = x_2274;
} else {
 lean::inc(x_2278);
 lean::dec(x_2274);
 x_2280 = lean::box(0);
}
if (lean::is_scalar(x_2280)) {
 x_2281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2281 = x_2280;
}
lean::cnstr_set(x_2281, 0, x_2278);
return x_2281;
}
else
{
obj* x_2282; obj* x_2285; obj* x_2287; obj* x_2290; obj* x_2293; 
x_2282 = lean::cnstr_get(x_2274, 0);
lean::inc(x_2282);
lean::dec(x_2274);
x_2285 = lean::cnstr_get(x_2282, 0);
lean::inc(x_2285);
x_2287 = lean::cnstr_get(x_2282, 1);
lean::inc(x_2287);
lean::dec(x_2282);
x_2290 = lean::cnstr_get(x_2269, 1);
lean::inc(x_2290);
lean::dec(x_2269);
x_2293 = l_Lean_Elaborator_toPexpr___main(x_2290, x_1, x_2, x_2287);
if (lean::obj_tag(x_2293) == 0)
{
obj* x_2295; obj* x_2297; obj* x_2298; 
lean::dec(x_2285);
x_2295 = lean::cnstr_get(x_2293, 0);
if (lean::is_exclusive(x_2293)) {
 x_2297 = x_2293;
} else {
 lean::inc(x_2295);
 lean::dec(x_2293);
 x_2297 = lean::box(0);
}
if (lean::is_scalar(x_2297)) {
 x_2298 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2298 = x_2297;
}
lean::cnstr_set(x_2298, 0, x_2295);
return x_2298;
}
else
{
obj* x_2299; obj* x_2301; obj* x_2302; obj* x_2304; obj* x_2306; obj* x_2307; obj* x_2308; obj* x_2309; 
x_2299 = lean::cnstr_get(x_2293, 0);
if (lean::is_exclusive(x_2293)) {
 x_2301 = x_2293;
} else {
 lean::inc(x_2299);
 lean::dec(x_2293);
 x_2301 = lean::box(0);
}
x_2302 = lean::cnstr_get(x_2299, 0);
x_2304 = lean::cnstr_get(x_2299, 1);
if (lean::is_exclusive(x_2299)) {
 x_2306 = x_2299;
} else {
 lean::inc(x_2302);
 lean::inc(x_2304);
 lean::dec(x_2299);
 x_2306 = lean::box(0);
}
x_2307 = lean_expr_mk_app(x_2285, x_2302);
if (lean::is_scalar(x_2306)) {
 x_2308 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2308 = x_2306;
}
lean::cnstr_set(x_2308, 0, x_2307);
lean::cnstr_set(x_2308, 1, x_2304);
if (lean::is_scalar(x_2301)) {
 x_2309 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2309 = x_2301;
}
lean::cnstr_set(x_2309, 0, x_2308);
return x_2309;
}
}
}
}
else
{
obj* x_2311; obj* x_2312; obj* x_2316; obj* x_2317; 
lean::dec(x_10);
x_2311 = l_Lean_Parser_identUnivs_HasView;
x_2312 = lean::cnstr_get(x_2311, 0);
lean::inc(x_2312);
lean::dec(x_2311);
lean::inc(x_0);
x_2316 = lean::apply_1(x_2312, x_0);
x_2317 = lean::cnstr_get(x_2316, 1);
lean::inc(x_2317);
if (lean::obj_tag(x_2317) == 0)
{
obj* x_2320; obj* x_2324; obj* x_2325; obj* x_2326; obj* x_2327; obj* x_2330; obj* x_2331; obj* x_2332; obj* x_2333; obj* x_2334; obj* x_2335; uint8 x_2336; 
lean::dec(x_1);
x_2320 = lean::cnstr_get(x_2316, 0);
lean::inc(x_2320);
lean::dec(x_2316);
lean::inc(x_2320);
x_2324 = l_Lean_Elaborator_mangleIdent(x_2320);
x_2325 = lean::box(0);
x_2326 = lean_expr_mk_const(x_2324, x_2325);
x_2327 = lean::cnstr_get(x_2320, 3);
lean::inc(x_2327);
lean::dec(x_2320);
x_2330 = lean::mk_nat_obj(0ul);
x_2331 = l_List_enumFrom___main___rarg(x_2330, x_2327);
x_2332 = l_Lean_Elaborator_toPexpr___main___closed__45;
x_2333 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2332, x_2331);
x_2334 = lean_expr_mk_mdata(x_2333, x_2326);
x_2335 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2336 = lean_name_dec_eq(x_8, x_2335);
lean::dec(x_8);
if (x_2336 == 0)
{
obj* x_2338; 
x_2338 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2338) == 0)
{
obj* x_2341; obj* x_2342; 
lean::dec(x_2);
x_2341 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2341, 0, x_2334);
lean::cnstr_set(x_2341, 1, x_3);
x_2342 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2342, 0, x_2341);
return x_2342;
}
else
{
obj* x_2343; obj* x_2346; obj* x_2349; obj* x_2352; obj* x_2353; obj* x_2355; obj* x_2356; obj* x_2357; obj* x_2360; obj* x_2361; obj* x_2362; obj* x_2363; obj* x_2364; 
x_2343 = lean::cnstr_get(x_2338, 0);
lean::inc(x_2343);
lean::dec(x_2338);
x_2346 = lean::cnstr_get(x_2, 0);
lean::inc(x_2346);
lean::dec(x_2);
x_2349 = lean::cnstr_get(x_2346, 2);
lean::inc(x_2349);
lean::dec(x_2346);
x_2352 = l_Lean_FileMap_toPosition(x_2349, x_2343);
x_2353 = lean::cnstr_get(x_2352, 1);
lean::inc(x_2353);
x_2355 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2356 = l_Lean_KVMap_setNat(x_2325, x_2355, x_2353);
x_2357 = lean::cnstr_get(x_2352, 0);
lean::inc(x_2357);
lean::dec(x_2352);
x_2360 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2361 = l_Lean_KVMap_setNat(x_2356, x_2360, x_2357);
x_2362 = lean_expr_mk_mdata(x_2361, x_2334);
x_2363 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2363, 0, x_2362);
lean::cnstr_set(x_2363, 1, x_3);
x_2364 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2364, 0, x_2363);
return x_2364;
}
}
else
{
obj* x_2367; obj* x_2368; 
lean::dec(x_0);
lean::dec(x_2);
x_2367 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2367, 0, x_2334);
lean::cnstr_set(x_2367, 1, x_3);
x_2368 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2368, 0, x_2367);
return x_2368;
}
}
else
{
obj* x_2369; obj* x_2372; obj* x_2375; obj* x_2379; 
x_2369 = lean::cnstr_get(x_2316, 0);
lean::inc(x_2369);
lean::dec(x_2316);
x_2372 = lean::cnstr_get(x_2317, 0);
lean::inc(x_2372);
lean::dec(x_2317);
x_2375 = lean::cnstr_get(x_2372, 1);
lean::inc(x_2375);
lean::dec(x_2372);
lean::inc(x_2);
x_2379 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_2375, x_1, x_2, x_3);
if (lean::obj_tag(x_2379) == 0)
{
obj* x_2384; obj* x_2386; obj* x_2387; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2369);
x_2384 = lean::cnstr_get(x_2379, 0);
if (lean::is_exclusive(x_2379)) {
 x_2386 = x_2379;
} else {
 lean::inc(x_2384);
 lean::dec(x_2379);
 x_2386 = lean::box(0);
}
if (lean::is_scalar(x_2386)) {
 x_2387 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2387 = x_2386;
}
lean::cnstr_set(x_2387, 0, x_2384);
return x_2387;
}
else
{
obj* x_2388; obj* x_2390; obj* x_2391; obj* x_2393; obj* x_2395; obj* x_2397; obj* x_2398; obj* x_2399; obj* x_2402; obj* x_2403; obj* x_2404; obj* x_2405; obj* x_2406; obj* x_2407; uint8 x_2408; 
x_2388 = lean::cnstr_get(x_2379, 0);
if (lean::is_exclusive(x_2379)) {
 lean::cnstr_set(x_2379, 0, lean::box(0));
 x_2390 = x_2379;
} else {
 lean::inc(x_2388);
 lean::dec(x_2379);
 x_2390 = lean::box(0);
}
x_2391 = lean::cnstr_get(x_2388, 0);
x_2393 = lean::cnstr_get(x_2388, 1);
if (lean::is_exclusive(x_2388)) {
 lean::cnstr_set(x_2388, 0, lean::box(0));
 lean::cnstr_set(x_2388, 1, lean::box(0));
 x_2395 = x_2388;
} else {
 lean::inc(x_2391);
 lean::inc(x_2393);
 lean::dec(x_2388);
 x_2395 = lean::box(0);
}
lean::inc(x_2369);
x_2397 = l_Lean_Elaborator_mangleIdent(x_2369);
x_2398 = lean_expr_mk_const(x_2397, x_2391);
x_2399 = lean::cnstr_get(x_2369, 3);
lean::inc(x_2399);
lean::dec(x_2369);
x_2402 = lean::mk_nat_obj(0ul);
x_2403 = l_List_enumFrom___main___rarg(x_2402, x_2399);
x_2404 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2405 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2404, x_2403);
x_2406 = lean_expr_mk_mdata(x_2405, x_2398);
x_2407 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2408 = lean_name_dec_eq(x_8, x_2407);
lean::dec(x_8);
if (x_2408 == 0)
{
obj* x_2410; 
x_2410 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2410) == 0)
{
obj* x_2413; obj* x_2414; 
lean::dec(x_2);
if (lean::is_scalar(x_2395)) {
 x_2413 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2413 = x_2395;
}
lean::cnstr_set(x_2413, 0, x_2406);
lean::cnstr_set(x_2413, 1, x_2393);
if (lean::is_scalar(x_2390)) {
 x_2414 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2414 = x_2390;
}
lean::cnstr_set(x_2414, 0, x_2413);
return x_2414;
}
else
{
obj* x_2415; obj* x_2418; obj* x_2419; obj* x_2422; obj* x_2425; obj* x_2426; obj* x_2428; obj* x_2429; obj* x_2430; obj* x_2433; obj* x_2434; obj* x_2435; obj* x_2436; obj* x_2437; 
x_2415 = lean::cnstr_get(x_2410, 0);
lean::inc(x_2415);
lean::dec(x_2410);
x_2418 = lean::box(0);
x_2419 = lean::cnstr_get(x_2, 0);
lean::inc(x_2419);
lean::dec(x_2);
x_2422 = lean::cnstr_get(x_2419, 2);
lean::inc(x_2422);
lean::dec(x_2419);
x_2425 = l_Lean_FileMap_toPosition(x_2422, x_2415);
x_2426 = lean::cnstr_get(x_2425, 1);
lean::inc(x_2426);
x_2428 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2429 = l_Lean_KVMap_setNat(x_2418, x_2428, x_2426);
x_2430 = lean::cnstr_get(x_2425, 0);
lean::inc(x_2430);
lean::dec(x_2425);
x_2433 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2434 = l_Lean_KVMap_setNat(x_2429, x_2433, x_2430);
x_2435 = lean_expr_mk_mdata(x_2434, x_2406);
if (lean::is_scalar(x_2395)) {
 x_2436 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2436 = x_2395;
}
lean::cnstr_set(x_2436, 0, x_2435);
lean::cnstr_set(x_2436, 1, x_2393);
if (lean::is_scalar(x_2390)) {
 x_2437 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2437 = x_2390;
}
lean::cnstr_set(x_2437, 0, x_2436);
return x_2437;
}
}
else
{
obj* x_2440; obj* x_2441; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2395)) {
 x_2440 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2440 = x_2395;
}
lean::cnstr_set(x_2440, 0, x_2406);
lean::cnstr_set(x_2440, 1, x_2393);
if (lean::is_scalar(x_2390)) {
 x_2441 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2441 = x_2390;
}
lean::cnstr_set(x_2441, 0, x_2440);
return x_2441;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2445; obj* x_2447; obj* x_2448; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2445 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2447 = x_13;
} else {
 lean::inc(x_2445);
 lean::dec(x_13);
 x_2447 = lean::box(0);
}
if (lean::is_scalar(x_2447)) {
 x_2448 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2448 = x_2447;
}
lean::cnstr_set(x_2448, 0, x_2445);
return x_2448;
}
else
{
obj* x_2449; obj* x_2451; obj* x_2452; obj* x_2454; obj* x_2456; obj* x_2457; uint8 x_2458; 
x_2449 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2451 = x_13;
} else {
 lean::inc(x_2449);
 lean::dec(x_13);
 x_2451 = lean::box(0);
}
x_2452 = lean::cnstr_get(x_2449, 0);
x_2454 = lean::cnstr_get(x_2449, 1);
if (lean::is_exclusive(x_2449)) {
 lean::cnstr_set(x_2449, 0, lean::box(0));
 lean::cnstr_set(x_2449, 1, lean::box(0));
 x_2456 = x_2449;
} else {
 lean::inc(x_2452);
 lean::inc(x_2454);
 lean::dec(x_2449);
 x_2456 = lean::box(0);
}
x_2457 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2458 = lean_name_dec_eq(x_8, x_2457);
lean::dec(x_8);
if (x_2458 == 0)
{
obj* x_2460; 
x_2460 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2460) == 0)
{
obj* x_2463; obj* x_2464; 
lean::dec(x_2);
if (lean::is_scalar(x_2456)) {
 x_2463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2463 = x_2456;
}
lean::cnstr_set(x_2463, 0, x_2452);
lean::cnstr_set(x_2463, 1, x_2454);
if (lean::is_scalar(x_2451)) {
 x_2464 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2464 = x_2451;
}
lean::cnstr_set(x_2464, 0, x_2463);
return x_2464;
}
else
{
obj* x_2465; obj* x_2468; obj* x_2471; obj* x_2474; obj* x_2475; obj* x_2477; obj* x_2478; obj* x_2479; obj* x_2480; obj* x_2483; obj* x_2484; obj* x_2485; obj* x_2486; obj* x_2487; 
x_2465 = lean::cnstr_get(x_2460, 0);
lean::inc(x_2465);
lean::dec(x_2460);
x_2468 = lean::cnstr_get(x_2, 0);
lean::inc(x_2468);
lean::dec(x_2);
x_2471 = lean::cnstr_get(x_2468, 2);
lean::inc(x_2471);
lean::dec(x_2468);
x_2474 = l_Lean_FileMap_toPosition(x_2471, x_2465);
x_2475 = lean::cnstr_get(x_2474, 1);
lean::inc(x_2475);
x_2477 = lean::box(0);
x_2478 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2479 = l_Lean_KVMap_setNat(x_2477, x_2478, x_2475);
x_2480 = lean::cnstr_get(x_2474, 0);
lean::inc(x_2480);
lean::dec(x_2474);
x_2483 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2484 = l_Lean_KVMap_setNat(x_2479, x_2483, x_2480);
x_2485 = lean_expr_mk_mdata(x_2484, x_2452);
if (lean::is_scalar(x_2456)) {
 x_2486 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2486 = x_2456;
}
lean::cnstr_set(x_2486, 0, x_2485);
lean::cnstr_set(x_2486, 1, x_2454);
if (lean::is_scalar(x_2451)) {
 x_2487 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2487 = x_2451;
}
lean::cnstr_set(x_2487, 0, x_2486);
return x_2487;
}
}
else
{
obj* x_2490; obj* x_2491; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2456)) {
 x_2490 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2490 = x_2456;
}
lean::cnstr_set(x_2490, 0, x_2452);
lean::cnstr_set(x_2490, 1, x_2454);
if (lean::is_scalar(x_2451)) {
 x_2491 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2491 = x_2451;
}
lean::cnstr_set(x_2491, 0, x_2490);
return x_2491;
}
}
}
lbl_16:
{
obj* x_2492; obj* x_2494; obj* x_2496; obj* x_2497; uint8 x_2498; 
x_2492 = lean::cnstr_get(x_15, 0);
x_2494 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2496 = x_15;
} else {
 lean::inc(x_2492);
 lean::inc(x_2494);
 lean::dec(x_15);
 x_2496 = lean::box(0);
}
x_2497 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2498 = lean_name_dec_eq(x_8, x_2497);
lean::dec(x_8);
if (x_2498 == 0)
{
obj* x_2500; 
x_2500 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2500) == 0)
{
obj* x_2503; obj* x_2504; 
lean::dec(x_2);
if (lean::is_scalar(x_2496)) {
 x_2503 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2503 = x_2496;
}
lean::cnstr_set(x_2503, 0, x_2492);
lean::cnstr_set(x_2503, 1, x_2494);
x_2504 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2504, 0, x_2503);
return x_2504;
}
else
{
obj* x_2505; obj* x_2508; obj* x_2511; obj* x_2514; obj* x_2515; obj* x_2517; obj* x_2518; obj* x_2519; obj* x_2520; obj* x_2523; obj* x_2524; obj* x_2525; obj* x_2526; obj* x_2527; 
x_2505 = lean::cnstr_get(x_2500, 0);
lean::inc(x_2505);
lean::dec(x_2500);
x_2508 = lean::cnstr_get(x_2, 0);
lean::inc(x_2508);
lean::dec(x_2);
x_2511 = lean::cnstr_get(x_2508, 2);
lean::inc(x_2511);
lean::dec(x_2508);
x_2514 = l_Lean_FileMap_toPosition(x_2511, x_2505);
x_2515 = lean::cnstr_get(x_2514, 1);
lean::inc(x_2515);
x_2517 = lean::box(0);
x_2518 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2519 = l_Lean_KVMap_setNat(x_2517, x_2518, x_2515);
x_2520 = lean::cnstr_get(x_2514, 0);
lean::inc(x_2520);
lean::dec(x_2514);
x_2523 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2524 = l_Lean_KVMap_setNat(x_2519, x_2523, x_2520);
x_2525 = lean_expr_mk_mdata(x_2524, x_2492);
if (lean::is_scalar(x_2496)) {
 x_2526 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2526 = x_2496;
}
lean::cnstr_set(x_2526, 0, x_2525);
lean::cnstr_set(x_2526, 1, x_2494);
x_2527 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2527, 0, x_2526);
return x_2527;
}
}
else
{
obj* x_2530; obj* x_2531; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2496)) {
 x_2530 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2530 = x_2496;
}
lean::cnstr_set(x_2530, 0, x_2492);
lean::cnstr_set(x_2530, 1, x_2494);
x_2531 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2531, 0, x_2530);
return x_2531;
}
}
}
default:
{
obj* x_2532; 
x_2532 = lean::box(0);
x_4 = x_2532;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2535; obj* x_2536; obj* x_2537; obj* x_2538; obj* x_2539; obj* x_2540; obj* x_2542; 
lean::dec(x_4);
lean::inc(x_0);
x_2535 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2535, 0, x_0);
x_2536 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_2537 = l_Lean_Options_empty;
x_2538 = l_Lean_Format_pretty(x_2536, x_2537);
x_2539 = l_Lean_Elaborator_toPexpr___main___closed__1;
x_2540 = lean::string_append(x_2539, x_2538);
lean::dec(x_2538);
x_2542 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2535, x_2540, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
lean::dec(x_2535);
return x_2542;
}
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
obj* l_Lean_Elaborator_toPexpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_toPexpr___main(x_0, x_1, x_2, x_3);
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
obj* x_2; obj* x_4; obj* x_7; uint8 x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(x_4);
x_8 = l_RBNode_isRed___main___rarg(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::box(0);
x_10 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::box(0);
x_12 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = l_RBNode_setBlack___main___rarg(x_12);
return x_13;
}
}
}
}
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = l_Lean_Elaborator_toLevel___main___closed__4;
x_11 = l_Lean_Elaborator_OrderedRBMap_ofList___rarg(x_10, x_8);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
x_14 = l_Lean_Elaborator_OrderedRBMap_ofList___rarg(x_10, x_12);
x_15 = lean::cnstr_get(x_0, 4);
lean::inc(x_15);
x_17 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__3(x_15);
x_18 = lean::cnstr_get(x_1, 6);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 7);
lean::inc(x_20);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_0, 5);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_11);
lean::cnstr_set(x_26, 4, x_14);
lean::cnstr_set(x_26, 5, x_17);
lean::cnstr_set(x_26, 6, x_18);
lean::cnstr_set(x_26, 7, x_20);
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
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
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
lean::inc(x_94);
x_96 = lean::cnstr_get(x_53, 1);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_53, 2);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_53, 3);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_53, 4);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_53, 5);
lean::inc(x_104);
x_106 = l_List_append___rarg(x_91, x_104);
x_107 = lean::cnstr_get(x_53, 6);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_53, 7);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_53, 8);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_53, 9);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_53, 10);
lean::inc(x_115);
lean::dec(x_53);
x_118 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_118, 0, x_94);
lean::cnstr_set(x_118, 1, x_96);
lean::cnstr_set(x_118, 2, x_98);
lean::cnstr_set(x_118, 3, x_100);
lean::cnstr_set(x_118, 4, x_102);
lean::cnstr_set(x_118, 5, x_106);
lean::cnstr_set(x_118, 6, x_107);
lean::cnstr_set(x_118, 7, x_109);
lean::cnstr_set(x_118, 8, x_111);
lean::cnstr_set(x_118, 9, x_113);
lean::cnstr_set(x_118, 10, x_115);
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
obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_161; obj* x_163; obj* x_165; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
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
lean::inc(x_144);
x_146 = lean::cnstr_get(x_141, 1);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_141, 2);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_141, 3);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_141, 4);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_141, 5);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_141, 6);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_141, 7);
lean::inc(x_158);
lean::dec(x_141);
x_161 = lean::cnstr_get(x_126, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_126, 1);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_126, 6);
lean::inc(x_165);
lean::dec(x_126);
x_168 = l_List_append___rarg(x_123, x_154);
x_169 = lean::alloc_cnstr(0, 11, 0);
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toPexpr), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_9 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_7, x_1, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
x_15 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_22 = x_15;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_23, 2);
lean::inc(x_26);
lean::dec(x_23);
x_29 = l_Lean_Expr_mkCapp(x_26, x_18);
if (lean::is_scalar(x_22)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_22;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_20);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___lambda__1), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_15; 
x_4 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_0);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = l_Lean_Elaborator_toPexpr___main(x_12, x_1, x_2, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_10);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_20 = x_15;
} else {
 lean::inc(x_18);
 lean::dec(x_15);
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; uint8 x_31; obj* x_33; obj* x_34; obj* x_35; 
x_22 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_24 = x_15;
} else {
 lean::inc(x_22);
 lean::dec(x_15);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_22, 0);
x_27 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = l_Lean_Elaborator_mangleIdent(x_10);
x_31 = lean::unbox(x_7);
lean::inc(x_30);
x_33 = lean_expr_local(x_30, x_30, x_25, x_31);
if (lean::is_scalar(x_29)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_29;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
if (lean::is_scalar(x_24)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_24;
}
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___lambda__1), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_2);
x_9 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_5, x_2, x_3, x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
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
obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_29; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::cnstr_get(x_18, 0);
x_23 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 lean::cnstr_set(x_18, 1, lean::box(0));
 x_25 = x_18;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_18);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_0, 3);
lean::inc(x_26);
lean::dec(x_0);
x_29 = l_Lean_Elaborator_toPexpr___main(x_26, x_2, x_3, x_23);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_25);
lean::dec(x_1);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_35 = x_29;
} else {
 lean::inc(x_33);
 lean::dec(x_29);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_37 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_39 = x_29;
} else {
 lean::inc(x_37);
 lean::dec(x_29);
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
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_21);
lean::cnstr_set(x_45, 1, x_40);
if (lean::is_scalar(x_25)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_25;
}
lean::cnstr_set(x_46, 0, x_1);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
if (lean::is_scalar(x_39)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_39;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
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
x_9 = l_Lean_Elaborator_toLevel___main___closed__4;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_10);
x_14 = l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__3(x_8, x_13);
x_15 = lean::cnstr_get(x_1, 4);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 5);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 6);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 7);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 8);
lean::inc(x_23);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_4);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_14);
lean::cnstr_set(x_26, 4, x_15);
lean::cnstr_set(x_26, 5, x_17);
lean::cnstr_set(x_26, 6, x_19);
lean::cnstr_set(x_26, 7, x_21);
lean::cnstr_set(x_26, 8, x_23);
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
lean::dec(x_4);
lean::dec(x_16);
return x_18;
}
else
{
obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_32; obj* x_37; 
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 2);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_2, 4);
lean::inc(x_26);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_7, 1);
lean::inc(x_29);
lean::dec(x_7);
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
lean::dec(x_9);
lean::inc(x_5);
lean::inc(x_4);
x_37 = l_Lean_Elaborator_declModifiersToPexpr(x_1, x_4, x_5, x_6);
if (lean::obj_tag(x_37) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_5);
lean::dec(x_29);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_26);
x_47 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_49 = x_37;
} else {
 lean::inc(x_47);
 lean::dec(x_37);
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
obj* x_51; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_51 = lean::cnstr_get(x_37, 0);
lean::inc(x_51);
lean::dec(x_37);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::box(0);
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_3);
x_61 = lean_expr_mk_lit(x_60);
if (lean::obj_tag(x_22) == 0)
{
obj* x_65; obj* x_69; 
x_65 = l_Lean_Expander_getOptType___main(x_29);
lean::dec(x_29);
lean::inc(x_5);
lean::inc(x_4);
x_69 = l_Lean_Elaborator_toPexpr___main(x_65, x_4, x_5, x_56);
if (lean::obj_tag(x_69) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_5);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_24);
lean::dec(x_26);
lean::dec(x_61);
lean::dec(x_54);
x_78 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 x_80 = x_69;
} else {
 lean::inc(x_78);
 lean::dec(x_69);
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
x_82 = lean::cnstr_get(x_69, 0);
lean::inc(x_82);
lean::dec(x_69);
x_62 = x_59;
x_63 = x_82;
goto lbl_64;
}
}
else
{
obj* x_85; obj* x_89; obj* x_91; 
x_85 = lean::cnstr_get(x_22, 0);
lean::inc(x_85);
lean::dec(x_22);
lean::inc(x_85);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_89, 0, x_85);
lean::inc(x_5);
x_91 = l_Lean_Elaborator_modifyCurrentScope(x_89, x_4, x_5, x_56);
if (lean::obj_tag(x_91) == 0)
{
obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_5);
lean::dec(x_29);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_85);
lean::dec(x_24);
lean::dec(x_26);
lean::dec(x_61);
lean::dec(x_54);
x_102 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_104 = x_91;
} else {
 lean::inc(x_102);
 lean::dec(x_91);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
return x_105;
}
else
{
obj* x_106; obj* x_109; obj* x_112; obj* x_116; 
x_106 = lean::cnstr_get(x_91, 0);
lean::inc(x_106);
lean::dec(x_91);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
x_112 = l_Lean_Expander_getOptType___main(x_29);
lean::dec(x_29);
lean::inc(x_5);
lean::inc(x_4);
x_116 = l_Lean_Elaborator_toPexpr___main(x_112, x_4, x_5, x_109);
if (lean::obj_tag(x_116) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_5);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_85);
lean::dec(x_24);
lean::dec(x_26);
lean::dec(x_61);
lean::dec(x_54);
x_126 = lean::cnstr_get(x_116, 0);
if (lean::is_exclusive(x_116)) {
 x_128 = x_116;
} else {
 lean::inc(x_126);
 lean::dec(x_116);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_133; obj* x_136; 
x_130 = lean::cnstr_get(x_116, 0);
lean::inc(x_130);
lean::dec(x_116);
x_133 = lean::cnstr_get(x_85, 1);
lean::inc(x_133);
lean::dec(x_85);
x_136 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_133);
x_62 = x_136;
x_63 = x_130;
goto lbl_64;
}
}
}
lbl_64:
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_143; obj* x_146; uint8 x_147; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_137 = lean::cnstr_get(x_63, 0);
x_139 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_141 = x_63;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_63);
 x_141 = lean::box(0);
}
x_142 = l_Lean_Elaborator_namesToPexpr(x_62);
x_143 = lean::cnstr_get(x_24, 0);
lean::inc(x_143);
lean::dec(x_24);
x_146 = l_Lean_Elaborator_mangleIdent(x_143);
x_147 = 4;
lean::inc(x_137);
lean::inc(x_146);
lean::inc(x_146);
x_151 = lean_expr_local(x_146, x_146, x_137, x_147);
x_152 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_59);
x_153 = l_Lean_Elaborator_mkEqns___closed__1;
x_154 = l_Lean_Expr_mkCapp(x_153, x_152);
switch (lean::obj_tag(x_26)) {
case 0:
{
obj* x_160; obj* x_163; obj* x_168; 
lean::dec(x_146);
lean::dec(x_141);
lean::dec(x_137);
x_160 = lean::cnstr_get(x_26, 0);
lean::inc(x_160);
lean::dec(x_26);
x_163 = lean::cnstr_get(x_160, 1);
lean::inc(x_163);
lean::dec(x_160);
lean::inc(x_5);
lean::inc(x_4);
x_168 = l_Lean_Elaborator_toPexpr___main(x_163, x_4, x_5, x_139);
if (lean::obj_tag(x_168) == 0)
{
obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_5);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_61);
lean::dec(x_54);
lean::dec(x_154);
lean::dec(x_142);
x_177 = lean::cnstr_get(x_168, 0);
if (lean::is_exclusive(x_168)) {
 x_179 = x_168;
} else {
 lean::inc(x_177);
 lean::dec(x_168);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
return x_180;
}
else
{
obj* x_181; 
x_181 = lean::cnstr_get(x_168, 0);
lean::inc(x_181);
lean::dec(x_168);
x_155 = x_181;
goto lbl_156;
}
}
case 1:
{
obj* x_186; obj* x_187; 
lean::dec(x_26);
lean::dec(x_146);
x_186 = l_Lean_Elaborator_mkEqns(x_137, x_59);
if (lean::is_scalar(x_141)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_141;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_139);
x_155 = x_187;
goto lbl_156;
}
default:
{
obj* x_189; obj* x_194; 
lean::dec(x_141);
x_189 = lean::cnstr_get(x_26, 0);
lean::inc(x_189);
lean::dec(x_26);
lean::inc(x_5);
lean::inc(x_4);
x_194 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_146, x_189, x_4, x_5, x_139);
if (lean::obj_tag(x_194) == 0)
{
obj* x_204; obj* x_206; obj* x_207; 
lean::dec(x_5);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_61);
lean::dec(x_54);
lean::dec(x_154);
lean::dec(x_142);
lean::dec(x_137);
x_204 = lean::cnstr_get(x_194, 0);
if (lean::is_exclusive(x_194)) {
 x_206 = x_194;
} else {
 lean::inc(x_204);
 lean::dec(x_194);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_204);
return x_207;
}
else
{
obj* x_208; obj* x_211; obj* x_213; obj* x_215; obj* x_216; obj* x_217; 
x_208 = lean::cnstr_get(x_194, 0);
lean::inc(x_208);
lean::dec(x_194);
x_211 = lean::cnstr_get(x_208, 0);
x_213 = lean::cnstr_get(x_208, 1);
if (lean::is_exclusive(x_208)) {
 x_215 = x_208;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::dec(x_208);
 x_215 = lean::box(0);
}
x_216 = l_Lean_Elaborator_mkEqns(x_137, x_211);
if (lean::is_scalar(x_215)) {
 x_217 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_217 = x_215;
}
lean::cnstr_set(x_217, 0, x_216);
lean::cnstr_set(x_217, 1, x_213);
x_155 = x_217;
goto lbl_156;
}
}
}
lbl_156:
{
obj* x_218; obj* x_220; obj* x_225; 
x_218 = lean::cnstr_get(x_155, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_155, 1);
lean::inc(x_220);
lean::dec(x_155);
lean::inc(x_5);
lean::inc(x_4);
x_225 = l_Lean_Elaborator_simpleBindersToPexpr(x_32, x_4, x_5, x_220);
if (lean::obj_tag(x_225) == 0)
{
obj* x_234; obj* x_236; obj* x_237; 
lean::dec(x_218);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_61);
lean::dec(x_54);
lean::dec(x_154);
lean::dec(x_142);
x_234 = lean::cnstr_get(x_225, 0);
if (lean::is_exclusive(x_225)) {
 x_236 = x_225;
} else {
 lean::inc(x_234);
 lean::dec(x_225);
 x_236 = lean::box(0);
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_234);
return x_237;
}
else
{
obj* x_238; obj* x_241; obj* x_243; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_238 = lean::cnstr_get(x_225, 0);
lean::inc(x_238);
lean::dec(x_225);
x_241 = lean::cnstr_get(x_238, 0);
lean::inc(x_241);
x_243 = lean::cnstr_get(x_238, 1);
lean::inc(x_243);
lean::dec(x_238);
x_246 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_246, 0, x_218);
lean::cnstr_set(x_246, 1, x_59);
x_247 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_247, 0, x_241);
lean::cnstr_set(x_247, 1, x_246);
x_248 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_248, 0, x_154);
lean::cnstr_set(x_248, 1, x_247);
x_249 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_249, 0, x_142);
lean::cnstr_set(x_249, 1, x_248);
x_250 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_250, 0, x_61);
lean::cnstr_set(x_250, 1, x_249);
x_251 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_251, 0, x_54);
lean::cnstr_set(x_251, 1, x_250);
x_252 = l_Lean_Expr_mkCapp(x_153, x_251);
x_253 = l_Lean_Elaborator_elabDefLike___closed__2;
x_254 = lean_expr_mk_mdata(x_253, x_252);
x_255 = l_Lean_Elaborator_oldElabCommand(x_0, x_254, x_4, x_5, x_243);
lean::dec(x_4);
lean::dec(x_0);
return x_255;
}
}
}
}
}
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
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("Declaration.elaborate: unexpected input");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_1);
x_13 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
x_14 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_12, x_13, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_12);
return x_14;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
lean::dec(x_7);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; 
x_21 = lean::cnstr_get(x_5, 1);
lean::inc(x_21);
lean::dec(x_5);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_1);
x_26 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
x_27 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_25, x_26, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_25);
return x_27;
}
else
{
obj* x_32; obj* x_35; obj* x_38; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_21, 0);
lean::inc(x_32);
lean::dec(x_21);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_38 = l_Lean_Elaborator_toPexpr___main(x_35, x_2, x_3, x_4);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_0);
x_40 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_42 = x_38;
} else {
 lean::inc(x_40);
 lean::dec(x_38);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_55; uint8 x_56; obj* x_58; obj* x_59; obj* x_60; 
x_44 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_44, 0);
x_49 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_0, 1);
lean::inc(x_52);
lean::dec(x_0);
x_55 = l_Lean_Elaborator_mangleIdent(x_52);
x_56 = 0;
lean::inc(x_55);
x_58 = lean_expr_local(x_55, x_55, x_47, x_56);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_49);
if (lean::is_scalar(x_46)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_46;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_0);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_1);
x_65 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
x_66 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_64, x_65, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_64);
return x_66;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_20; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_0);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_2, x_3, x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
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
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(x_0, x_12, x_2, x_3, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_39 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = lean::apply_1(x_32, x_46);
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_48);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(obj* x_0) {
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
x_12 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(x_4);
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_20; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toPexpr), 4, 1);
lean::closure_set(x_16, 0, x_13);
x_17 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_20 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_17, x_16, x_1, x_2, x_3);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_26 = x_20;
} else {
 lean::inc(x_24);
 lean::dec(x_20);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_10, x_1, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_31);
x_38 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_40 = x_36;
} else {
 lean::inc(x_38);
 lean::dec(x_36);
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
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_42 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_44 = x_36;
} else {
 lean::inc(x_42);
 lean::dec(x_36);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_42, 0);
x_47 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_49 = x_42;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_42);
 x_49 = lean::box(0);
}
x_50 = lean::apply_1(x_31, x_45);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
if (lean::is_scalar(x_44)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_44;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_16; obj* x_18; 
lean::dec(x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_2);
x_16 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
lean::inc(x_4);
x_18 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_15, x_16, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
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
obj* x_28; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_6 = x_28;
goto lbl_7;
}
}
else
{
obj* x_32; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_2);
x_32 = lean::cnstr_get(x_11, 0);
lean::inc(x_32);
lean::dec(x_11);
x_35 = 0;
x_36 = lean::box(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_5);
x_6 = x_38;
goto lbl_7;
}
}
case 1:
{
obj* x_40; obj* x_43; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_2);
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = 1;
x_47 = lean::box(x_46);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_43);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_5);
x_6 = x_49;
goto lbl_7;
}
case 2:
{
obj* x_51; obj* x_54; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_2);
x_51 = lean::cnstr_get(x_1, 0);
lean::inc(x_51);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
x_57 = 2;
x_58 = lean::box(x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_54);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_5);
x_6 = x_60;
goto lbl_7;
}
default:
{
obj* x_62; obj* x_65; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_2);
x_62 = lean::cnstr_get(x_1, 0);
lean::inc(x_62);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = 3;
x_69 = lean::box(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
x_6 = x_71;
goto lbl_7;
}
}
lbl_7:
{
obj* x_72; obj* x_74; obj* x_77; obj* x_79; obj* x_82; obj* x_84; obj* x_87; obj* x_89; 
x_72 = lean::cnstr_get(x_6, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_6, 1);
lean::inc(x_74);
lean::dec(x_6);
x_77 = lean::cnstr_get(x_72, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_72, 1);
lean::inc(x_79);
lean::dec(x_72);
x_82 = lean::cnstr_get(x_79, 2);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_82, 1);
lean::inc(x_84);
lean::dec(x_82);
x_87 = l_Lean_Expander_getOptType___main(x_84);
lean::dec(x_84);
x_89 = l_Lean_Elaborator_toPexpr___main(x_87, x_3, x_4, x_74);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; obj* x_95; obj* x_96; 
lean::dec(x_0);
lean::dec(x_79);
lean::dec(x_77);
x_93 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_95 = x_89;
} else {
 lean::inc(x_93);
 lean::dec(x_89);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
return x_96;
}
else
{
obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; uint8 x_106; obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_117; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_97 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_99 = x_89;
} else {
 lean::inc(x_97);
 lean::dec(x_89);
 x_99 = lean::box(0);
}
x_100 = lean::cnstr_get(x_97, 0);
x_102 = lean::cnstr_get(x_97, 1);
if (lean::is_exclusive(x_97)) {
 x_104 = x_97;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_97);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Elaborator_dummy;
x_106 = lean::unbox(x_77);
lean::inc(x_0);
lean::inc(x_0);
x_109 = lean_expr_local(x_0, x_0, x_105, x_106);
x_110 = lean::cnstr_get(x_79, 0);
lean::inc(x_110);
x_112 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_110);
x_113 = l_Lean_Elaborator_namesToPexpr(x_112);
x_114 = lean::cnstr_get(x_79, 1);
lean::inc(x_114);
lean::dec(x_79);
x_117 = l_Lean_Elaborator_inferModToPexpr(x_114);
lean::dec(x_114);
x_119 = lean::box(0);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_100);
lean::cnstr_set(x_120, 1, x_119);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set(x_121, 1, x_120);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_113);
lean::cnstr_set(x_122, 1, x_121);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_109);
lean::cnstr_set(x_123, 1, x_122);
x_124 = l_Lean_Expr_mkCapp(x_0, x_123);
if (lean::is_scalar(x_104)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_104;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_102);
if (lean::is_scalar(x_99)) {
 x_126 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_126 = x_99;
}
lean::cnstr_set(x_126, 0, x_125);
return x_126;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::box(0);
x_9 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_8, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_9;
}
else
{
obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_23; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
lean::inc(x_0);
lean::inc(x_1);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5___lambda__1), 6, 3);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_12);
lean::closure_set(x_19, 2, x_0);
x_20 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_23 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_20, x_19, x_3, x_4, x_5);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_31 = x_23;
} else {
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_38; obj* x_41; 
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_0, x_1, x_14, x_3, x_4, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_36);
x_43 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_45 = x_41;
} else {
 lean::inc(x_43);
 lean::dec(x_41);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
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
x_55 = lean::apply_1(x_36, x_50);
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_52);
if (lean::is_scalar(x_49)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_49;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
}
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_14; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_6);
x_14 = l_Lean_Elaborator_toPexpr___main(x_9, x_6, x_7, x_8);
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_21);
 lean::dec(x_14);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
lean::dec(x_14);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_Lean_Elaborator_identUnivParamsToPexpr(x_1);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_28);
lean::cnstr_set(x_34, 1, x_2);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_5);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Elaborator_mkEqns___closed__1;
x_38 = l_Lean_Expr_mkCapp(x_37, x_36);
x_39 = lean_expr_mk_mdata(x_3, x_38);
x_40 = l_Lean_Elaborator_oldElabCommand(x_4, x_39, x_6, x_7, x_30);
lean::dec(x_6);
return x_40;
}
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
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
obj* x_22; 
lean::inc(x_11);
lean::inc(x_10);
x_22 = l_Lean_Elaborator_attrsToPexpr(x_13, x_10, x_11, x_12);
if (lean::obj_tag(x_22) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
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
obj* x_37; obj* x_40; obj* x_42; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_37 = lean::cnstr_get(x_22, 0);
lean::inc(x_37);
lean::dec(x_22);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
lean::inc(x_0);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_40);
lean::cnstr_set(x_46, 1, x_0);
x_47 = l_Lean_Elaborator_mkEqns___closed__1;
x_48 = l_Lean_Expr_mkCapp(x_47, x_46);
if (lean::obj_tag(x_6) == 0)
{
obj* x_52; obj* x_55; 
x_52 = l_Lean_Expander_getOptType___main(x_7);
lean::inc(x_11);
lean::inc(x_10);
x_55 = l_Lean_Elaborator_toPexpr___main(x_52, x_10, x_11, x_42);
if (lean::obj_tag(x_55) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_48);
x_66 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_68 = x_55;
} else {
 lean::inc(x_66);
 lean::dec(x_55);
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
obj* x_70; 
x_70 = lean::cnstr_get(x_55, 0);
lean::inc(x_70);
lean::dec(x_55);
lean::inc(x_0);
x_49 = x_0;
x_50 = x_70;
goto lbl_51;
}
}
else
{
obj* x_74; obj* x_78; obj* x_80; 
x_74 = lean::cnstr_get(x_6, 0);
lean::inc(x_74);
lean::dec(x_6);
lean::inc(x_74);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_78, 0, x_74);
lean::inc(x_11);
x_80 = l_Lean_Elaborator_modifyCurrentScope(x_78, x_10, x_11, x_42);
if (lean::obj_tag(x_80) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_74);
lean::dec(x_48);
x_92 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_94 = x_80;
} else {
 lean::inc(x_92);
 lean::dec(x_80);
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
obj* x_96; obj* x_99; obj* x_102; obj* x_105; 
x_96 = lean::cnstr_get(x_80, 0);
lean::inc(x_96);
lean::dec(x_80);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
x_102 = l_Lean_Expander_getOptType___main(x_7);
lean::inc(x_11);
lean::inc(x_10);
x_105 = l_Lean_Elaborator_toPexpr___main(x_102, x_10, x_11, x_99);
if (lean::obj_tag(x_105) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_74);
lean::dec(x_48);
x_117 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_119 = x_105;
} else {
 lean::inc(x_117);
 lean::dec(x_105);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
return x_120;
}
else
{
obj* x_121; obj* x_124; obj* x_127; 
x_121 = lean::cnstr_get(x_105, 0);
lean::inc(x_121);
lean::dec(x_105);
x_124 = lean::cnstr_get(x_74, 1);
lean::inc(x_124);
lean::dec(x_74);
x_127 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_124);
x_49 = x_127;
x_50 = x_121;
goto lbl_51;
}
}
}
lbl_51:
{
obj* x_128; obj* x_130; obj* x_135; 
x_128 = lean::cnstr_get(x_50, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_50, 1);
lean::inc(x_130);
lean::dec(x_50);
lean::inc(x_11);
lean::inc(x_10);
x_135 = l_Lean_Elaborator_simpleBindersToPexpr(x_1, x_10, x_11, x_130);
if (lean::obj_tag(x_135) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_48);
lean::dec(x_128);
lean::dec(x_49);
x_147 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_149 = x_135;
} else {
 lean::inc(x_147);
 lean::dec(x_135);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
return x_150;
}
else
{
obj* x_151; obj* x_154; obj* x_156; obj* x_163; 
x_151 = lean::cnstr_get(x_135, 0);
lean::inc(x_151);
lean::dec(x_135);
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_151, 1);
lean::inc(x_156);
lean::dec(x_151);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_2);
x_163 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(x_2, x_3, x_10, x_11, x_156);
if (lean::obj_tag(x_163) == 0)
{
obj* x_176; obj* x_178; obj* x_179; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_48);
lean::dec(x_154);
lean::dec(x_128);
lean::dec(x_49);
x_176 = lean::cnstr_get(x_163, 0);
if (lean::is_exclusive(x_163)) {
 x_178 = x_163;
} else {
 lean::inc(x_176);
 lean::dec(x_163);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
return x_179;
}
else
{
obj* x_180; obj* x_183; obj* x_185; obj* x_188; obj* x_189; obj* x_192; uint8 x_193; obj* x_195; obj* x_197; obj* x_198; obj* x_199; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
x_180 = lean::cnstr_get(x_163, 0);
lean::inc(x_180);
lean::dec(x_163);
x_183 = lean::cnstr_get(x_180, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_180, 1);
lean::inc(x_185);
lean::dec(x_180);
x_188 = l_Lean_Elaborator_namesToPexpr(x_49);
x_189 = lean::cnstr_get(x_4, 0);
lean::inc(x_189);
lean::dec(x_4);
x_192 = l_Lean_Elaborator_mangleIdent(x_189);
x_193 = 0;
lean::inc(x_192);
x_195 = lean_expr_local(x_192, x_192, x_128, x_193);
lean::inc(x_0);
x_197 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_197, 0, x_195);
lean::cnstr_set(x_197, 1, x_0);
x_198 = l_Lean_Expr_mkCapp(x_47, x_197);
x_199 = l_Lean_Expr_mkCapp(x_47, x_183);
lean::inc(x_0);
x_201 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_201, 0, x_199);
lean::cnstr_set(x_201, 1, x_0);
x_202 = l_Lean_Expr_mkCapp(x_47, x_201);
x_203 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(x_3);
x_204 = l_Lean_Expr_mkCapp(x_47, x_203);
lean::inc(x_0);
x_206 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_206, 0, x_204);
lean::cnstr_set(x_206, 1, x_0);
x_207 = l_Lean_Expr_mkCapp(x_47, x_206);
x_208 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_0);
x_209 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_209, 0, x_202);
lean::cnstr_set(x_209, 1, x_208);
x_210 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_210, 0, x_154);
lean::cnstr_set(x_210, 1, x_209);
x_211 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_211, 0, x_198);
lean::cnstr_set(x_211, 1, x_210);
x_212 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_212, 0, x_188);
lean::cnstr_set(x_212, 1, x_211);
x_213 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_213, 0, x_48);
lean::cnstr_set(x_213, 1, x_212);
x_214 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_214, 0, x_9);
lean::cnstr_set(x_214, 1, x_213);
x_215 = l_Lean_Expr_mkCapp(x_47, x_214);
x_216 = lean_expr_mk_mdata(x_5, x_215);
x_217 = l_Lean_Elaborator_oldElabCommand(x_2, x_216, x_10, x_11, x_185);
lean::dec(x_10);
lean::dec(x_2);
return x_217;
}
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_inferModToPexpr(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("mk");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; obj* x_15; 
if (lean::obj_tag(x_8) == 0)
{
obj* x_17; obj* x_20; 
x_17 = l_Lean_Expander_getOptType___main(x_9);
lean::inc(x_12);
lean::inc(x_11);
x_20 = l_Lean_Elaborator_toPexpr___main(x_17, x_11, x_12, x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_33 = x_20;
} else {
 lean::inc(x_31);
 lean::dec(x_20);
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
obj* x_35; 
x_35 = lean::cnstr_get(x_20, 0);
lean::inc(x_35);
lean::dec(x_20);
lean::inc(x_5);
x_14 = x_5;
x_15 = x_35;
goto lbl_16;
}
}
else
{
obj* x_39; obj* x_43; obj* x_45; 
x_39 = lean::cnstr_get(x_8, 0);
lean::inc(x_39);
lean::dec(x_8);
lean::inc(x_39);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_43, 0, x_39);
lean::inc(x_12);
x_45 = l_Lean_Elaborator_modifyCurrentScope(x_43, x_11, x_12, x_13);
if (lean::obj_tag(x_45) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_39);
x_57 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_59 = x_45;
} else {
 lean::inc(x_57);
 lean::dec(x_45);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_57);
return x_60;
}
else
{
obj* x_61; obj* x_64; obj* x_67; obj* x_70; 
x_61 = lean::cnstr_get(x_45, 0);
lean::inc(x_61);
lean::dec(x_45);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Expander_getOptType___main(x_9);
lean::inc(x_12);
lean::inc(x_11);
x_70 = l_Lean_Elaborator_toPexpr___main(x_67, x_11, x_12, x_64);
if (lean::obj_tag(x_70) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_39);
x_82 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_84 = x_70;
} else {
 lean::inc(x_82);
 lean::dec(x_70);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
return x_85;
}
else
{
obj* x_86; obj* x_89; obj* x_92; 
x_86 = lean::cnstr_get(x_70, 0);
lean::inc(x_86);
lean::dec(x_70);
x_89 = lean::cnstr_get(x_39, 1);
lean::inc(x_89);
lean::dec(x_39);
x_92 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_89);
x_14 = x_92;
x_15 = x_86;
goto lbl_16;
}
}
}
lbl_16:
{
obj* x_93; obj* x_95; obj* x_100; 
x_93 = lean::cnstr_get(x_15, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_15, 1);
lean::inc(x_95);
lean::dec(x_15);
lean::inc(x_12);
lean::inc(x_11);
x_100 = l_Lean_Elaborator_simpleBindersToPexpr(x_0, x_11, x_12, x_95);
if (lean::obj_tag(x_100) == 0)
{
obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_14);
lean::dec(x_93);
x_112 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_114 = x_100;
} else {
 lean::inc(x_112);
 lean::dec(x_100);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
return x_115;
}
else
{
obj* x_116; obj* x_119; obj* x_121; obj* x_124; obj* x_125; obj* x_128; obj* x_129; uint8 x_130; obj* x_132; obj* x_133; 
x_116 = lean::cnstr_get(x_100, 0);
lean::inc(x_116);
lean::dec(x_100);
x_119 = lean::cnstr_get(x_116, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
lean::dec(x_116);
x_124 = l_Lean_Elaborator_namesToPexpr(x_14);
x_125 = lean::cnstr_get(x_1, 0);
lean::inc(x_125);
lean::dec(x_1);
x_128 = l_Lean_Elaborator_mangleIdent(x_125);
x_129 = l_Lean_Elaborator_dummy;
x_130 = 0;
lean::inc(x_128);
x_132 = lean_expr_local(x_128, x_128, x_129, x_130);
if (lean::obj_tag(x_7) == 0)
{
lean::inc(x_5);
x_133 = x_5;
goto lbl_134;
}
else
{
obj* x_136; obj* x_137; 
x_136 = lean::cnstr_get(x_7, 0);
x_137 = lean::cnstr_get(x_136, 1);
lean::inc(x_137);
x_133 = x_137;
goto lbl_134;
}
lbl_134:
{
obj* x_141; 
lean::inc(x_12);
lean::inc(x_11);
x_141 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_133, x_11, x_12, x_121);
if (lean::obj_tag(x_141) == 0)
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_124);
lean::dec(x_93);
lean::dec(x_119);
lean::dec(x_132);
x_154 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_156 = x_141;
} else {
 lean::inc(x_154);
 lean::dec(x_141);
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
obj* x_158; obj* x_161; obj* x_163; obj* x_166; obj* x_167; obj* x_171; obj* x_172; 
x_158 = lean::cnstr_get(x_141, 0);
lean::inc(x_158);
lean::dec(x_141);
x_161 = lean::cnstr_get(x_158, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_158, 1);
lean::inc(x_163);
lean::dec(x_158);
x_166 = l_Lean_Elaborator_mkEqns___closed__1;
x_167 = l_Lean_Expr_mkCapp(x_166, x_161);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_2);
x_171 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_2, x_166, x_3, x_11, x_12, x_163);
if (lean::obj_tag(x_4) == 0)
{
obj* x_174; 
x_174 = l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2;
x_172 = x_174;
goto lbl_173;
}
else
{
obj* x_175; obj* x_177; obj* x_180; 
x_175 = lean::cnstr_get(x_4, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_175, 0);
lean::inc(x_177);
lean::dec(x_175);
x_180 = l_Lean_Elaborator_mangleIdent(x_177);
x_172 = x_180;
goto lbl_173;
}
lbl_173:
{
obj* x_182; 
lean::inc(x_172);
x_182 = lean_expr_local(x_172, x_172, x_129, x_130);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_171) == 0)
{
obj* x_195; obj* x_197; obj* x_198; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_182);
lean::dec(x_167);
lean::dec(x_124);
lean::dec(x_93);
lean::dec(x_119);
lean::dec(x_132);
x_195 = lean::cnstr_get(x_171, 0);
if (lean::is_exclusive(x_171)) {
 x_197 = x_171;
} else {
 lean::inc(x_195);
 lean::dec(x_171);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_195);
return x_198;
}
else
{
obj* x_199; obj* x_202; obj* x_204; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_199 = lean::cnstr_get(x_171, 0);
lean::inc(x_199);
lean::dec(x_171);
x_202 = lean::cnstr_get(x_199, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_199, 1);
lean::inc(x_204);
lean::dec(x_199);
x_207 = l_Lean_Expr_mkCapp(x_166, x_202);
x_208 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_5);
x_209 = l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1;
x_210 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_208);
x_211 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_211, 0, x_182);
lean::cnstr_set(x_211, 1, x_210);
x_212 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_212, 0, x_93);
lean::cnstr_set(x_212, 1, x_211);
x_213 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_213, 0, x_167);
lean::cnstr_set(x_213, 1, x_212);
x_214 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_214, 0, x_119);
lean::cnstr_set(x_214, 1, x_213);
x_215 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_215, 0, x_132);
lean::cnstr_set(x_215, 1, x_214);
x_216 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_216, 0, x_124);
lean::cnstr_set(x_216, 1, x_215);
x_217 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_217, 0, x_10);
lean::cnstr_set(x_217, 1, x_216);
x_218 = l_Lean_Expr_mkCapp(x_166, x_217);
x_219 = lean_expr_mk_mdata(x_6, x_218);
x_220 = l_Lean_Elaborator_oldElabCommand(x_2, x_219, x_11, x_12, x_204);
lean::dec(x_11);
lean::dec(x_2);
return x_220;
}
}
else
{
if (lean::obj_tag(x_171) == 0)
{
obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_5);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_182);
lean::dec(x_167);
lean::dec(x_124);
lean::dec(x_93);
lean::dec(x_119);
lean::dec(x_132);
x_236 = lean::cnstr_get(x_171, 0);
if (lean::is_exclusive(x_171)) {
 x_238 = x_171;
} else {
 lean::inc(x_236);
 lean::dec(x_171);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
return x_239;
}
else
{
obj* x_240; obj* x_243; obj* x_246; obj* x_248; obj* x_251; obj* x_254; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
x_240 = lean::cnstr_get(x_171, 0);
lean::inc(x_240);
lean::dec(x_171);
x_243 = lean::cnstr_get(x_4, 0);
lean::inc(x_243);
lean::dec(x_4);
x_246 = lean::cnstr_get(x_240, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_240, 1);
lean::inc(x_248);
lean::dec(x_240);
x_251 = lean::cnstr_get(x_243, 1);
lean::inc(x_251);
lean::dec(x_243);
x_254 = l_Lean_Elaborator_inferModToPexpr(x_251);
lean::dec(x_251);
x_256 = l_Lean_Expr_mkCapp(x_166, x_246);
x_257 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_5);
x_258 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_258, 0, x_254);
lean::cnstr_set(x_258, 1, x_257);
x_259 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_259, 0, x_182);
lean::cnstr_set(x_259, 1, x_258);
x_260 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_260, 0, x_93);
lean::cnstr_set(x_260, 1, x_259);
x_261 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_261, 0, x_167);
lean::cnstr_set(x_261, 1, x_260);
x_262 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_262, 0, x_119);
lean::cnstr_set(x_262, 1, x_261);
x_263 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_263, 0, x_132);
lean::cnstr_set(x_263, 1, x_262);
x_264 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_264, 0, x_124);
lean::cnstr_set(x_264, 1, x_263);
x_265 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_265, 0, x_10);
lean::cnstr_set(x_265, 1, x_264);
x_266 = l_Lean_Expr_mkCapp(x_166, x_265);
x_267 = lean_expr_mk_mdata(x_6, x_266);
x_268 = l_Lean_Elaborator_oldElabCommand(x_2, x_267, x_11, x_12, x_248);
lean::dec(x_11);
lean::dec(x_2);
return x_268;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__1() {
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__2() {
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__3() {
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__4() {
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__5() {
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
obj* l_Lean_Elaborator_Declaration_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
x_6 = l_Lean_Parser_command_Declaration_HasView;
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
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_47, 2);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_56, 1);
lean::inc(x_60);
lean::dec(x_56);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_60);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_58);
lean::cnstr_set(x_64, 1, x_63);
if (lean::obj_tag(x_54) == 0)
{
obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_65 = lean::cnstr_get(x_47, 3);
lean::inc(x_65);
lean::dec(x_47);
x_68 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_69 = l_Lean_Elaborator_Declaration_elaborate___closed__2;
x_70 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_53);
lean::cnstr_set(x_70, 2, x_69);
lean::cnstr_set(x_70, 3, x_64);
lean::cnstr_set(x_70, 4, x_65);
x_71 = lean::mk_nat_obj(4ul);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_77 = lean::cnstr_get(x_54, 0);
lean::inc(x_77);
lean::dec(x_54);
x_80 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_81 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_53);
lean::cnstr_set(x_81, 2, x_77);
lean::cnstr_set(x_81, 3, x_64);
lean::cnstr_set(x_81, 4, x_74);
x_82 = lean::mk_nat_obj(4ul);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_104 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_105 = l_Lean_Elaborator_Declaration_elaborate___closed__2;
x_106 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_91);
lean::cnstr_set(x_106, 2, x_105);
lean::cnstr_set(x_106, 3, x_100);
lean::cnstr_set(x_106, 4, x_101);
x_107 = lean::mk_nat_obj(3ul);
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike), 7, 4);
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
x_135 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr), 4, 1);
lean::closure_set(x_135, 0, x_132);
x_136 = l_Lean_Elaborator_Declaration_elaborate___closed__3;
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed), 9, 5);
lean::closure_set(x_137, 0, x_128);
lean::closure_set(x_137, 1, x_125);
lean::closure_set(x_137, 2, x_131);
lean::closure_set(x_137, 3, x_136);
lean::closure_set(x_137, 4, x_0);
x_138 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
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
x_177 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr), 4, 1);
lean::closure_set(x_177, 0, x_173);
x_178 = l_Lean_Elaborator_Declaration_elaborate___closed__4;
x_179 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__2___boxed), 13, 9);
lean::closure_set(x_179, 0, x_172);
lean::closure_set(x_179, 1, x_169);
lean::closure_set(x_179, 2, x_0);
lean::closure_set(x_179, 3, x_163);
lean::closure_set(x_179, 4, x_161);
lean::closure_set(x_179, 5, x_178);
lean::closure_set(x_179, 6, x_159);
lean::closure_set(x_179, 7, x_166);
lean::closure_set(x_179, 8, x_173);
x_180 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
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
x_222 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr), 4, 1);
lean::closure_set(x_222, 0, x_219);
x_223 = l_Lean_Elaborator_Declaration_elaborate___closed__5;
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed), 14, 10);
lean::closure_set(x_224, 0, x_215);
lean::closure_set(x_224, 1, x_203);
lean::closure_set(x_224, 2, x_0);
lean::closure_set(x_224, 3, x_209);
lean::closure_set(x_224, 4, x_207);
lean::closure_set(x_224, 5, x_218);
lean::closure_set(x_224, 6, x_223);
lean::closure_set(x_224, 7, x_205);
lean::closure_set(x_224, 8, x_201);
lean::closure_set(x_224, 9, x_212);
x_225 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
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
x_233 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1;
x_234 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed), 5, 2);
lean::closure_set(x_234, 0, x_232);
lean::closure_set(x_234, 1, x_233);
x_235 = l_Lean_Elaborator_locally(x_234, x_1, x_2, x_3);
return x_235;
}
}
}
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Elaborator_Declaration_elaborate___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
return x_9;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; 
x_13 = l_Lean_Elaborator_Declaration_elaborate___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean::dec(x_7);
lean::dec(x_8);
return x_13;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
x_14 = l_Lean_Elaborator_Declaration_elaborate___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean::dec(x_7);
lean::dec(x_9);
return x_14;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_32; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 3);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_1);
x_20 = x_19;
x_21 = l_Lean_Elaborator_toLevel___main___closed__4;
x_22 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_21, x_12, x_2, x_20);
x_23 = lean::cnstr_get(x_3, 5);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_3, 6);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_3, 7);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 8);
lean::inc(x_29);
lean::dec(x_3);
x_32 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_6);
lean::cnstr_set(x_32, 2, x_8);
lean::cnstr_set(x_32, 3, x_10);
lean::cnstr_set(x_32, 4, x_22);
lean::cnstr_set(x_32, 5, x_23);
lean::cnstr_set(x_32, 6, x_25);
lean::cnstr_set(x_32, 7, x_27);
lean::cnstr_set(x_32, 8, x_29);
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
x_59 = l_Lean_Elaborator_toLevel___main___closed__4;
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
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_38; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
lean::inc(x_2);
lean::inc(x_1);
x_38 = l_Lean_Elaborator_simpleBindersToPexpr(x_31, x_1, x_2, x_33);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_42 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
lean::dec(x_46);
x_54 = l_Lean_Elaborator_variables_elaborate___closed__2;
x_55 = lean_expr_mk_mdata(x_54, x_49);
x_56 = l_Lean_Elaborator_oldElabCommand(x_0, x_55, x_1, x_2, x_51);
lean::dec(x_1);
lean::dec(x_0);
return x_56;
}
}
}
else
{
obj* x_59; obj* x_63; 
x_59 = lean::cnstr_get(x_10, 0);
lean::inc(x_59);
lean::dec(x_10);
lean::inc(x_2);
x_63 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__1(x_59, x_1, x_2, x_3);
if (lean::obj_tag(x_63) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_67 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_69 = x_63;
} else {
 lean::inc(x_67);
 lean::dec(x_63);
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
obj* x_71; obj* x_74; obj* x_76; obj* x_81; 
x_71 = lean::cnstr_get(x_63, 0);
lean::inc(x_71);
lean::dec(x_63);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
lean::dec(x_71);
lean::inc(x_2);
lean::inc(x_1);
x_81 = l_Lean_Elaborator_simpleBindersToPexpr(x_74, x_1, x_2, x_76);
if (lean::obj_tag(x_81) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_85 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_87 = x_81;
} else {
 lean::inc(x_85);
 lean::dec(x_81);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; obj* x_92; obj* x_94; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_81, 0);
lean::inc(x_89);
lean::dec(x_81);
x_92 = lean::cnstr_get(x_89, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_89, 1);
lean::inc(x_94);
lean::dec(x_89);
x_97 = l_Lean_Elaborator_variables_elaborate___closed__2;
x_98 = lean_expr_mk_mdata(x_97, x_92);
x_99 = l_Lean_Elaborator_oldElabCommand(x_0, x_98, x_1, x_2, x_94);
lean::dec(x_1);
lean::dec(x_0);
return x_99;
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
obj* l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; uint8 x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_Lean_Elaborator_mangleIdent(x_2);
x_8 = l_RBNode_isRed___main___rarg(x_0);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::box(0);
x_10 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_9);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::box(0);
x_13 = l_RBNode_ins___main___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_12);
x_14 = l_RBNode_setBlack___main___rarg(x_13);
x_0 = x_14;
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
x_17 = l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(x_12, x_14);
x_18 = lean::cnstr_get(x_1, 6);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 7);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_1, 8);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_17);
lean::cnstr_set(x_25, 6, x_18);
lean::cnstr_set(x_25, 7, x_20);
lean::cnstr_set(x_25, 8, x_22);
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
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_52; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_5, 3);
lean::inc(x_17);
lean::dec(x_5);
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
lean::dec(x_8);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::dec(x_23);
x_30 = lean::cnstr_get(x_20, 1);
lean::inc(x_30);
lean::dec(x_20);
x_33 = l_String_trim(x_30);
lean::dec(x_30);
x_35 = l_Lean_Elaborator_precToNat___main(x_17);
x_36 = lean::box(0);
lean::inc(x_33);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_33);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set(x_38, 2, x_36);
x_39 = lean::mk_nat_obj(0ul);
x_40 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_33, x_38, x_27, x_39);
lean::dec(x_33);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_25);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::cnstr_get(x_0, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_0, 3);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 4);
lean::inc(x_49);
lean::dec(x_0);
x_52 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_52, 0, x_42);
lean::cnstr_set(x_52, 1, x_43);
lean::cnstr_set(x_52, 2, x_45);
lean::cnstr_set(x_52, 3, x_47);
lean::cnstr_set(x_52, 4, x_49);
x_0 = x_52;
x_1 = x_14;
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
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
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
obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; 
lean::dec(x_26);
x_60 = lean::cnstr_get(x_2, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_2, 1);
lean::inc(x_62);
x_64 = lean::box(0);
x_65 = lean_name_mk_string(x_64, x_49);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_66, 0, x_0);
lean::closure_set(x_66, 1, x_52);
x_67 = l_Lean_Parser_TokenMap_insert___rarg(x_62, x_65, x_66);
x_68 = lean::cnstr_get(x_2, 2);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_2, 3);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_2, 4);
lean::inc(x_72);
lean::dec(x_2);
x_75 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_75, 0, x_60);
lean::cnstr_set(x_75, 1, x_67);
lean::cnstr_set(x_75, 2, x_68);
lean::cnstr_set(x_75, 3, x_70);
lean::cnstr_set(x_75, 4, x_72);
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
obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_96; obj* x_97; 
lean::dec(x_56);
x_78 = lean::cnstr_get(x_2, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_2, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 2);
lean::inc(x_82);
x_84 = lean::box(0);
x_85 = lean_name_mk_string(x_84, x_49);
x_86 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(x_52);
x_87 = l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
if (lean::is_scalar(x_26)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_26;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_86);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3), 8, 2);
lean::closure_set(x_89, 0, x_0);
lean::closure_set(x_89, 1, x_88);
x_90 = l_Lean_Parser_TokenMap_insert___rarg(x_82, x_85, x_89);
x_91 = lean::cnstr_get(x_2, 3);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_2, 4);
lean::inc(x_93);
lean::dec(x_2);
x_96 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_96, 0, x_78);
lean::cnstr_set(x_96, 1, x_80);
lean::cnstr_set(x_96, 2, x_90);
lean::cnstr_set(x_96, 3, x_91);
lean::cnstr_set(x_96, 4, x_93);
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
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_26);
x_103 = lean::cnstr_get(x_2, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_2, 1);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 2);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 3);
lean::inc(x_109);
x_111 = lean::box(0);
x_112 = lean_name_mk_string(x_111, x_49);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1), 7, 2);
lean::closure_set(x_113, 0, x_0);
lean::closure_set(x_113, 1, x_52);
x_114 = l_Lean_Parser_TokenMap_insert___rarg(x_109, x_112, x_113);
x_115 = lean::cnstr_get(x_2, 4);
lean::inc(x_115);
lean::dec(x_2);
x_118 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_118, 0, x_103);
lean::cnstr_set(x_118, 1, x_105);
lean::cnstr_set(x_118, 2, x_107);
lean::cnstr_set(x_118, 3, x_114);
lean::cnstr_set(x_118, 4, x_115);
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
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_99);
x_121 = lean::cnstr_get(x_2, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_2, 1);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_2, 2);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_2, 3);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_2, 4);
lean::inc(x_129);
lean::dec(x_2);
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
x_139 = lean::alloc_cnstr(0, 5, 0);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_28; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
lean::inc(x_1);
lean::inc(x_24);
x_28 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(x_22, x_24, x_0, x_1, x_17);
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_20);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
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
obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_48; obj* x_52; obj* x_53; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_2, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 2);
lean::inc(x_48);
lean::dec(x_15);
lean::inc(x_46);
x_52 = l_List_append___rarg(x_46, x_48);
x_53 = l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(x_41, x_52, x_0, x_1, x_43);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_2);
lean::dec(x_20);
lean::dec(x_24);
lean::dec(x_46);
x_58 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_60 = x_53;
} else {
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_62 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_64 = x_53;
} else {
 lean::inc(x_62);
 lean::dec(x_53);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 1);
 x_67 = x_62;
} else {
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_2, 2);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_2, 3);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_2, 4);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_2, 5);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_20, 1);
lean::inc(x_76);
lean::dec(x_20);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_65);
lean::cnstr_set(x_79, 1, x_76);
x_80 = lean::cnstr_get(x_2, 7);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_2, 8);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_2, 9);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_2, 10);
lean::inc(x_86);
lean::dec(x_2);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_24);
lean::cnstr_set(x_89, 1, x_46);
lean::cnstr_set(x_89, 2, x_68);
lean::cnstr_set(x_89, 3, x_70);
lean::cnstr_set(x_89, 4, x_72);
lean::cnstr_set(x_89, 5, x_74);
lean::cnstr_set(x_89, 6, x_79);
lean::cnstr_set(x_89, 7, x_80);
lean::cnstr_set(x_89, 8, x_82);
lean::cnstr_set(x_89, 9, x_84);
lean::cnstr_set(x_89, 10, x_86);
x_90 = lean::box(0);
if (lean::is_scalar(x_67)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_67;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
if (lean::is_scalar(x_64)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_64;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
x_4 = l_Lean_Parser_command_reserveNotation_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::apply_1(x_5, x_0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_Lean_Elaborator_postprocessNotationSpec(x_13);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::cnstr_get(x_3, 0);
lean::inc(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_3, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_3, 3);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_3, 4);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_3, 5);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_3, 6);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_3, 7);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_3, 8);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_3, 9);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_3, 10);
lean::inc(x_39);
lean::dec(x_3);
x_42 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_42, 0, x_20);
lean::cnstr_set(x_42, 1, x_21);
lean::cnstr_set(x_42, 2, x_23);
lean::cnstr_set(x_42, 3, x_25);
lean::cnstr_set(x_42, 4, x_27);
lean::cnstr_set(x_42, 5, x_29);
lean::cnstr_set(x_42, 6, x_31);
lean::cnstr_set(x_42, 7, x_33);
lean::cnstr_set(x_42, 8, x_35);
lean::cnstr_set(x_42, 9, x_37);
lean::cnstr_set(x_42, 10, x_39);
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
obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_32; 
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
lean::inc(x_28);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_25);
x_39 = lean::box(0);
x_7 = x_39;
goto lbl_8;
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_48; obj* x_50; obj* x_53; uint8 x_55; 
x_40 = lean::cnstr_get(x_28, 3);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_set(x_32, 0, lean::box(0));
 x_44 = x_32;
} else {
 lean::inc(x_42);
 lean::dec(x_32);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_25, 1);
lean::inc(x_45);
lean::dec(x_25);
x_48 = l_String_trim(x_45);
lean::dec(x_45);
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
lean::dec(x_42);
x_53 = l_String_trim(x_50);
lean::dec(x_50);
x_55 = lean::string_dec_eq(x_48, x_53);
lean::dec(x_53);
lean::dec(x_48);
if (x_55 == 0)
{
obj* x_64; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_40);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_44);
x_64 = lean::box(0);
x_7 = x_64;
goto lbl_8;
}
else
{
uint8 x_65; 
x_65 = l_Lean_Elaborator_matchPrecedence___main(x_22, x_40);
if (x_65 == 0)
{
obj* x_70; 
lean::dec(x_28);
lean::dec(x_9);
lean::dec(x_19);
lean::dec(x_44);
x_70 = lean::box(0);
x_7 = x_70;
goto lbl_8;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_9, 1);
lean::inc(x_71);
lean::dec(x_9);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; 
x_74 = lean::cnstr_get(x_19, 1);
lean::inc(x_74);
lean::dec(x_19);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; 
if (lean::is_scalar(x_44)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_44;
}
lean::cnstr_set(x_77, 0, x_74);
x_30 = x_77;
goto lbl_31;
}
else
{
obj* x_80; 
lean::dec(x_44);
lean::dec(x_74);
x_80 = lean::box(0);
x_30 = x_80;
goto lbl_31;
}
}
else
{
obj* x_82; obj* x_84; 
lean::dec(x_44);
x_82 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 x_84 = x_71;
} else {
 lean::inc(x_82);
 lean::dec(x_71);
 x_84 = lean::box(0);
}
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_85; 
x_85 = lean::cnstr_get(x_19, 1);
lean::inc(x_85);
lean::dec(x_19);
if (lean::obj_tag(x_85) == 0)
{
obj* x_90; 
lean::dec(x_84);
lean::dec(x_82);
x_90 = lean::box(0);
x_30 = x_90;
goto lbl_31;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
switch (lean::obj_tag(x_91)) {
case 0:
{
obj* x_93; obj* x_96; obj* x_99; obj* x_102; uint8 x_105; 
x_93 = lean::cnstr_get(x_82, 0);
lean::inc(x_93);
lean::dec(x_82);
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
lean::dec(x_85);
lean::dec(x_84);
x_108 = lean::box(0);
x_30 = x_108;
goto lbl_31;
}
else
{
obj* x_109; 
if (lean::is_scalar(x_84)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_84;
}
lean::cnstr_set(x_109, 0, x_85);
x_30 = x_109;
goto lbl_31;
}
}
default:
{
obj* x_114; 
lean::dec(x_85);
lean::dec(x_84);
lean::dec(x_91);
lean::dec(x_82);
x_114 = lean::box(0);
x_30 = x_114;
goto lbl_31;
}
}
}
}
case 1:
{
obj* x_115; 
x_115 = lean::cnstr_get(x_19, 1);
lean::inc(x_115);
lean::dec(x_19);
if (lean::obj_tag(x_115) == 0)
{
obj* x_120; 
lean::dec(x_84);
lean::dec(x_82);
x_120 = lean::box(0);
x_30 = x_120;
goto lbl_31;
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_115, 0);
lean::inc(x_121);
switch (lean::obj_tag(x_121)) {
case 1:
{
obj* x_123; obj* x_126; obj* x_129; obj* x_132; uint8 x_135; 
x_123 = lean::cnstr_get(x_82, 0);
lean::inc(x_123);
lean::dec(x_82);
x_126 = lean::cnstr_get(x_121, 0);
lean::inc(x_126);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_123, 1);
lean::inc(x_129);
lean::dec(x_123);
x_132 = lean::cnstr_get(x_126, 1);
lean::inc(x_132);
lean::dec(x_126);
x_135 = l_Lean_Elaborator_matchPrecedence___main(x_129, x_132);
if (x_135 == 0)
{
obj* x_138; 
lean::dec(x_84);
lean::dec(x_115);
x_138 = lean::box(0);
x_30 = x_138;
goto lbl_31;
}
else
{
obj* x_139; 
if (lean::is_scalar(x_84)) {
 x_139 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_139 = x_84;
}
lean::cnstr_set(x_139, 0, x_115);
x_30 = x_139;
goto lbl_31;
}
}
default:
{
obj* x_144; 
lean::dec(x_84);
lean::dec(x_82);
lean::dec(x_121);
lean::dec(x_115);
x_144 = lean::box(0);
x_30 = x_144;
goto lbl_31;
}
}
}
}
default:
{
obj* x_145; obj* x_147; obj* x_148; obj* x_150; 
x_145 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_147 = x_82;
} else {
 lean::inc(x_145);
 lean::dec(x_82);
 x_147 = lean::box(0);
}
x_150 = lean::cnstr_get(x_19, 1);
lean::inc(x_150);
lean::dec(x_19);
if (lean::obj_tag(x_150) == 0)
{
obj* x_156; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_156 = lean::box(0);
x_30 = x_156;
goto lbl_31;
}
else
{
obj* x_157; obj* x_159; 
x_157 = lean::cnstr_get(x_150, 0);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_set(x_150, 0, lean::box(0));
 x_159 = x_150;
} else {
 lean::inc(x_157);
 lean::dec(x_150);
 x_159 = lean::box(0);
}
switch (lean::obj_tag(x_157)) {
case 2:
{
obj* x_160; 
x_160 = lean::cnstr_get(x_145, 1);
lean::inc(x_160);
if (lean::obj_tag(x_160) == 0)
{
obj* x_162; obj* x_165; 
x_162 = lean::cnstr_get(x_157, 0);
lean::inc(x_162);
lean::dec(x_157);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
if (lean::obj_tag(x_165) == 0)
{
obj* x_169; 
lean::dec(x_159);
x_169 = lean::box(0);
x_148 = x_169;
goto lbl_149;
}
else
{
obj* x_170; obj* x_172; 
x_170 = lean::cnstr_get(x_165, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_170, 1);
lean::inc(x_172);
lean::dec(x_170);
switch (lean::obj_tag(x_172)) {
case 0:
{
obj* x_176; 
lean::dec(x_172);
if (lean::is_scalar(x_159)) {
 x_176 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_176 = x_159;
}
lean::cnstr_set(x_176, 0, x_165);
x_148 = x_176;
goto lbl_149;
}
default:
{
obj* x_180; 
lean::dec(x_159);
lean::dec(x_172);
lean::dec(x_165);
x_180 = lean::box(0);
x_148 = x_180;
goto lbl_149;
}
}
}
}
else
{
obj* x_182; obj* x_184; 
lean::dec(x_159);
x_182 = lean::cnstr_get(x_160, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_182, 1);
lean::inc(x_184);
lean::dec(x_182);
switch (lean::obj_tag(x_184)) {
case 0:
{
obj* x_187; obj* x_190; 
x_187 = lean::cnstr_get(x_157, 0);
lean::inc(x_187);
lean::dec(x_157);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_190) == 0)
{
obj* x_195; 
lean::dec(x_184);
lean::dec(x_160);
x_195 = lean::box(0);
x_148 = x_195;
goto lbl_149;
}
else
{
obj* x_196; obj* x_198; obj* x_199; 
x_196 = lean::cnstr_get(x_190, 0);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_set(x_190, 0, lean::box(0));
 x_198 = x_190;
} else {
 lean::inc(x_196);
 lean::dec(x_190);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
switch (lean::obj_tag(x_199)) {
case 0:
{
obj* x_202; obj* x_205; obj* x_208; obj* x_209; uint8 x_210; 
x_202 = lean::cnstr_get(x_184, 0);
lean::inc(x_202);
lean::dec(x_184);
x_205 = lean::cnstr_get(x_199, 0);
lean::inc(x_205);
lean::dec(x_199);
x_208 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_202);
x_209 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_205);
x_210 = lean::nat_dec_eq(x_208, x_209);
lean::dec(x_209);
lean::dec(x_208);
if (x_210 == 0)
{
obj* x_215; 
lean::dec(x_198);
lean::dec(x_160);
x_215 = lean::box(0);
x_148 = x_215;
goto lbl_149;
}
else
{
obj* x_216; 
if (lean::is_scalar(x_198)) {
 x_216 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_216 = x_198;
}
lean::cnstr_set(x_216, 0, x_160);
x_148 = x_216;
goto lbl_149;
}
}
default:
{
obj* x_221; 
lean::dec(x_198);
lean::dec(x_184);
lean::dec(x_199);
lean::dec(x_160);
x_221 = lean::box(0);
x_148 = x_221;
goto lbl_149;
}
}
}
}
default:
{
obj* x_225; 
lean::dec(x_184);
lean::dec(x_157);
lean::dec(x_160);
x_225 = lean::box(0);
x_148 = x_225;
goto lbl_149;
}
}
}
}
default:
{
obj* x_231; 
lean::dec(x_84);
lean::dec(x_159);
lean::dec(x_157);
lean::dec(x_147);
lean::dec(x_145);
x_231 = lean::box(0);
x_30 = x_231;
goto lbl_31;
}
}
}
lbl_149:
{
if (lean::obj_tag(x_148) == 0)
{
obj* x_235; 
lean::dec(x_84);
lean::dec(x_147);
lean::dec(x_145);
x_235 = lean::box(0);
x_30 = x_235;
goto lbl_31;
}
else
{
obj* x_236; obj* x_238; obj* x_239; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_236 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_238 = x_148;
} else {
 lean::inc(x_236);
 lean::dec(x_148);
 x_238 = lean::box(0);
}
x_239 = lean::cnstr_get(x_145, 0);
lean::inc(x_239);
lean::dec(x_145);
x_242 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_242, 0, x_239);
lean::cnstr_set(x_242, 1, x_236);
if (lean::is_scalar(x_147)) {
 x_243 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_243 = x_147;
}
lean::cnstr_set(x_243, 0, x_242);
if (lean::is_scalar(x_238)) {
 x_244 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_244 = x_238;
}
lean::cnstr_set(x_244, 0, x_243);
if (lean::is_scalar(x_84)) {
 x_245 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_245 = x_84;
}
lean::cnstr_set(x_245, 0, x_244);
x_30 = x_245;
goto lbl_31;
}
}
}
}
}
}
}
}
lbl_31:
{
if (lean::obj_tag(x_30) == 0)
{
obj* x_247; 
lean::dec(x_28);
x_247 = lean::box(0);
x_7 = x_247;
goto lbl_8;
}
else
{
obj* x_248; obj* x_250; obj* x_251; obj* x_252; 
x_248 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_250 = x_30;
} else {
 lean::inc(x_248);
 lean::dec(x_30);
 x_250 = lean::box(0);
}
x_251 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_251, 0, x_28);
lean::cnstr_set(x_251, 1, x_248);
if (lean::is_scalar(x_250)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_250;
}
lean::cnstr_set(x_252, 0, x_251);
x_7 = x_252;
goto lbl_8;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_255; 
lean::dec(x_6);
lean::dec(x_4);
x_255 = lean::box(0);
return x_255;
}
else
{
obj* x_256; obj* x_259; 
x_256 = lean::cnstr_get(x_7, 0);
lean::inc(x_256);
lean::dec(x_7);
x_259 = l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(x_4);
if (lean::obj_tag(x_259) == 0)
{
obj* x_262; 
lean::dec(x_6);
lean::dec(x_256);
x_262 = lean::box(0);
return x_262;
}
else
{
obj* x_263; obj* x_265; obj* x_266; obj* x_267; 
x_263 = lean::cnstr_get(x_259, 0);
if (lean::is_exclusive(x_259)) {
 x_265 = x_259;
} else {
 lean::inc(x_263);
 lean::dec(x_259);
 x_265 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_266 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_266 = x_6;
}
lean::cnstr_set(x_266, 0, x_256);
lean::cnstr_set(x_266, 1, x_263);
if (lean::is_scalar(x_265)) {
 x_267 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_267 = x_265;
}
lean::cnstr_set(x_267, 0, x_266);
return x_267;
}
}
}
}
}
}
obj* _init_l_Lean_Elaborator_matchSpec___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 0);
return x_0;
}
}
obj* l_Lean_Elaborator_matchSpec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
x_4 = x_8;
goto lbl_5;
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::box(0);
return x_12;
}
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_18 = lean::box(0);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_13);
x_20 = lean::box(0);
x_4 = x_20;
goto lbl_5;
}
}
lbl_5:
{
obj* x_22; obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_4);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::dec(x_1);
x_28 = l_Lean_Elaborator_matchSpec___closed__1;
x_29 = l_List_zipWith___main___rarg(x_28, x_22, x_25);
x_30 = l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; 
lean::dec(x_2);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_2);
lean::cnstr_set(x_36, 1, x_33);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_36);
return x_37;
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
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
x_15 = l_Lean_Elaborator_postprocessNotationSpec(x_13);
x_16 = lean::cnstr_get(x_0, 3);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 4);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_11);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_16);
lean::cnstr_set(x_21, 4, x_18);
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
obj* x_27; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 4);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_Lean_Elaborator_postprocessNotationSpec(x_27);
x_40 = lean::alloc_cnstr(0, 5, 0);
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
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_81; 
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
lean::inc(x_67);
x_69 = lean::cnstr_get(x_62, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_62, 2);
lean::inc(x_71);
x_73 = l_Lean_Elaborator_postprocessNotationSpec(x_71);
x_74 = lean::cnstr_get(x_62, 3);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_62, 4);
lean::inc(x_76);
lean::dec(x_62);
x_79 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_79, 0, x_67);
lean::cnstr_set(x_79, 1, x_69);
lean::cnstr_set(x_79, 2, x_73);
lean::cnstr_set(x_79, 3, x_74);
lean::cnstr_set(x_79, 4, x_76);
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
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_add(x_5, x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 5);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 7);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 8);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 9);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 10);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_3);
lean::cnstr_set(x_26, 2, x_8);
lean::cnstr_set(x_26, 3, x_9);
lean::cnstr_set(x_26, 4, x_11);
lean::cnstr_set(x_26, 5, x_13);
lean::cnstr_set(x_26, 6, x_15);
lean::cnstr_set(x_26, 7, x_17);
lean::cnstr_set(x_26, 8, x_19);
lean::cnstr_set(x_26, 9, x_21);
lean::cnstr_set(x_26, 10, x_23);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_47; uint8 x_50; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_15, 7);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 8);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 9);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 10);
lean::inc(x_26);
lean::inc(x_13);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_13);
lean::cnstr_set(x_29, 1, x_0);
lean::inc(x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer), 3, 1);
lean::closure_set(x_31, 0, x_29);
x_32 = lean::cnstr_get(x_15, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_15, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_15, 3);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_15, 4);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_15, 5);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_15, 6);
lean::inc(x_44);
lean::dec(x_15);
x_47 = lean::cnstr_get(x_18, 0);
lean::inc(x_47);
lean::dec(x_18);
x_50 = l_RBNode_isRed___main___rarg(x_20);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_20, x_13, x_31);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_47);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_53, 0, x_32);
lean::cnstr_set(x_53, 1, x_34);
lean::cnstr_set(x_53, 2, x_36);
lean::cnstr_set(x_53, 3, x_38);
lean::cnstr_set(x_53, 4, x_40);
lean::cnstr_set(x_53, 5, x_42);
lean::cnstr_set(x_53, 6, x_44);
lean::cnstr_set(x_53, 7, x_52);
lean::cnstr_set(x_53, 8, x_22);
lean::cnstr_set(x_53, 9, x_24);
lean::cnstr_set(x_53, 10, x_26);
if (lean::is_scalar(x_17)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_17;
}
lean::cnstr_set(x_54, 0, x_29);
lean::cnstr_set(x_54, 1, x_53);
if (lean::is_scalar(x_12)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_12;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_20, x_13, x_31);
x_57 = l_RBNode_setBlack___main___rarg(x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_47);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_59, 0, x_32);
lean::cnstr_set(x_59, 1, x_34);
lean::cnstr_set(x_59, 2, x_36);
lean::cnstr_set(x_59, 3, x_38);
lean::cnstr_set(x_59, 4, x_40);
lean::cnstr_set(x_59, 5, x_42);
lean::cnstr_set(x_59, 6, x_44);
lean::cnstr_set(x_59, 7, x_58);
lean::cnstr_set(x_59, 8, x_22);
lean::cnstr_set(x_59, 9, x_24);
lean::cnstr_set(x_59, 10, x_26);
if (lean::is_scalar(x_17)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_17;
}
lean::cnstr_set(x_60, 0, x_29);
lean::cnstr_set(x_60, 1, x_59);
if (lean::is_scalar(x_12)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_12;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_22; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 5);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 6);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 7);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 8);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_4);
lean::cnstr_set(x_22, 2, x_8);
lean::cnstr_set(x_22, 3, x_9);
lean::cnstr_set(x_22, 4, x_11);
lean::cnstr_set(x_22, 5, x_13);
lean::cnstr_set(x_22, 6, x_15);
lean::cnstr_set(x_22, 7, x_17);
lean::cnstr_set(x_22, 8, x_19);
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
obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; 
x_46 = lean::cnstr_get(x_40, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_40, 1);
lean::inc(x_48);
lean::dec(x_40);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_46);
lean::cnstr_set(x_55, 1, x_53);
x_56 = lean::cnstr_get(x_48, 2);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_48, 3);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_48, 4);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_48, 5);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_48, 6);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_48, 7);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_48, 8);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_48, 9);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_48, 10);
lean::inc(x_72);
lean::dec(x_48);
x_75 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_75, 0, x_51);
lean::cnstr_set(x_75, 1, x_55);
lean::cnstr_set(x_75, 2, x_56);
lean::cnstr_set(x_75, 3, x_58);
lean::cnstr_set(x_75, 4, x_60);
lean::cnstr_set(x_75, 5, x_62);
lean::cnstr_set(x_75, 6, x_64);
lean::cnstr_set(x_75, 7, x_66);
lean::cnstr_set(x_75, 8, x_68);
lean::cnstr_set(x_75, 9, x_70);
lean::cnstr_set(x_75, 10, x_72);
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
obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_112; obj* x_115; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_8);
x_99 = lean::cnstr_get(x_3, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_3, 1);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_3, 2);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_3, 3);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_3, 4);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 0);
lean::inc(x_109);
lean::dec(x_2);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
lean::dec(x_109);
x_115 = lean::box(0);
x_116 = l_Lean_Elaborator_notation_elaborate___closed__1;
x_117 = 1;
x_118 = l_String_splitAux___main___closed__1;
x_119 = l_Lean_Elaborator_notation_elaborate___closed__2;
x_120 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_120, 0, x_112);
lean::cnstr_set(x_120, 1, x_116);
lean::cnstr_set(x_120, 2, x_115);
lean::cnstr_set(x_120, 3, x_118);
lean::cnstr_set(x_120, 4, x_119);
lean::cnstr_set_scalar(x_120, sizeof(void*)*5, x_117);
x_121 = x_120;
x_122 = lean::cnstr_get(x_3, 5);
lean::inc(x_122);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_121);
lean::cnstr_set(x_124, 1, x_122);
x_125 = lean::cnstr_get(x_3, 6);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_3, 7);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_3, 8);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_3, 9);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_3, 10);
lean::inc(x_133);
lean::dec(x_3);
x_136 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_136, 0, x_99);
lean::cnstr_set(x_136, 1, x_101);
lean::cnstr_set(x_136, 2, x_103);
lean::cnstr_set(x_136, 3, x_105);
lean::cnstr_set(x_136, 4, x_107);
lean::cnstr_set(x_136, 5, x_124);
lean::cnstr_set(x_136, 6, x_125);
lean::cnstr_set(x_136, 7, x_127);
lean::cnstr_set(x_136, 8, x_129);
lean::cnstr_set(x_136, 9, x_131);
lean::cnstr_set(x_136, 10, x_133);
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::inc(x_0);
x_11 = level_mk_param(x_0);
x_12 = l_Lean_Elaborator_toLevel___main___closed__4;
x_13 = l_Lean_Elaborator_OrderedRBMap_insert___rarg(x_12, x_8, x_0, x_11);
x_14 = lean::cnstr_get(x_1, 4);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 5);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 6);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 7);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_1, 8);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_13);
lean::cnstr_set(x_25, 4, x_14);
lean::cnstr_set(x_25, 5, x_16);
lean::cnstr_set(x_25, 6, x_18);
lean::cnstr_set(x_25, 7, x_20);
lean::cnstr_set(x_25, 8, x_22);
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
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_33; obj* x_35; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_Lean_Parser_command_universe_HasView;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
lean::inc(x_0);
x_25 = lean::apply_1(x_21, x_0);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_29 = l_Lean_Elaborator_mangleIdent(x_26);
x_30 = lean::cnstr_get(x_15, 3);
lean::inc(x_30);
lean::dec(x_15);
x_33 = l_Lean_Elaborator_toLevel___main___closed__4;
lean::inc(x_29);
x_35 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_33, x_30, x_29);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_0);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_universe_elaborate___lambda__1), 2, 1);
lean::closure_set(x_37, 0, x_29);
x_38 = l_Lean_Elaborator_modifyCurrentScope(x_37, x_1, x_2, x_17);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_39 = x_35;
} else {
 lean::dec(x_35);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_0);
x_41 = l_Lean_Name_toString___closed__1;
x_42 = l_Lean_Name_toStringWithSep___main(x_41, x_29);
x_43 = l_Lean_Elaborator_universe_elaborate___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_46 = l_Lean_Elaborator_universe_elaborate___closed__2;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_40, x_47, x_1, x_2, x_17);
lean::dec(x_17);
lean::dec(x_40);
return x_48;
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
obj* _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown identifier '");
return x_0;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid 'attribute' command, identifier is ambiguous");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::inc(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_9);
x_14 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean::string_append(x_15, x_17);
x_19 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_8, x_18, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_8);
return x_19;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_4, 1);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_4, 0);
lean::inc(x_26);
lean::dec(x_4);
x_29 = lean::box(0);
x_30 = lean_expr_mk_const(x_26, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_4);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_0);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2;
x_38 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_36, x_37, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_36);
return x_38;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___boxed), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* x_4; obj* x_5; obj* x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_19; 
x_4 = l_Lean_Parser_command_attribute_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_9, 3);
lean::inc(x_15);
lean::inc(x_2);
lean::inc(x_1);
x_19 = l_Lean_Elaborator_attrsToPexpr(x_15, x_1, x_2, x_3);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_24);
 lean::dec(x_19);
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
obj* x_28; uint8 x_31; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = 0;
x_10 = x_31;
x_11 = x_28;
goto lbl_12;
}
}
else
{
lean::dec(x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_1);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_37 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_39 = x_19;
} else {
 lean::inc(x_37);
 lean::dec(x_19);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; uint8 x_44; 
x_41 = lean::cnstr_get(x_19, 0);
lean::inc(x_41);
lean::dec(x_19);
x_44 = 1;
x_10 = x_44;
x_11 = x_41;
goto lbl_12;
}
}
lbl_12:
{
obj* x_45; obj* x_47; obj* x_50; obj* x_55; 
x_45 = lean::cnstr_get(x_11, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_11, 1);
lean::inc(x_47);
lean::dec(x_11);
x_50 = lean::cnstr_get(x_9, 5);
lean::inc(x_50);
lean::dec(x_9);
lean::inc(x_2);
lean::inc(x_1);
x_55 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_50, x_1, x_2, x_47);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_45);
x_60 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_62 = x_55;
} else {
 lean::inc(x_60);
 lean::dec(x_55);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
return x_63;
}
else
{
obj* x_64; obj* x_67; obj* x_69; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_64 = lean::cnstr_get(x_55, 0);
lean::inc(x_64);
lean::dec(x_55);
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_64, 1);
lean::inc(x_69);
lean::dec(x_64);
x_72 = l_Lean_Elaborator_attribute_elaborate___closed__1;
x_73 = l_Lean_Elaborator_attribute_elaborate___closed__2;
x_74 = l_Lean_KVMap_setBool(x_72, x_73, x_10);
x_75 = l_Lean_Elaborator_mkEqns___closed__1;
x_76 = l_Lean_Expr_mkCapp(x_75, x_67);
x_77 = lean_expr_mk_app(x_45, x_76);
x_78 = lean_expr_mk_mdata(x_74, x_77);
x_79 = l_Lean_Elaborator_oldElabCommand(x_0, x_78, x_1, x_2, x_69);
lean::dec(x_1);
lean::dec(x_0);
return x_79;
}
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1(x_0, x_1, x_2, x_3);
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
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_15; 
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
lean::inc(x_1);
x_15 = l_Lean_Elaborator_toPexpr___main(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
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
obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
lean::dec(x_15);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_Lean_Elaborator_check_elaborate___closed__1;
x_32 = lean_expr_mk_mdata(x_31, x_26);
x_33 = l_Lean_Elaborator_oldElabCommand(x_0, x_32, x_1, x_2, x_28);
lean::dec(x_1);
lean::dec(x_0);
return x_33;
}
}
}
obj* l_Lean_Elaborator_open_elaborate___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 6);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 7);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_List_append___rarg(x_16, x_18);
x_22 = lean::cnstr_get(x_1, 8);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_8);
lean::cnstr_set(x_25, 4, x_10);
lean::cnstr_set(x_25, 5, x_12);
lean::cnstr_set(x_25, 6, x_14);
lean::cnstr_set(x_25, 7, x_21);
lean::cnstr_set(x_25, 8, x_22);
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
obj* x_4; 
x_4 = l_Lean_Elaborator_getNamespace(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
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
x_18 = l_Lean_Parser_command_export_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_0);
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_15, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_15, 2);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_15, 3);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
lean::dec(x_22);
x_34 = l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(x_13, x_31);
x_35 = l_List_append___rarg(x_29, x_34);
x_36 = lean::cnstr_get(x_15, 4);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_15, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_15, 6);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_15, 7);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_15, 8);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_15, 9);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 10);
lean::inc(x_48);
lean::dec(x_15);
x_51 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_51, 0, x_23);
lean::cnstr_set(x_51, 1, x_25);
lean::cnstr_set(x_51, 2, x_27);
lean::cnstr_set(x_51, 3, x_35);
lean::cnstr_set(x_51, 4, x_36);
lean::cnstr_set(x_51, 5, x_38);
lean::cnstr_set(x_51, 6, x_40);
lean::cnstr_set(x_51, 7, x_42);
lean::cnstr_set(x_51, 8, x_44);
lean::cnstr_set(x_51, 9, x_46);
lean::cnstr_set(x_51, 10, x_48);
x_52 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_17;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 5);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 6);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 7);
lean::inc(x_16);
lean::dec(x_1);
x_19 = lean::alloc_cnstr(0, 9, 0);
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
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_24; obj* x_25; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_Lean_Parser_command_setOption_HasView;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
x_24 = lean::apply_1(x_21, x_0);
x_25 = lean::cnstr_get(x_24, 2);
lean::inc(x_25);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_27; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_34; obj* x_37; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_27);
x_31 = lean::cnstr_get(x_24, 1);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_31, 2);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::cnstr_get(x_15, 8);
lean::inc(x_37);
lean::dec(x_15);
x_40 = 1;
x_41 = l_Lean_KVMap_setBool(x_37, x_34, x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_42, 0, x_41);
x_43 = l_Lean_Elaborator_modifyCurrentScope(x_42, x_1, x_2, x_17);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_51; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_27);
x_45 = lean::cnstr_get(x_24, 1);
lean::inc(x_45);
lean::dec(x_24);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
lean::dec(x_45);
x_51 = lean::cnstr_get(x_15, 8);
lean::inc(x_51);
lean::dec(x_15);
x_54 = 0;
x_55 = l_Lean_KVMap_setBool(x_51, x_48, x_54);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_56, 0, x_55);
x_57 = l_Lean_Elaborator_modifyCurrentScope(x_56, x_1, x_2, x_17);
return x_57;
}
}
case 1:
{
obj* x_58; obj* x_61; obj* x_64; obj* x_67; obj* x_70; 
x_58 = lean::cnstr_get(x_24, 1);
lean::inc(x_58);
lean::dec(x_24);
x_61 = lean::cnstr_get(x_58, 2);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::cnstr_get(x_15, 8);
lean::inc(x_64);
lean::dec(x_15);
x_67 = lean::cnstr_get(x_25, 0);
lean::inc(x_67);
lean::dec(x_25);
x_70 = l_Lean_Parser_stringLit_View_value(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_72; obj* x_73; 
lean::dec(x_61);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_72, 0, x_64);
x_73 = l_Lean_Elaborator_modifyCurrentScope(x_72, x_1, x_2, x_17);
return x_73;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_70, 0);
lean::inc(x_74);
lean::dec(x_70);
x_77 = l_Lean_KVMap_setString(x_64, x_61, x_74);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_78, 0, x_77);
x_79 = l_Lean_Elaborator_modifyCurrentScope(x_78, x_1, x_2, x_17);
return x_79;
}
}
default:
{
obj* x_80; obj* x_83; obj* x_86; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_80 = lean::cnstr_get(x_24, 1);
lean::inc(x_80);
lean::dec(x_24);
x_83 = lean::cnstr_get(x_80, 2);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::cnstr_get(x_15, 8);
lean::inc(x_86);
lean::dec(x_15);
x_89 = lean::cnstr_get(x_25, 0);
lean::inc(x_89);
lean::dec(x_25);
x_92 = l_Lean_Parser_number_View_toNat___main(x_89);
x_93 = l_Lean_KVMap_setNat(x_86, x_83, x_92);
x_94 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_setOption_elaborate___lambda__1), 2, 1);
lean::closure_set(x_94, 0, x_93);
x_95 = l_Lean_Elaborator_modifyCurrentScope(x_94, x_1, x_2, x_17);
return x_95;
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_15; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_15 = lean::apply_3(x_1, x_8, x_2, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_1);
lean::dec(x_10);
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
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_0 = x_10;
x_3 = x_26;
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
obj* x_19; obj* x_22; obj* x_23; obj* x_27; obj* x_28; 
x_19 = lean::cnstr_get(x_4, 0);
lean::inc(x_19);
lean::dec(x_4);
x_22 = l_Lean_Parser_command_end_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
lean::inc(x_0);
x_27 = lean::apply_1(x_23, x_0);
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_33; uint8 x_34; 
x_31 = lean::cnstr_get(x_19, 1);
lean::inc(x_31);
x_33 = l_Lean_Elaborator_end_elaborate___closed__2;
x_34 = lean_name_dec_eq(x_33, x_31);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_51; 
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_0);
x_36 = lean::cnstr_get(x_19, 0);
lean::inc(x_36);
lean::dec(x_19);
x_39 = l_Lean_Elaborator_end_elaborate___closed__3;
x_40 = lean::string_append(x_39, x_36);
lean::dec(x_36);
x_42 = l_Lean_Elaborator_end_elaborate___closed__4;
x_43 = lean::string_append(x_40, x_42);
x_44 = l_Lean_Name_toString___closed__1;
x_45 = l_Lean_Name_toStringWithSep___main(x_44, x_31);
x_46 = lean::string_append(x_43, x_45);
lean::dec(x_45);
x_48 = l_Char_HasRepr___closed__1;
x_49 = lean::string_append(x_46, x_48);
lean::inc(x_2);
x_51 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_35, x_49, x_1, x_2, x_3);
lean::dec(x_35);
if (lean::obj_tag(x_51) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
x_56 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_58 = x_51;
} else {
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_51);
x_61 = lean::cnstr_get(x_3, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_3, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_3, 2);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_3, 3);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_3, 5);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_3, 6);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_3, 7);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_3, 8);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_3, 9);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_3, 10);
lean::inc(x_79);
lean::dec(x_3);
x_82 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_82, 0, x_61);
lean::cnstr_set(x_82, 1, x_63);
lean::cnstr_set(x_82, 2, x_65);
lean::cnstr_set(x_82, 3, x_67);
lean::cnstr_set(x_82, 4, x_11);
lean::cnstr_set(x_82, 5, x_69);
lean::cnstr_set(x_82, 6, x_71);
lean::cnstr_set(x_82, 7, x_73);
lean::cnstr_set(x_82, 8, x_75);
lean::cnstr_set(x_82, 9, x_77);
lean::cnstr_set(x_82, 10, x_79);
x_83 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_82);
return x_83;
}
}
else
{
obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_31);
lean::dec(x_19);
x_87 = lean::cnstr_get(x_3, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_3, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_3, 2);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_3, 3);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_3, 5);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_3, 6);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_3, 7);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_3, 8);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_3, 9);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_3, 10);
lean::inc(x_105);
lean::dec(x_3);
x_108 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_108, 0, x_87);
lean::cnstr_set(x_108, 1, x_89);
lean::cnstr_set(x_108, 2, x_91);
lean::cnstr_set(x_108, 3, x_93);
lean::cnstr_set(x_108, 4, x_11);
lean::cnstr_set(x_108, 5, x_95);
lean::cnstr_set(x_108, 6, x_97);
lean::cnstr_set(x_108, 7, x_99);
lean::cnstr_set(x_108, 8, x_101);
lean::cnstr_set(x_108, 9, x_103);
lean::cnstr_set(x_108, 10, x_105);
x_109 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_108);
return x_109;
}
}
else
{
obj* x_110; obj* x_112; obj* x_114; obj* x_115; uint8 x_116; 
x_110 = lean::cnstr_get(x_19, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 x_114 = x_28;
} else {
 lean::inc(x_112);
 lean::dec(x_28);
 x_114 = lean::box(0);
}
x_115 = l_Lean_Elaborator_mangleIdent(x_112);
x_116 = lean_name_dec_eq(x_115, x_110);
lean::dec(x_115);
if (x_116 == 0)
{
obj* x_118; obj* x_119; obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_131; obj* x_132; obj* x_134; 
if (lean::is_scalar(x_114)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_114;
}
lean::cnstr_set(x_118, 0, x_0);
x_119 = lean::cnstr_get(x_19, 0);
lean::inc(x_119);
lean::dec(x_19);
x_122 = l_Lean_Elaborator_end_elaborate___closed__3;
x_123 = lean::string_append(x_122, x_119);
lean::dec(x_119);
x_125 = l_Lean_Elaborator_end_elaborate___closed__4;
x_126 = lean::string_append(x_123, x_125);
x_127 = l_Lean_Name_toString___closed__1;
x_128 = l_Lean_Name_toStringWithSep___main(x_127, x_110);
x_129 = lean::string_append(x_126, x_128);
lean::dec(x_128);
x_131 = l_Char_HasRepr___closed__1;
x_132 = lean::string_append(x_129, x_131);
lean::inc(x_2);
x_134 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_118, x_132, x_1, x_2, x_3);
lean::dec(x_118);
if (lean::obj_tag(x_134) == 0)
{
obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
x_139 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_141 = x_134;
} else {
 lean::inc(x_139);
 lean::dec(x_134);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_139);
return x_142;
}
else
{
obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; obj* x_166; 
lean::dec(x_134);
x_144 = lean::cnstr_get(x_3, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_3, 1);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_3, 2);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_3, 3);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_3, 5);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_3, 6);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_3, 7);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_3, 8);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_3, 9);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_3, 10);
lean::inc(x_162);
lean::dec(x_3);
x_165 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_165, 0, x_144);
lean::cnstr_set(x_165, 1, x_146);
lean::cnstr_set(x_165, 2, x_148);
lean::cnstr_set(x_165, 3, x_150);
lean::cnstr_set(x_165, 4, x_11);
lean::cnstr_set(x_165, 5, x_152);
lean::cnstr_set(x_165, 6, x_154);
lean::cnstr_set(x_165, 7, x_156);
lean::cnstr_set(x_165, 8, x_158);
lean::cnstr_set(x_165, 9, x_160);
lean::cnstr_set(x_165, 10, x_162);
x_166 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_165);
return x_166;
}
}
else
{
obj* x_171; obj* x_173; obj* x_175; obj* x_177; obj* x_179; obj* x_181; obj* x_183; obj* x_185; obj* x_187; obj* x_189; obj* x_192; obj* x_193; 
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_114);
lean::dec(x_110);
x_171 = lean::cnstr_get(x_3, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_3, 1);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_3, 2);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_3, 3);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_3, 5);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_3, 6);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_3, 7);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_3, 8);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_3, 9);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_3, 10);
lean::inc(x_189);
lean::dec(x_3);
x_192 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_192, 0, x_171);
lean::cnstr_set(x_192, 1, x_173);
lean::cnstr_set(x_192, 2, x_175);
lean::cnstr_set(x_192, 3, x_177);
lean::cnstr_set(x_192, 4, x_11);
lean::cnstr_set(x_192, 5, x_179);
lean::cnstr_set(x_192, 6, x_181);
lean::cnstr_set(x_192, 7, x_183);
lean::cnstr_set(x_192, 8, x_185);
lean::cnstr_set(x_192, 9, x_187);
lean::cnstr_set(x_192, 10, x_189);
x_193 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_192);
return x_193;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_15; 
x_7 = l_Lean_Parser_command_section_HasView;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::apply_1(x_8, x_0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_12) == 0)
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
lean::dec(x_15);
x_23 = l_Lean_Elaborator_section_elaborate___closed__2;
x_4 = x_23;
x_5 = x_20;
goto lbl_6;
}
}
else
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_12);
x_25 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_27 = x_15;
} else {
 lean::inc(x_25);
 lean::dec(x_15);
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
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_12, 0);
lean::inc(x_29);
lean::dec(x_12);
x_32 = lean::cnstr_get(x_15, 0);
lean::inc(x_32);
lean::dec(x_15);
x_4 = x_29;
x_5 = x_32;
goto lbl_6;
}
}
lbl_6:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_35 = lean::cnstr_get(x_5, 0);
x_37 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_39 = x_5;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_5);
 x_39 = lean::box(0);
}
x_40 = l_Lean_Elaborator_mangleIdent(x_4);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_37, 3);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_35, 2);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_35, 3);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_35, 4);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_35, 5);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_35, 6);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_35, 7);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_35, 8);
lean::inc(x_61);
lean::dec(x_35);
x_64 = l_Lean_Elaborator_section_elaborate___closed__1;
x_65 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_40);
lean::cnstr_set(x_65, 2, x_49);
lean::cnstr_set(x_65, 3, x_51);
lean::cnstr_set(x_65, 4, x_53);
lean::cnstr_set(x_65, 5, x_55);
lean::cnstr_set(x_65, 6, x_57);
lean::cnstr_set(x_65, 7, x_59);
lean::cnstr_set(x_65, 8, x_61);
x_66 = lean::cnstr_get(x_37, 4);
lean::inc(x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::cnstr_get(x_37, 5);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_37, 6);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_37, 7);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_37, 8);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_37, 9);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_37, 10);
lean::inc(x_79);
lean::dec(x_37);
x_82 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_82, 0, x_41);
lean::cnstr_set(x_82, 1, x_43);
lean::cnstr_set(x_82, 2, x_45);
lean::cnstr_set(x_82, 3, x_47);
lean::cnstr_set(x_82, 4, x_68);
lean::cnstr_set(x_82, 5, x_69);
lean::cnstr_set(x_82, 6, x_71);
lean::cnstr_set(x_82, 7, x_73);
lean::cnstr_set(x_82, 8, x_75);
lean::cnstr_set(x_82, 9, x_77);
lean::cnstr_set(x_82, 10, x_79);
x_83 = lean::box(0);
if (lean::is_scalar(x_39)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_39;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
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
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_0);
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_Lean_Elaborator_getNamespace(x_1, x_2, x_17);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_15);
x_23 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_25 = x_20;
} else {
 lean::inc(x_23);
 lean::dec(x_20);
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
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_27 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_29 = x_20;
} else {
 lean::inc(x_27);
 lean::dec(x_20);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 0);
x_32 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_34 = x_27;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_27);
 x_34 = lean::box(0);
}
x_35 = l_Lean_Parser_command_namespace_HasView;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_39 = lean::apply_1(x_36, x_0);
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_43 = l_Lean_Elaborator_mangleIdent(x_40);
x_44 = lean::cnstr_get(x_15, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_15, 3);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_15, 4);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_15, 5);
lean::inc(x_50);
lean::inc(x_43);
x_53 = l_Lean_Name_append___main(x_30, x_43);
lean::dec(x_30);
x_55 = lean::cnstr_get(x_15, 6);
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::cnstr_get(x_15, 7);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_15, 8);
lean::inc(x_60);
lean::dec(x_15);
x_63 = l_Lean_Elaborator_namespace_elaborate___closed__1;
x_64 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_43);
lean::cnstr_set(x_64, 2, x_44);
lean::cnstr_set(x_64, 3, x_46);
lean::cnstr_set(x_64, 4, x_48);
lean::cnstr_set(x_64, 5, x_50);
lean::cnstr_set(x_64, 6, x_57);
lean::cnstr_set(x_64, 7, x_58);
lean::cnstr_set(x_64, 8, x_60);
x_65 = lean::cnstr_get(x_32, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_32, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_32, 2);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_32, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_32, 4);
lean::inc(x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_64);
lean::cnstr_set(x_75, 1, x_73);
x_76 = lean::cnstr_get(x_32, 5);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_32, 6);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_32, 7);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_32, 8);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_32, 9);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_32, 10);
lean::inc(x_86);
lean::dec(x_32);
x_89 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_89, 0, x_65);
lean::cnstr_set(x_89, 1, x_67);
lean::cnstr_set(x_89, 2, x_69);
lean::cnstr_set(x_89, 3, x_71);
lean::cnstr_set(x_89, 4, x_75);
lean::cnstr_set(x_89, 5, x_76);
lean::cnstr_set(x_89, 6, x_78);
lean::cnstr_set(x_89, 7, x_80);
lean::cnstr_set(x_89, 8, x_82);
lean::cnstr_set(x_89, 9, x_84);
lean::cnstr_set(x_89, 10, x_86);
x_90 = lean::box(0);
if (lean::is_scalar(x_34)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_34;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
if (lean::is_scalar(x_29)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_29;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
x_22 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_13, x_1, x_2);
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
x_25 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_7, x_1, x_2);
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
x_44 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_34, x_1, x_2);
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
x_50 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_34, x_1, x_2);
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
x_53 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_28, x_1, x_2);
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
x_59 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_28, x_1, x_2);
x_60 = l_RBNode_balance1___main___rarg(x_58, x_59);
return x_60;
}
}
}
}
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; uint8 x_12; 
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
x_12 = l_RBNode_isRed___main___rarg(x_0);
if (x_12 == 0)
{
obj* x_13; 
x_13 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_0, x_7, x_9);
x_0 = x_13;
x_1 = x_4;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__1(x_0, x_7, x_9);
x_16 = l_RBNode_setBlack___main___rarg(x_15);
x_0 = x_16;
x_1 = x_4;
goto _start;
}
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
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_variables_elaborate), 4, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_include;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_include_elaborate___boxed), 4, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_command_Declaration;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate), 4, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_Lean_Parser_command_attribute;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_attribute_elaborate), 4, 0);
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
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_check_elaborate), 4, 0);
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
x_74 = l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__2(x_73, x_72);
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_5, 2);
x_7 = lean_name_dec_eq(x_6, x_0);
if (x_7 == 0)
{
x_2 = x_4;
goto _start;
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
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean_name_dec_eq(x_0, x_5);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
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
obj* x_5; 
lean::dec(x_0);
x_5 = l_List_reverse___rarg(x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_1, 8);
lean::inc(x_0);
x_13 = l_Lean_Name_append___main(x_6, x_0);
x_14 = lean_environment_contains(x_11, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
lean::dec(x_6);
lean::dec(x_10);
x_2 = x_8;
goto _start;
}
else
{
obj* x_19; 
if (lean::is_scalar(x_10)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_10;
}
lean::cnstr_set(x_19, 0, x_6);
lean::cnstr_set(x_19, 1, x_3);
x_2 = x_8;
x_3 = x_19;
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
obj* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
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
x_9 = lean_environment_contains(x_0, x_4);
if (x_9 == 0)
{
lean::dec(x_4);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_13; 
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_2);
x_1 = x_6;
x_2 = x_13;
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
obj* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
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
x_9 = lean_environment_contains(x_0, x_4);
if (x_9 == 0)
{
lean::dec(x_4);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
else
{
obj* x_13; 
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_2);
x_1 = x_6;
x_2 = x_13;
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
x_22 = l_Lean_Elaborator_toLevel___main___closed__4;
lean::inc(x_0);
x_24 = l_Lean_Elaborator_OrderedRBMap_find___rarg(x_22, x_20, x_0);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; 
x_25 = lean::cnstr_get(x_15, 6);
lean::inc(x_25);
x_27 = lean::box(0);
lean::inc(x_0);
x_29 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(x_0, x_3, x_25, x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_33; obj* x_34; uint8 x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_45; obj* x_47; obj* x_48; 
x_30 = l_Lean_Elaborator_resolveContext___main___closed__1;
x_31 = lean::box(0);
lean::inc(x_0);
x_33 = l_Lean_Name_replacePrefix___main(x_0, x_30, x_31);
x_34 = lean::cnstr_get(x_3, 8);
lean::inc(x_34);
x_36 = lean_environment_contains(x_34, x_33);
x_37 = lean::cnstr_get(x_15, 7);
lean::inc(x_37);
lean::inc(x_0);
x_40 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(x_0, x_37);
x_41 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(x_34, x_40, x_27);
x_42 = lean::cnstr_get(x_3, 3);
lean::inc(x_42);
lean::dec(x_3);
x_45 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(x_15, x_42, x_27);
lean::dec(x_15);
x_47 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(x_0, x_45);
x_48 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(x_34, x_47, x_27);
lean::dec(x_34);
if (x_36 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_33);
x_51 = l_List_append___rarg(x_29, x_41);
x_52 = l_List_append___rarg(x_51, x_48);
if (lean::is_scalar(x_19)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_19;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_14;
}
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_33);
lean::cnstr_set(x_55, 1, x_29);
x_56 = l_List_append___rarg(x_55, x_41);
x_57 = l_List_append___rarg(x_56, x_48);
if (lean::is_scalar(x_19)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_19;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_14;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
else
{
obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_3);
lean::dec(x_15);
x_62 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 1);
 x_64 = x_29;
} else {
 lean::inc(x_62);
 lean::dec(x_29);
 x_64 = lean::box(0);
}
x_65 = l_Lean_Name_append___main(x_62, x_0);
lean::dec(x_62);
if (lean::is_scalar(x_64)) {
 x_67 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_67 = x_64;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_27);
if (lean::is_scalar(x_19)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_19;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_14;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_74; obj* x_77; obj* x_79; obj* x_80; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
lean::dec(x_19);
x_74 = lean::cnstr_get(x_24, 0);
lean::inc(x_74);
lean::dec(x_24);
x_77 = lean::cnstr_get(x_74, 1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_79 = x_74;
} else {
 lean::inc(x_77);
 lean::dec(x_74);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
lean::dec(x_77);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set(x_84, 1, x_83);
if (lean::is_scalar(x_79)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_79;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_14;
}
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
}
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(x_0, x_1, x_2);
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
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_ReaderT_pure___at_Lean_Elaborator_toLevel___main___spec__2___rarg(x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_preresolve___main), 4, 1);
lean::closure_set(x_13, 0, x_8);
x_14 = l_List_mmap___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_ReaderT_map___at_Lean_Elaborator_toLevel___main___spec__1___rarg(x_14, x_13, x_1, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_10);
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_10, x_1, x_2, x_30);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_35 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_37 = x_33;
} else {
 lean::inc(x_35);
 lean::dec(x_33);
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
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_39, 0);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_28, x_42);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_41)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_41;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
lean::dec(x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_17 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_19 = x_9;
} else {
 lean::inc(x_17);
 lean::dec(x_9);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 0);
x_22 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_24 = x_17;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_17);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_4, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_4, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_4, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_4, 3);
lean::inc(x_31);
x_33 = l_List_append___rarg(x_20, x_31);
x_34 = lean::cnstr_get(x_4, 4);
lean::inc(x_34);
lean::dec(x_4);
x_37 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_37, 0, x_25);
lean::cnstr_set(x_37, 1, x_27);
lean::cnstr_set(x_37, 2, x_29);
lean::cnstr_set(x_37, 3, x_33);
lean::cnstr_set(x_37, 4, x_34);
if (lean::is_scalar(x_6)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_6;
}
lean::cnstr_set(x_38, 0, x_37);
if (lean::is_scalar(x_24)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_24;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_22);
if (lean::is_scalar(x_19)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_19;
}
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
case 2:
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
x_41 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_43 = x_0;
} else {
 lean::inc(x_41);
 lean::dec(x_0);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_46 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_44, x_1, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_41);
lean::dec(x_43);
x_49 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_51 = x_46;
} else {
 lean::inc(x_49);
 lean::dec(x_46);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
return x_52;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_53 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_55 = x_46;
} else {
 lean::inc(x_53);
 lean::dec(x_46);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_53, 0);
x_58 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_60 = x_53;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_41, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_41, 2);
lean::inc(x_63);
lean::dec(x_41);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set(x_66, 1, x_56);
lean::cnstr_set(x_66, 2, x_63);
if (lean::is_scalar(x_43)) {
 x_67 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_67 = x_43;
}
lean::cnstr_set(x_67, 0, x_66);
if (lean::is_scalar(x_60)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_60;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_58);
if (lean::is_scalar(x_55)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_55;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
default:
{
obj* x_72; obj* x_73; 
lean::dec(x_1);
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
obj* l_Lean_Elaborator_preresolve(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_preresolve___main(x_0, x_1, x_2, x_3);
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
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_Lean_Expander_builtinTransformers;
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
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
lean::cnstr_set(x_20, 6, x_10);
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
x_8 = l_Lean_Parser_Syntax_toFormat___main(x_1);
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
obj* x_38; obj* x_43; 
lean::dec(x_20);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_25, 0);
lean::inc(x_38);
lean::dec(x_25);
lean::inc(x_2);
lean::inc(x_0);
x_43 = l_Lean_Elaborator_preresolve___main(x_1, x_0, x_2, x_3);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_38);
x_47 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_49 = x_43;
} else {
 lean::inc(x_47);
 lean::dec(x_43);
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
obj* x_51; obj* x_54; obj* x_56; obj* x_59; 
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
x_59 = lean::apply_4(x_38, x_54, x_0, x_2, x_56);
return x_59;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_35; obj* x_36; obj* x_37; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 6);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 7);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 8);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 9);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 10);
lean::inc(x_21);
lean::dec(x_1);
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
x_35 = lean::alloc_cnstr(0, 11, 0);
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
 l_Lean_Elaborator_toLevel___main___closed__5 = _init_l_Lean_Elaborator_toLevel___main___closed__5();
lean::mark_persistent(l_Lean_Elaborator_toLevel___main___closed__5);
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
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___lambda__1___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___lambda__1___closed__2);
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
 l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___lambda__1___closed__1);
 l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1 = _init_l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1);
 l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2 = _init_l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2);
 l_Lean_Elaborator_Declaration_elaborate___closed__1 = _init_l_Lean_Elaborator_Declaration_elaborate___closed__1();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___closed__1);
 l_Lean_Elaborator_Declaration_elaborate___closed__2 = _init_l_Lean_Elaborator_Declaration_elaborate___closed__2();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___closed__2);
 l_Lean_Elaborator_Declaration_elaborate___closed__3 = _init_l_Lean_Elaborator_Declaration_elaborate___closed__3();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___closed__3);
 l_Lean_Elaborator_Declaration_elaborate___closed__4 = _init_l_Lean_Elaborator_Declaration_elaborate___closed__4();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___closed__4);
 l_Lean_Elaborator_Declaration_elaborate___closed__5 = _init_l_Lean_Elaborator_Declaration_elaborate___closed__5();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___closed__5);
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
 l_Lean_Elaborator_matchSpec___closed__1 = _init_l_Lean_Elaborator_matchSpec___closed__1();
lean::mark_persistent(l_Lean_Elaborator_matchSpec___closed__1);
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
 l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___lambda__1___closed__2);
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
