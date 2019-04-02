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
obj* l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_getOptType___main(obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1(obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__2;
obj* l_Lean_Elaborator_notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_postprocessNotationSpec___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3___boxed(obj*, obj*, obj*, obj*);
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
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7___boxed(obj*);
uint8 l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(obj*, uint8, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1(obj*, uint8, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
obj* l_Lean_Elaborator_mkState___closed__3;
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1;
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2;
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9(obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_MonadExcept;
obj* l_Lean_Elaborator_attribute_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__6;
obj* l_Lean_Elaborator_toPexpr___main___closed__21;
obj* l_Lean_Elaborator_matchSpec(obj*, obj*);
obj* l_Lean_Elaborator_matchOpenSpec(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__3;
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace;
extern obj* l_Lean_Parser_Level_trailing_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_lengthAux___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_identUnivParamsToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Module_header;
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__22;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadState;
obj* l_Lean_Elaborator_elaborators;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2;
obj* l_StateT_Monad___rarg(obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3(obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_variables_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__2;
obj* l_Lean_Elaborator_variables_elaborate(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__37;
extern "C" obj* level_mk_mvar(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_include_elaborate___spec__1(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___rarg(obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___rarg(obj*, obj*, obj*);
extern "C" obj* lean_expr_local(obj*, obj*, obj*, uint8);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1;
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__3;
obj* l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__9;
extern obj* l_Lean_Parser_command_attribute;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_TokenMap_insert___rarg(obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__30;
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
extern obj* l_Lean_Parser_command_variables;
obj* l_Lean_Elaborator_elabDefLike(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__4;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_mangleIdent___spec__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__3;
obj* l_Lean_Elaborator_elabDefLike___lambda__1(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__28;
extern obj* l_Lean_Parser_Term_have_HasView;
obj* l_Lean_Expr_mkCapp(obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__19;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___boxed(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__31;
extern obj* l_Lean_Parser_Term_structInst_HasView;
obj* l_Lean_Elaborator_universe_elaborate___closed__1;
obj* l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_toList___rarg(obj*);
obj* l_Lean_Elaborator_mkNotationKind(obj*, obj*);
obj* l_Lean_Elaborator_command_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__34;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__45;
obj* l_Lean_Elaborator_toLevel___main___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_Elaborator_section_elaborate___closed__2;
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___closed__2;
obj* l_Lean_Elaborator_toPexpr___main___closed__1;
extern obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Elaborator_check_elaborate(obj*, obj*, obj*, obj*);
obj* l_monadStateTrans___rarg(obj*, obj*);
obj* l_Lean_Elaborator_namesToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Lean_Elaborator_mkState___closed__4;
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_Lean_Elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_section;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__14;
obj* l_ExceptT_MonadExcept___rarg(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_attribute_HasView;
obj* l_Lean_Elaborator_toPexpr___main___closed__32;
extern obj* l_Lean_Parser_command_reserveNotation_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_export_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15___boxed(obj*);
obj* l_Lean_Elaborator_resolveContext___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__1;
obj* l_Lean_Elaborator_notation_elaborateAux(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__5(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderIdent_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__8(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__18;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__6;
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__10;
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__44;
obj* l_Lean_Elaborator_levelAdd___main(obj*, obj*);
extern obj* l_Lean_Parser_command_end_HasView;
obj* l_Lean_Elaborator_attribute_elaborate___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4;
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj*, obj*, obj*);
obj* l_fix1___rarg___lambda__1___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_end;
extern obj* l_Lean_Parser_Term_sort_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__27;
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_command_export;
obj* l_Lean_Elaborator_end_elaborate___closed__4;
obj* l_Lean_Elaborator_mangleIdent(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace___main(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__12;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__2;
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Term_show_HasView;
obj* l_List_join___main___rarg(obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__29;
extern obj* l_Lean_Parser_Term_structInstItem_HasView;
extern obj* l_Lean_Parser_command_setOption_HasView;
obj* l_Lean_Elaborator_Expr_mkAnnotation___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_Lean_Parser_MonadRec;
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2;
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__20;
extern obj* l_Lean_Parser_command_initQuot;
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16(obj*, obj*, obj*);
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
obj* l_Lean_Elaborator_matchSpec___closed__1;
extern obj* l_Lean_Parser_command_open_HasView;
obj* l_Lean_Elaborator_inferModToPexpr___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_check;
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_explicit_HasView;
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__17;
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__4(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16___boxed(obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_Elaborator_noKind_elaborate___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_currLbp___rarg___lambda__3___closed__1;
obj* l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
extern obj* l_Lean_Parser_command_include_HasView;
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___closed__3;
obj* l_Lean_Elaborator_end_elaborate___closed__3;
obj* l_Lean_Elaborator_toPexpr___main___closed__33;
obj* l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkEqns___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
extern obj* l_Lean_Expander_builtinTransformers;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__4;
extern obj* l_Char_HasRepr___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Elaborator_toPexpr___main___closed__39;
extern obj* l_Lean_Parser_Term_lambda_HasView;
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__36;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1(obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3;
obj* l_Lean_Elaborator_isOpenNamespace___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Module_header_HasView;
obj* l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj*, obj*);
extern obj* l_Lean_Parser_command_setOption;
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Elaborator_matchPrecedence___main___boxed(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8___boxed(obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_StateT_MonadExcept___rarg(obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate___closed__1;
obj* l_Lean_Elaborator_currentScope___closed__1;
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(obj*);
obj* l_Lean_Elaborator_setOption_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate___closed__1;
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___rarg(obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationTokens(obj*, obj*);
obj* l_Lean_Elaborator_updateParserConfig___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__11;
obj* l_Lean_Elaborator_toPexpr___main___closed__40;
obj* l_Lean_Elaborator_eoi_elaborate___closed__1;
obj* l_Lean_Elaborator_toLevel___main___closed__3;
obj* l_Lean_Elaborator_end_elaborate___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15(obj*);
obj* l_Lean_Elaborator_section_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2(obj*, obj*);
uint8 l_List_foldr___main___at_Lean_Elaborator_isOpenNamespace___main___spec__2(obj*, uint8, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8(obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_Declaration;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Expander_expandBracketedBinder___main___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__13;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__1___closed__1;
obj* l_Lean_Elaborator_mkEqns___closed__2;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Elaborator_processCommand___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1;
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_open;
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_Id_pure___boxed(obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation_HasView;
obj* l_RBMap_fromList___at_Lean_Elaborator_elaborators___spec__1(obj*);
extern obj* l_Lean_Parser_command_section_HasView;
obj* l_List_filterMap___main___at_Lean_Elaborator_notation_elaborateAux___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Term_app_HasView;
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(obj*, obj*, obj*, obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(obj*, obj*, obj*, obj*);
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
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__5;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_registerNotationMacro___spec__1(obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_sortApp_HasView;
obj* l_Lean_Elaborator_mkNotationKind___boxed(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkEqns(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_isOpenNamespace___boxed(obj*, obj*);
obj* l_String_trim(obj*);
extern obj* l_Lean_Parser_command_universe;
obj* l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__7;
extern "C" obj* level_mk_succ(obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__43;
extern obj* l_Lean_Expander_bindingAnnotationUpdate;
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace_HasView;
obj* l_Lean_Elaborator_setOption_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__1;
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___closed__1;
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___closed__1;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7(obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(obj*);
obj* l_Lean_Elaborator_getNamespace___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_universe_HasView;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___boxed(obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__5;
obj* l_Lean_Elaborator_levelGetAppArgs___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_anonymousConstructor_HasView;
obj* l_Lean_Elaborator_end_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(obj*, obj*, obj*, obj*);
obj* l_Id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__5;
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4(obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__24;
obj* l_Id_bind___boxed(obj*, obj*);
uint8 l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_Lean_environment_contains___boxed(obj*, obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_variables_elaborate___spec__4(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_borrowed_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__26;
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__3(obj*, obj*, obj*);
obj* l_Lean_Elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" uint8 lean_environment_contains(obj*, obj*);
obj* l_ExceptT_Monad___rarg(obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Elaborator_preresolve___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2(obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__38;
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
obj* l_Lean_Elaborator_declModifiersToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_updateParserConfig(obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadReader;
obj* l_Lean_Elaborator_toPexpr___main___closed__41;
obj* l_Lean_Elaborator_toPexpr___main___closed__25;
obj* l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__17(obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate___closed__1;
obj* l_Lean_Elaborator_matchPrecedence___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1(obj*, obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_Lean_Elaborator_end_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_kind___main(obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5;
obj* l_Lean_Elaborator_variables_elaborate___closed__1;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_export_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__5;
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_Monad;
obj* l_Lean_Elaborator_levelAdd(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_eoi_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(obj*, obj*);
extern obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Elaborator_toLevel___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_currentScope(obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1___boxed(obj*);
extern obj* l_Lean_Parser_Term_inaccessible_HasView;
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_precToNat___main(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1(obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_match_HasView;
obj* l_Lean_Parser_Term_getLeading___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig___boxed(obj*);
obj* l_Lean_Expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__1;
extern obj* l_Lean_Parser_command_Declaration_HasView;
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(obj*);
extern obj* l_Lean_Expander_noExpansion___closed__1;
extern obj* l_Lean_Parser_Term_sort_HasView;
obj* l_Lean_Elaborator_resolveContext(obj*, obj*, obj*, obj*);
obj* l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__23;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__3___boxed(obj*, obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Elaborator_Declaration_elaborate___closed__2;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__2;
extern obj* l_Lean_Parser_command_reserveNotation;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj*, obj*);
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4(obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1;
uint8 l_Lean_Elaborator_matchPrecedence___main(obj*, obj*);
obj* l_Lean_Elaborator_attrsToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__2;
obj* l_Lean_Elaborator_initQuot_elaborate___closed__1;
obj* l_Lean_Parser_Syntax_toFormat___main(obj*);
obj* l_StateT_MonadState___rarg(obj*);
obj* l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1___boxed(obj*, obj*);
extern obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(obj*, obj*);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_pi_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__42;
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_paren_transform___spec__1(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__15;
obj* l_Lean_Elaborator_postprocessNotationSpec(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19(obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6(obj*, obj*, obj*);
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
obj* _init_l_Lean_Elaborator_OrderedRBMap_empty___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
x_17 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_OrderedRBMap_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = lean::box(0);
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_6 = l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg(x_0, lean::box(0), x_3, x_2);
return x_6;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_find___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_OrderedRBMap_find(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
x_17 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___rarg(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_15 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
x_3 = l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_OrderedRBMap_ofList___rarg), 2, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_OrderedRBMap_ofList___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elaborator_OrderedRBMap_ofList(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_pure___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Id_Monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
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
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
x_14 = l_Lean_Name_quickLt(x_3, x_7);
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_5);
x_16 = l_Lean_Name_quickLt(x_7, x_3);
lean::dec(x_7);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_11);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_9);
return x_19;
}
else
{
lean::dec(x_9);
x_1 = lean::box(0);
x_2 = x_11;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6(x_2, lean::box(0), x_3, x_1);
return x_6;
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
x_53 = l_Lean_Parser_Syntax_toFormat___main(x_0);
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
x_77 = l_Lean_Parser_Syntax_toFormat___main(x_0);
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
obj* x_288; obj* x_291; obj* x_292; obj* x_295; 
x_288 = lean::cnstr_get(x_140, 0);
lean::inc(x_288);
lean::dec(x_140);
x_291 = l_Lean_Elaborator_mangleIdent(x_288);
x_292 = lean::cnstr_get(x_39, 3);
lean::inc(x_292);
lean::dec(x_39);
x_295 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4(x_292, x_291);
if (lean::obj_tag(x_295) == 0)
{
obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_304; obj* x_305; obj* x_306; 
lean::dec(x_38);
lean::dec(x_43);
if (lean::is_scalar(x_64)) {
 x_298 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_298 = x_64;
}
lean::cnstr_set(x_298, 0, x_0);
x_299 = l_Lean_Name_toString___closed__1;
x_300 = l_Lean_Name_toStringWithSep___main(x_299, x_291);
x_301 = l_Lean_Elaborator_toLevel___main___closed__4;
x_302 = lean::string_append(x_301, x_300);
lean::dec(x_300);
x_304 = l_Char_HasRepr___closed__1;
x_305 = lean::string_append(x_302, x_304);
x_306 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_298, x_305, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_298);
return x_306;
}
else
{
obj* x_313; obj* x_314; obj* x_315; 
lean::dec(x_64);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_295);
x_313 = level_mk_param(x_291);
if (lean::is_scalar(x_43)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_43;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_315 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_315 = x_38;
}
lean::cnstr_set(x_315, 0, x_314);
return x_315;
}
}
else
{
obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_23);
lean::dec(x_38);
lean::dec(x_39);
lean::dec(x_43);
lean::dec(x_140);
if (lean::is_scalar(x_64)) {
 x_321 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_321 = x_64;
}
lean::cnstr_set(x_321, 0, x_0);
x_322 = l_Lean_Elaborator_toLevel___main___closed__2;
x_323 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_321, x_322, x_1, x_2, x_41);
lean::dec(x_41);
lean::dec(x_321);
return x_323;
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
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4(x_0, x_1);
lean::dec(x_1);
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
obj* x_47; obj* x_50; obj* x_52; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_37, 0);
lean::inc(x_47);
lean::dec(x_37);
x_50 = lean::cnstr_get(x_47, 0);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 lean::cnstr_set(x_47, 1, lean::box(0));
 x_54 = x_47;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_10, x_1, x_2, x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_12);
lean::dec(x_28);
lean::dec(x_32);
lean::dec(x_50);
lean::dec(x_54);
x_61 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_63 = x_55;
} else {
 lean::inc(x_61);
 lean::dec(x_55);
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
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_65 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_67 = x_55;
} else {
 lean::inc(x_65);
 lean::dec(x_55);
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
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_28);
lean::cnstr_set(x_73, 1, x_50);
x_74 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3___closed__1;
if (lean::is_scalar(x_54)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_54;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
if (lean::is_scalar(x_12)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_12;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_68);
if (lean::is_scalar(x_32)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_32;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
if (lean::is_scalar(x_67)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_67;
}
lean::cnstr_set(x_78, 0, x_77);
return x_78;
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
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
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
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_Lean_Elaborator_mangleIdent(x_58);
x_62 = lean::box(0);
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_64 = l_Lean_KVMap_setName(x_62, x_63, x_61);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_77 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
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
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
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
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_Lean_Elaborator_mangleIdent(x_58);
x_62 = lean::box(0);
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_64 = l_Lean_KVMap_setName(x_62, x_63, x_61);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_77 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
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
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
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
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_Lean_Elaborator_mangleIdent(x_58);
x_62 = lean::box(0);
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_64 = l_Lean_KVMap_setName(x_62, x_63, x_61);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_77 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
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
obj* x_34; obj* x_37; obj* x_39; obj* x_42; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
lean::dec(x_34);
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_15, x_2, x_3, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_37);
lean::dec(x_17);
lean::dec(x_18);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_50 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_52 = x_42;
} else {
 lean::inc(x_50);
 lean::dec(x_42);
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
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_Lean_Elaborator_mangleIdent(x_58);
x_62 = lean::box(0);
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__1;
x_64 = l_Lean_KVMap_setName(x_62, x_63, x_61);
x_65 = lean_expr_mk_mdata(x_64, x_37);
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_53);
if (lean::is_scalar(x_57)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_57;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_55);
if (lean::is_scalar(x_52)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_52;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_12);
x_70 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_72 = x_1;
} else {
 lean::inc(x_70);
 lean::dec(x_1);
 x_72 = lean::box(0);
}
lean::inc(x_0);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_0);
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_3);
x_77 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_74, x_75, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_70);
lean::dec(x_72);
x_84 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_86 = x_77;
} else {
 lean::inc(x_84);
 lean::dec(x_77);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_93; obj* x_96; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_70, x_2, x_3, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_72);
lean::dec(x_91);
x_99 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
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
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_105 = x_96;
} else {
 lean::inc(x_103);
 lean::dec(x_96);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
x_108 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_110 = x_103;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_103);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_72;
}
lean::cnstr_set(x_111, 0, x_91);
lean::cnstr_set(x_111, 1, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
if (lean::is_scalar(x_105)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_105;
}
lean::cnstr_set(x_113, 0, x_112);
return x_113;
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
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_77 = x_66;
} else {
 lean::inc(x_75);
 lean::dec(x_66);
 x_77 = lean::box(0);
}
if (x_20 == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
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
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_0);
lean::dec(x_2);
x_113 = lean::cnstr_get(x_75, 0);
x_115 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_117 = x_75;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_75);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_118, 1, x_115);
if (lean::is_scalar(x_77)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_77;
}
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
obj* x_120; obj* x_121; obj* x_125; obj* x_126; obj* x_128; obj* x_130; 
x_120 = l_Lean_Parser_Term_match_HasView;
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
lean::dec(x_120);
lean::inc(x_0);
x_125 = lean::apply_1(x_121, x_0);
x_126 = lean::cnstr_get(x_125, 5);
lean::inc(x_126);
x_128 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(x_126);
lean::inc(x_2);
x_130 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(x_128, x_1, x_2, x_3);
if (lean::obj_tag(x_130) == 0)
{
obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_125);
x_132 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_134 = x_130;
} else {
 lean::inc(x_132);
 lean::dec(x_130);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
x_13 = x_135;
goto lbl_14;
}
else
{
obj* x_136; obj* x_139; obj* x_141; obj* x_144; obj* x_146; obj* x_149; 
x_136 = lean::cnstr_get(x_130, 0);
lean::inc(x_136);
lean::dec(x_130);
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_136, 1);
lean::inc(x_141);
lean::dec(x_136);
x_144 = lean::cnstr_get(x_125, 2);
lean::inc(x_144);
x_146 = l_Lean_Expander_getOptType___main(x_144);
lean::dec(x_144);
lean::inc(x_2);
x_149 = l_Lean_Elaborator_toPexpr___main(x_146, x_1, x_2, x_141);
if (lean::obj_tag(x_149) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_139);
lean::dec(x_125);
x_152 = lean::cnstr_get(x_149, 0);
if (lean::is_exclusive(x_149)) {
 x_154 = x_149;
} else {
 lean::inc(x_152);
 lean::dec(x_149);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
x_13 = x_155;
goto lbl_14;
}
else
{
obj* x_156; obj* x_159; obj* x_161; obj* x_164; 
x_156 = lean::cnstr_get(x_149, 0);
lean::inc(x_156);
lean::dec(x_149);
x_159 = lean::cnstr_get(x_156, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_156, 1);
lean::inc(x_161);
lean::dec(x_156);
x_164 = l_Lean_Elaborator_mkEqns(x_159, x_139);
switch (lean::obj_tag(x_164)) {
case 10:
{
obj* x_165; obj* x_167; obj* x_170; obj* x_174; 
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
lean::dec(x_164);
x_170 = lean::cnstr_get(x_125, 1);
lean::inc(x_170);
lean::dec(x_125);
lean::inc(x_2);
x_174 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(x_170, x_1, x_2, x_161);
if (lean::obj_tag(x_174) == 0)
{
obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_167);
lean::dec(x_165);
x_177 = lean::cnstr_get(x_174, 0);
if (lean::is_exclusive(x_174)) {
 x_179 = x_174;
} else {
 lean::inc(x_177);
 lean::dec(x_174);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
x_13 = x_180;
goto lbl_14;
}
else
{
obj* x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_188; obj* x_189; uint8 x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_181 = lean::cnstr_get(x_174, 0);
if (lean::is_exclusive(x_174)) {
 x_183 = x_174;
} else {
 lean::inc(x_181);
 lean::dec(x_174);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_181, 0);
x_186 = lean::cnstr_get(x_181, 1);
if (lean::is_exclusive(x_181)) {
 x_188 = x_181;
} else {
 lean::inc(x_184);
 lean::inc(x_186);
 lean::dec(x_181);
 x_188 = lean::box(0);
}
x_189 = l_Lean_Elaborator_toPexpr___main___closed__22;
x_190 = 1;
x_191 = l_Lean_KVMap_setBool(x_165, x_189, x_190);
x_192 = lean_expr_mk_mdata(x_191, x_167);
x_193 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_192, x_184);
if (lean::is_scalar(x_188)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_188;
}
lean::cnstr_set(x_194, 0, x_193);
lean::cnstr_set(x_194, 1, x_186);
if (lean::is_scalar(x_183)) {
 x_195 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_195 = x_183;
}
lean::cnstr_set(x_195, 0, x_194);
x_13 = x_195;
goto lbl_14;
}
}
default:
{
obj* x_199; obj* x_200; obj* x_202; 
lean::dec(x_164);
lean::dec(x_125);
lean::inc(x_0);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_0);
x_200 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6___closed__2;
lean::inc(x_2);
x_202 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_199, x_200, x_1, x_2, x_161);
lean::dec(x_161);
lean::dec(x_199);
x_13 = x_202;
goto lbl_14;
}
}
}
}
}
}
else
{
obj* x_205; obj* x_206; obj* x_210; obj* x_211; obj* x_213; obj* x_214; obj* x_215; obj* x_217; obj* x_220; obj* x_221; 
x_205 = l_Lean_Parser_Term_structInst_HasView;
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
lean::dec(x_205);
lean::inc(x_0);
x_210 = lean::apply_1(x_206, x_0);
x_211 = lean::cnstr_get(x_210, 3);
lean::inc(x_211);
x_213 = lean::box(0);
x_214 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_211, x_213);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
x_220 = l_List_spanAux___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_217, x_213);
x_221 = lean::cnstr_get(x_220, 1);
lean::inc(x_221);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_228; 
x_223 = lean::cnstr_get(x_220, 0);
lean::inc(x_223);
lean::dec(x_220);
lean::inc(x_2);
lean::inc(x_0);
x_228 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_215, x_1, x_2, x_3);
if (lean::obj_tag(x_228) == 0)
{
obj* x_234; obj* x_236; obj* x_237; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_223);
lean::dec(x_210);
x_234 = lean::cnstr_get(x_228, 0);
if (lean::is_exclusive(x_228)) {
 x_236 = x_228;
} else {
 lean::inc(x_234);
 lean::dec(x_228);
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
obj* x_238; obj* x_241; obj* x_243; obj* x_246; obj* x_250; 
x_238 = lean::cnstr_get(x_228, 0);
lean::inc(x_238);
lean::dec(x_228);
x_241 = lean::cnstr_get(x_238, 0);
lean::inc(x_241);
x_243 = lean::cnstr_get(x_238, 1);
lean::inc(x_243);
lean::dec(x_238);
lean::inc(x_2);
lean::inc(x_0);
x_250 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_223, x_1, x_2, x_243);
if (lean::obj_tag(x_250) == 0)
{
obj* x_256; obj* x_258; obj* x_259; 
lean::dec(x_241);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_256 = lean::cnstr_get(x_250, 0);
if (lean::is_exclusive(x_250)) {
 x_258 = x_250;
} else {
 lean::inc(x_256);
 lean::dec(x_250);
 x_258 = lean::box(0);
}
if (lean::is_scalar(x_258)) {
 x_259 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_259 = x_258;
}
lean::cnstr_set(x_259, 0, x_256);
return x_259;
}
else
{
obj* x_260; obj* x_263; 
x_260 = lean::cnstr_get(x_250, 0);
lean::inc(x_260);
lean::dec(x_250);
x_263 = lean::cnstr_get(x_210, 2);
lean::inc(x_263);
if (lean::obj_tag(x_263) == 0)
{
obj* x_265; obj* x_267; obj* x_269; obj* x_270; 
x_265 = lean::cnstr_get(x_260, 0);
x_267 = lean::cnstr_get(x_260, 1);
if (lean::is_exclusive(x_260)) {
 x_269 = x_260;
} else {
 lean::inc(x_265);
 lean::inc(x_267);
 lean::dec(x_260);
 x_269 = lean::box(0);
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_265);
lean::cnstr_set(x_270, 1, x_267);
x_246 = x_270;
goto lbl_247;
}
else
{
obj* x_271; obj* x_273; obj* x_276; obj* x_279; obj* x_283; 
x_271 = lean::cnstr_get(x_260, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_260, 1);
lean::inc(x_273);
lean::dec(x_260);
x_276 = lean::cnstr_get(x_263, 0);
lean::inc(x_276);
lean::dec(x_263);
x_279 = lean::cnstr_get(x_276, 0);
lean::inc(x_279);
lean::dec(x_276);
lean::inc(x_2);
x_283 = l_Lean_Elaborator_toPexpr___main(x_279, x_1, x_2, x_273);
if (lean::obj_tag(x_283) == 0)
{
obj* x_290; obj* x_292; obj* x_293; 
lean::dec(x_241);
lean::dec(x_271);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_290 = lean::cnstr_get(x_283, 0);
if (lean::is_exclusive(x_283)) {
 x_292 = x_283;
} else {
 lean::inc(x_290);
 lean::dec(x_283);
 x_292 = lean::box(0);
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_290);
return x_293;
}
else
{
obj* x_294; obj* x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
x_294 = lean::cnstr_get(x_283, 0);
lean::inc(x_294);
lean::dec(x_283);
x_297 = lean::cnstr_get(x_294, 0);
x_299 = lean::cnstr_get(x_294, 1);
if (lean::is_exclusive(x_294)) {
 x_301 = x_294;
} else {
 lean::inc(x_297);
 lean::inc(x_299);
 lean::dec(x_294);
 x_301 = lean::box(0);
}
x_302 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_302, 0, x_297);
lean::cnstr_set(x_302, 1, x_213);
x_303 = l_List_append___rarg(x_271, x_302);
if (lean::is_scalar(x_301)) {
 x_304 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_304 = x_301;
}
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_299);
x_246 = x_304;
goto lbl_247;
}
}
}
lbl_247:
{
obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; uint8 x_315; obj* x_316; obj* x_317; obj* x_320; obj* x_321; obj* x_322; 
x_305 = lean::cnstr_get(x_246, 0);
x_307 = lean::cnstr_get(x_246, 1);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_set(x_246, 0, lean::box(0));
 lean::cnstr_set(x_246, 1, lean::box(0));
 x_309 = x_246;
} else {
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_246);
 x_309 = lean::box(0);
}
x_310 = lean::mk_nat_obj(0ul);
x_311 = l_List_lengthAux___main___rarg(x_241, x_310);
x_312 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_313 = l_Lean_KVMap_setNat(x_213, x_312, x_311);
x_314 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_315 = 0;
x_316 = l_Lean_KVMap_setBool(x_313, x_314, x_315);
x_317 = lean::cnstr_get(x_210, 1);
lean::inc(x_317);
lean::dec(x_210);
x_320 = l_List_append___rarg(x_241, x_305);
x_321 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_322 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_321, x_320);
if (lean::obj_tag(x_317) == 0)
{
obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_323 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_324 = lean::box(0);
x_325 = l_Lean_KVMap_setName(x_316, x_323, x_324);
x_326 = lean_expr_mk_mdata(x_325, x_322);
if (lean::is_scalar(x_309)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_309;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_307);
x_15 = x_327;
goto lbl_16;
}
else
{
obj* x_328; obj* x_331; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; 
x_328 = lean::cnstr_get(x_317, 0);
lean::inc(x_328);
lean::dec(x_317);
x_331 = lean::cnstr_get(x_328, 0);
lean::inc(x_331);
lean::dec(x_328);
x_334 = l_Lean_Elaborator_mangleIdent(x_331);
x_335 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_336 = l_Lean_KVMap_setName(x_316, x_335, x_334);
x_337 = lean_expr_mk_mdata(x_336, x_322);
if (lean::is_scalar(x_309)) {
 x_338 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_338 = x_309;
}
lean::cnstr_set(x_338, 0, x_337);
lean::cnstr_set(x_338, 1, x_307);
x_15 = x_338;
goto lbl_16;
}
}
}
}
else
{
obj* x_339; obj* x_341; 
x_339 = lean::cnstr_get(x_221, 0);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_339, 0);
lean::inc(x_341);
lean::dec(x_339);
if (lean::obj_tag(x_341) == 0)
{
obj* x_344; obj* x_345; obj* x_348; obj* x_349; obj* x_352; obj* x_353; obj* x_354; obj* x_356; 
if (lean::is_exclusive(x_221)) {
 lean::cnstr_release(x_221, 0);
 lean::cnstr_release(x_221, 1);
 x_344 = x_221;
} else {
 lean::dec(x_221);
 x_344 = lean::box(0);
}
x_345 = lean::cnstr_get(x_220, 0);
lean::inc(x_345);
lean::dec(x_220);
x_348 = l_Lean_Parser_Term_structInstItem_HasView;
x_349 = lean::cnstr_get(x_348, 1);
lean::inc(x_349);
lean::dec(x_348);
x_352 = lean::apply_1(x_349, x_341);
x_353 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_353, 0, x_352);
x_354 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_356 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_353, x_354, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_353);
if (lean::obj_tag(x_356) == 0)
{
obj* x_366; obj* x_368; obj* x_369; 
lean::dec(x_345);
lean::dec(x_344);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_215);
lean::dec(x_210);
x_366 = lean::cnstr_get(x_356, 0);
if (lean::is_exclusive(x_356)) {
 x_368 = x_356;
} else {
 lean::inc(x_366);
 lean::dec(x_356);
 x_368 = lean::box(0);
}
if (lean::is_scalar(x_368)) {
 x_369 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_369 = x_368;
}
lean::cnstr_set(x_369, 0, x_366);
return x_369;
}
else
{
obj* x_370; obj* x_373; obj* x_375; obj* x_380; 
x_370 = lean::cnstr_get(x_356, 0);
lean::inc(x_370);
lean::dec(x_356);
x_373 = lean::cnstr_get(x_370, 0);
lean::inc(x_373);
x_375 = lean::cnstr_get(x_370, 1);
lean::inc(x_375);
lean::dec(x_370);
lean::inc(x_2);
lean::inc(x_0);
x_380 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_215, x_1, x_2, x_375);
if (lean::obj_tag(x_380) == 0)
{
obj* x_388; obj* x_390; obj* x_391; 
lean::dec(x_345);
lean::dec(x_344);
lean::dec(x_8);
lean::dec(x_373);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_388 = lean::cnstr_get(x_380, 0);
if (lean::is_exclusive(x_380)) {
 x_390 = x_380;
} else {
 lean::inc(x_388);
 lean::dec(x_380);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_388);
return x_391;
}
else
{
obj* x_392; obj* x_395; obj* x_397; obj* x_400; obj* x_404; 
x_392 = lean::cnstr_get(x_380, 0);
lean::inc(x_392);
lean::dec(x_380);
x_395 = lean::cnstr_get(x_392, 0);
lean::inc(x_395);
x_397 = lean::cnstr_get(x_392, 1);
lean::inc(x_397);
lean::dec(x_392);
lean::inc(x_2);
lean::inc(x_0);
x_404 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_345, x_1, x_2, x_397);
if (lean::obj_tag(x_404) == 0)
{
obj* x_412; obj* x_414; obj* x_415; 
lean::dec(x_344);
lean::dec(x_8);
lean::dec(x_373);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_395);
lean::dec(x_210);
x_412 = lean::cnstr_get(x_404, 0);
if (lean::is_exclusive(x_404)) {
 x_414 = x_404;
} else {
 lean::inc(x_412);
 lean::dec(x_404);
 x_414 = lean::box(0);
}
if (lean::is_scalar(x_414)) {
 x_415 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_415 = x_414;
}
lean::cnstr_set(x_415, 0, x_412);
return x_415;
}
else
{
obj* x_416; obj* x_419; 
x_416 = lean::cnstr_get(x_404, 0);
lean::inc(x_416);
lean::dec(x_404);
x_419 = lean::cnstr_get(x_210, 2);
lean::inc(x_419);
if (lean::obj_tag(x_419) == 0)
{
obj* x_422; obj* x_424; obj* x_426; obj* x_427; 
lean::dec(x_344);
x_422 = lean::cnstr_get(x_416, 0);
x_424 = lean::cnstr_get(x_416, 1);
if (lean::is_exclusive(x_416)) {
 x_426 = x_416;
} else {
 lean::inc(x_422);
 lean::inc(x_424);
 lean::dec(x_416);
 x_426 = lean::box(0);
}
if (lean::is_scalar(x_426)) {
 x_427 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_427 = x_426;
}
lean::cnstr_set(x_427, 0, x_422);
lean::cnstr_set(x_427, 1, x_424);
x_400 = x_427;
goto lbl_401;
}
else
{
obj* x_428; obj* x_430; obj* x_433; obj* x_436; obj* x_440; 
x_428 = lean::cnstr_get(x_416, 0);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_416, 1);
lean::inc(x_430);
lean::dec(x_416);
x_433 = lean::cnstr_get(x_419, 0);
lean::inc(x_433);
lean::dec(x_419);
x_436 = lean::cnstr_get(x_433, 0);
lean::inc(x_436);
lean::dec(x_433);
lean::inc(x_2);
x_440 = l_Lean_Elaborator_toPexpr___main(x_436, x_1, x_2, x_430);
if (lean::obj_tag(x_440) == 0)
{
obj* x_449; obj* x_451; obj* x_452; 
lean::dec(x_344);
lean::dec(x_8);
lean::dec(x_373);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_395);
lean::dec(x_428);
lean::dec(x_210);
x_449 = lean::cnstr_get(x_440, 0);
if (lean::is_exclusive(x_440)) {
 x_451 = x_440;
} else {
 lean::inc(x_449);
 lean::dec(x_440);
 x_451 = lean::box(0);
}
if (lean::is_scalar(x_451)) {
 x_452 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_452 = x_451;
}
lean::cnstr_set(x_452, 0, x_449);
return x_452;
}
else
{
obj* x_453; obj* x_456; obj* x_458; obj* x_460; obj* x_461; obj* x_462; obj* x_463; 
x_453 = lean::cnstr_get(x_440, 0);
lean::inc(x_453);
lean::dec(x_440);
x_456 = lean::cnstr_get(x_453, 0);
x_458 = lean::cnstr_get(x_453, 1);
if (lean::is_exclusive(x_453)) {
 x_460 = x_453;
} else {
 lean::inc(x_456);
 lean::inc(x_458);
 lean::dec(x_453);
 x_460 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_461 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_461 = x_344;
}
lean::cnstr_set(x_461, 0, x_456);
lean::cnstr_set(x_461, 1, x_213);
x_462 = l_List_append___rarg(x_428, x_461);
if (lean::is_scalar(x_460)) {
 x_463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_463 = x_460;
}
lean::cnstr_set(x_463, 0, x_462);
lean::cnstr_set(x_463, 1, x_458);
x_400 = x_463;
goto lbl_401;
}
}
}
lbl_401:
{
obj* x_464; obj* x_466; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; uint8 x_474; obj* x_475; obj* x_476; obj* x_479; obj* x_480; obj* x_481; 
x_464 = lean::cnstr_get(x_400, 0);
x_466 = lean::cnstr_get(x_400, 1);
if (lean::is_exclusive(x_400)) {
 lean::cnstr_set(x_400, 0, lean::box(0));
 lean::cnstr_set(x_400, 1, lean::box(0));
 x_468 = x_400;
} else {
 lean::inc(x_464);
 lean::inc(x_466);
 lean::dec(x_400);
 x_468 = lean::box(0);
}
x_469 = lean::mk_nat_obj(0ul);
x_470 = l_List_lengthAux___main___rarg(x_395, x_469);
x_471 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_472 = l_Lean_KVMap_setNat(x_213, x_471, x_470);
x_473 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_474 = lean::unbox(x_373);
x_475 = l_Lean_KVMap_setBool(x_472, x_473, x_474);
x_476 = lean::cnstr_get(x_210, 1);
lean::inc(x_476);
lean::dec(x_210);
x_479 = l_List_append___rarg(x_395, x_464);
x_480 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_481 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_480, x_479);
if (lean::obj_tag(x_476) == 0)
{
obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; 
x_482 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_483 = lean::box(0);
x_484 = l_Lean_KVMap_setName(x_475, x_482, x_483);
x_485 = lean_expr_mk_mdata(x_484, x_481);
if (lean::is_scalar(x_468)) {
 x_486 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_486 = x_468;
}
lean::cnstr_set(x_486, 0, x_485);
lean::cnstr_set(x_486, 1, x_466);
x_15 = x_486;
goto lbl_16;
}
else
{
obj* x_487; obj* x_490; obj* x_493; obj* x_494; obj* x_495; obj* x_496; obj* x_497; 
x_487 = lean::cnstr_get(x_476, 0);
lean::inc(x_487);
lean::dec(x_476);
x_490 = lean::cnstr_get(x_487, 0);
lean::inc(x_490);
lean::dec(x_487);
x_493 = l_Lean_Elaborator_mangleIdent(x_490);
x_494 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_495 = l_Lean_KVMap_setName(x_475, x_494, x_493);
x_496 = lean_expr_mk_mdata(x_495, x_481);
if (lean::is_scalar(x_468)) {
 x_497 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_497 = x_468;
}
lean::cnstr_set(x_497, 0, x_496);
lean::cnstr_set(x_497, 1, x_466);
x_15 = x_497;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_498; obj* x_500; 
x_498 = lean::cnstr_get(x_221, 1);
if (lean::is_exclusive(x_221)) {
 lean::cnstr_release(x_221, 0);
 lean::cnstr_set(x_221, 1, lean::box(0));
 x_500 = x_221;
} else {
 lean::inc(x_498);
 lean::dec(x_221);
 x_500 = lean::box(0);
}
if (lean::obj_tag(x_498) == 0)
{
obj* x_502; obj* x_507; 
lean::dec(x_341);
x_502 = lean::cnstr_get(x_220, 0);
lean::inc(x_502);
lean::dec(x_220);
lean::inc(x_2);
lean::inc(x_0);
x_507 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_215, x_1, x_2, x_3);
if (lean::obj_tag(x_507) == 0)
{
obj* x_514; obj* x_516; obj* x_517; 
lean::dec(x_502);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_500);
lean::dec(x_210);
x_514 = lean::cnstr_get(x_507, 0);
if (lean::is_exclusive(x_507)) {
 x_516 = x_507;
} else {
 lean::inc(x_514);
 lean::dec(x_507);
 x_516 = lean::box(0);
}
if (lean::is_scalar(x_516)) {
 x_517 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_517 = x_516;
}
lean::cnstr_set(x_517, 0, x_514);
return x_517;
}
else
{
obj* x_518; obj* x_521; obj* x_523; obj* x_526; obj* x_530; 
x_518 = lean::cnstr_get(x_507, 0);
lean::inc(x_518);
lean::dec(x_507);
x_521 = lean::cnstr_get(x_518, 0);
lean::inc(x_521);
x_523 = lean::cnstr_get(x_518, 1);
lean::inc(x_523);
lean::dec(x_518);
lean::inc(x_2);
lean::inc(x_0);
x_530 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_502, x_1, x_2, x_523);
if (lean::obj_tag(x_530) == 0)
{
obj* x_537; obj* x_539; obj* x_540; 
lean::dec(x_521);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_500);
lean::dec(x_210);
x_537 = lean::cnstr_get(x_530, 0);
if (lean::is_exclusive(x_530)) {
 x_539 = x_530;
} else {
 lean::inc(x_537);
 lean::dec(x_530);
 x_539 = lean::box(0);
}
if (lean::is_scalar(x_539)) {
 x_540 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_540 = x_539;
}
lean::cnstr_set(x_540, 0, x_537);
return x_540;
}
else
{
obj* x_541; obj* x_544; 
x_541 = lean::cnstr_get(x_530, 0);
lean::inc(x_541);
lean::dec(x_530);
x_544 = lean::cnstr_get(x_210, 2);
lean::inc(x_544);
if (lean::obj_tag(x_544) == 0)
{
obj* x_547; obj* x_549; obj* x_551; obj* x_552; 
lean::dec(x_500);
x_547 = lean::cnstr_get(x_541, 0);
x_549 = lean::cnstr_get(x_541, 1);
if (lean::is_exclusive(x_541)) {
 x_551 = x_541;
} else {
 lean::inc(x_547);
 lean::inc(x_549);
 lean::dec(x_541);
 x_551 = lean::box(0);
}
if (lean::is_scalar(x_551)) {
 x_552 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_552 = x_551;
}
lean::cnstr_set(x_552, 0, x_547);
lean::cnstr_set(x_552, 1, x_549);
x_526 = x_552;
goto lbl_527;
}
else
{
obj* x_553; obj* x_555; obj* x_558; obj* x_561; obj* x_565; 
x_553 = lean::cnstr_get(x_541, 0);
lean::inc(x_553);
x_555 = lean::cnstr_get(x_541, 1);
lean::inc(x_555);
lean::dec(x_541);
x_558 = lean::cnstr_get(x_544, 0);
lean::inc(x_558);
lean::dec(x_544);
x_561 = lean::cnstr_get(x_558, 0);
lean::inc(x_561);
lean::dec(x_558);
lean::inc(x_2);
x_565 = l_Lean_Elaborator_toPexpr___main(x_561, x_1, x_2, x_555);
if (lean::obj_tag(x_565) == 0)
{
obj* x_573; obj* x_575; obj* x_576; 
lean::dec(x_553);
lean::dec(x_521);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_500);
lean::dec(x_210);
x_573 = lean::cnstr_get(x_565, 0);
if (lean::is_exclusive(x_565)) {
 x_575 = x_565;
} else {
 lean::inc(x_573);
 lean::dec(x_565);
 x_575 = lean::box(0);
}
if (lean::is_scalar(x_575)) {
 x_576 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_576 = x_575;
}
lean::cnstr_set(x_576, 0, x_573);
return x_576;
}
else
{
obj* x_577; obj* x_580; obj* x_582; obj* x_584; obj* x_585; obj* x_586; obj* x_587; 
x_577 = lean::cnstr_get(x_565, 0);
lean::inc(x_577);
lean::dec(x_565);
x_580 = lean::cnstr_get(x_577, 0);
x_582 = lean::cnstr_get(x_577, 1);
if (lean::is_exclusive(x_577)) {
 x_584 = x_577;
} else {
 lean::inc(x_580);
 lean::inc(x_582);
 lean::dec(x_577);
 x_584 = lean::box(0);
}
if (lean::is_scalar(x_500)) {
 x_585 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_585 = x_500;
}
lean::cnstr_set(x_585, 0, x_580);
lean::cnstr_set(x_585, 1, x_213);
x_586 = l_List_append___rarg(x_553, x_585);
if (lean::is_scalar(x_584)) {
 x_587 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_587 = x_584;
}
lean::cnstr_set(x_587, 0, x_586);
lean::cnstr_set(x_587, 1, x_582);
x_526 = x_587;
goto lbl_527;
}
}
}
lbl_527:
{
obj* x_588; obj* x_590; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; uint8 x_598; obj* x_599; obj* x_600; obj* x_603; obj* x_604; obj* x_605; 
x_588 = lean::cnstr_get(x_526, 0);
x_590 = lean::cnstr_get(x_526, 1);
if (lean::is_exclusive(x_526)) {
 lean::cnstr_set(x_526, 0, lean::box(0));
 lean::cnstr_set(x_526, 1, lean::box(0));
 x_592 = x_526;
} else {
 lean::inc(x_588);
 lean::inc(x_590);
 lean::dec(x_526);
 x_592 = lean::box(0);
}
x_593 = lean::mk_nat_obj(0ul);
x_594 = l_List_lengthAux___main___rarg(x_521, x_593);
x_595 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_596 = l_Lean_KVMap_setNat(x_213, x_595, x_594);
x_597 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_598 = 1;
x_599 = l_Lean_KVMap_setBool(x_596, x_597, x_598);
x_600 = lean::cnstr_get(x_210, 1);
lean::inc(x_600);
lean::dec(x_210);
x_603 = l_List_append___rarg(x_521, x_588);
x_604 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_605 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_604, x_603);
if (lean::obj_tag(x_600) == 0)
{
obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; 
x_606 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_607 = lean::box(0);
x_608 = l_Lean_KVMap_setName(x_599, x_606, x_607);
x_609 = lean_expr_mk_mdata(x_608, x_605);
if (lean::is_scalar(x_592)) {
 x_610 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_610 = x_592;
}
lean::cnstr_set(x_610, 0, x_609);
lean::cnstr_set(x_610, 1, x_590);
x_15 = x_610;
goto lbl_16;
}
else
{
obj* x_611; obj* x_614; obj* x_617; obj* x_618; obj* x_619; obj* x_620; obj* x_621; 
x_611 = lean::cnstr_get(x_600, 0);
lean::inc(x_611);
lean::dec(x_600);
x_614 = lean::cnstr_get(x_611, 0);
lean::inc(x_614);
lean::dec(x_611);
x_617 = l_Lean_Elaborator_mangleIdent(x_614);
x_618 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_619 = l_Lean_KVMap_setName(x_599, x_618, x_617);
x_620 = lean_expr_mk_mdata(x_619, x_605);
if (lean::is_scalar(x_592)) {
 x_621 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_621 = x_592;
}
lean::cnstr_set(x_621, 0, x_620);
lean::cnstr_set(x_621, 1, x_590);
x_15 = x_621;
goto lbl_16;
}
}
}
}
else
{
obj* x_623; obj* x_624; obj* x_627; obj* x_628; obj* x_631; obj* x_632; obj* x_633; obj* x_635; 
lean::dec(x_500);
if (lean::is_exclusive(x_498)) {
 lean::cnstr_release(x_498, 0);
 lean::cnstr_release(x_498, 1);
 x_623 = x_498;
} else {
 lean::dec(x_498);
 x_623 = lean::box(0);
}
x_624 = lean::cnstr_get(x_220, 0);
lean::inc(x_624);
lean::dec(x_220);
x_627 = l_Lean_Parser_Term_structInstItem_HasView;
x_628 = lean::cnstr_get(x_627, 1);
lean::inc(x_628);
lean::dec(x_627);
x_631 = lean::apply_1(x_628, x_341);
x_632 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_632, 0, x_631);
x_633 = l_Lean_Elaborator_toPexpr___main___closed__27;
lean::inc(x_2);
x_635 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_632, x_633, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_632);
if (lean::obj_tag(x_635) == 0)
{
obj* x_645; obj* x_647; obj* x_648; 
lean::dec(x_8);
lean::dec(x_624);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_623);
lean::dec(x_215);
lean::dec(x_210);
x_645 = lean::cnstr_get(x_635, 0);
if (lean::is_exclusive(x_635)) {
 x_647 = x_635;
} else {
 lean::inc(x_645);
 lean::dec(x_635);
 x_647 = lean::box(0);
}
if (lean::is_scalar(x_647)) {
 x_648 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_648 = x_647;
}
lean::cnstr_set(x_648, 0, x_645);
return x_648;
}
else
{
obj* x_649; obj* x_652; obj* x_654; obj* x_659; 
x_649 = lean::cnstr_get(x_635, 0);
lean::inc(x_649);
lean::dec(x_635);
x_652 = lean::cnstr_get(x_649, 0);
lean::inc(x_652);
x_654 = lean::cnstr_get(x_649, 1);
lean::inc(x_654);
lean::dec(x_649);
lean::inc(x_2);
lean::inc(x_0);
x_659 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_215, x_1, x_2, x_654);
if (lean::obj_tag(x_659) == 0)
{
obj* x_667; obj* x_669; obj* x_670; 
lean::dec(x_8);
lean::dec(x_624);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_623);
lean::dec(x_652);
lean::dec(x_210);
x_667 = lean::cnstr_get(x_659, 0);
if (lean::is_exclusive(x_659)) {
 x_669 = x_659;
} else {
 lean::inc(x_667);
 lean::dec(x_659);
 x_669 = lean::box(0);
}
if (lean::is_scalar(x_669)) {
 x_670 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_670 = x_669;
}
lean::cnstr_set(x_670, 0, x_667);
return x_670;
}
else
{
obj* x_671; obj* x_674; obj* x_676; obj* x_679; obj* x_683; 
x_671 = lean::cnstr_get(x_659, 0);
lean::inc(x_671);
lean::dec(x_659);
x_674 = lean::cnstr_get(x_671, 0);
lean::inc(x_674);
x_676 = lean::cnstr_get(x_671, 1);
lean::inc(x_676);
lean::dec(x_671);
lean::inc(x_2);
lean::inc(x_0);
x_683 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_624, x_1, x_2, x_676);
if (lean::obj_tag(x_683) == 0)
{
obj* x_691; obj* x_693; obj* x_694; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_623);
lean::dec(x_652);
lean::dec(x_674);
lean::dec(x_210);
x_691 = lean::cnstr_get(x_683, 0);
if (lean::is_exclusive(x_683)) {
 x_693 = x_683;
} else {
 lean::inc(x_691);
 lean::dec(x_683);
 x_693 = lean::box(0);
}
if (lean::is_scalar(x_693)) {
 x_694 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_694 = x_693;
}
lean::cnstr_set(x_694, 0, x_691);
return x_694;
}
else
{
obj* x_695; obj* x_698; 
x_695 = lean::cnstr_get(x_683, 0);
lean::inc(x_695);
lean::dec(x_683);
x_698 = lean::cnstr_get(x_210, 2);
lean::inc(x_698);
if (lean::obj_tag(x_698) == 0)
{
obj* x_701; obj* x_703; obj* x_705; obj* x_706; 
lean::dec(x_623);
x_701 = lean::cnstr_get(x_695, 0);
x_703 = lean::cnstr_get(x_695, 1);
if (lean::is_exclusive(x_695)) {
 x_705 = x_695;
} else {
 lean::inc(x_701);
 lean::inc(x_703);
 lean::dec(x_695);
 x_705 = lean::box(0);
}
if (lean::is_scalar(x_705)) {
 x_706 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_706 = x_705;
}
lean::cnstr_set(x_706, 0, x_701);
lean::cnstr_set(x_706, 1, x_703);
x_679 = x_706;
goto lbl_680;
}
else
{
obj* x_707; obj* x_709; obj* x_712; obj* x_715; obj* x_719; 
x_707 = lean::cnstr_get(x_695, 0);
lean::inc(x_707);
x_709 = lean::cnstr_get(x_695, 1);
lean::inc(x_709);
lean::dec(x_695);
x_712 = lean::cnstr_get(x_698, 0);
lean::inc(x_712);
lean::dec(x_698);
x_715 = lean::cnstr_get(x_712, 0);
lean::inc(x_715);
lean::dec(x_712);
lean::inc(x_2);
x_719 = l_Lean_Elaborator_toPexpr___main(x_715, x_1, x_2, x_709);
if (lean::obj_tag(x_719) == 0)
{
obj* x_728; obj* x_730; obj* x_731; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_707);
lean::dec(x_623);
lean::dec(x_652);
lean::dec(x_674);
lean::dec(x_210);
x_728 = lean::cnstr_get(x_719, 0);
if (lean::is_exclusive(x_719)) {
 x_730 = x_719;
} else {
 lean::inc(x_728);
 lean::dec(x_719);
 x_730 = lean::box(0);
}
if (lean::is_scalar(x_730)) {
 x_731 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_731 = x_730;
}
lean::cnstr_set(x_731, 0, x_728);
return x_731;
}
else
{
obj* x_732; obj* x_735; obj* x_737; obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
x_732 = lean::cnstr_get(x_719, 0);
lean::inc(x_732);
lean::dec(x_719);
x_735 = lean::cnstr_get(x_732, 0);
x_737 = lean::cnstr_get(x_732, 1);
if (lean::is_exclusive(x_732)) {
 x_739 = x_732;
} else {
 lean::inc(x_735);
 lean::inc(x_737);
 lean::dec(x_732);
 x_739 = lean::box(0);
}
if (lean::is_scalar(x_623)) {
 x_740 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_740 = x_623;
}
lean::cnstr_set(x_740, 0, x_735);
lean::cnstr_set(x_740, 1, x_213);
x_741 = l_List_append___rarg(x_707, x_740);
if (lean::is_scalar(x_739)) {
 x_742 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_742 = x_739;
}
lean::cnstr_set(x_742, 0, x_741);
lean::cnstr_set(x_742, 1, x_737);
x_679 = x_742;
goto lbl_680;
}
}
}
lbl_680:
{
obj* x_743; obj* x_745; obj* x_747; obj* x_748; obj* x_749; obj* x_750; obj* x_751; obj* x_752; uint8 x_753; obj* x_754; obj* x_755; obj* x_758; obj* x_759; obj* x_760; 
x_743 = lean::cnstr_get(x_679, 0);
x_745 = lean::cnstr_get(x_679, 1);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_set(x_679, 0, lean::box(0));
 lean::cnstr_set(x_679, 1, lean::box(0));
 x_747 = x_679;
} else {
 lean::inc(x_743);
 lean::inc(x_745);
 lean::dec(x_679);
 x_747 = lean::box(0);
}
x_748 = lean::mk_nat_obj(0ul);
x_749 = l_List_lengthAux___main___rarg(x_674, x_748);
x_750 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_751 = l_Lean_KVMap_setNat(x_213, x_750, x_749);
x_752 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_753 = lean::unbox(x_652);
x_754 = l_Lean_KVMap_setBool(x_751, x_752, x_753);
x_755 = lean::cnstr_get(x_210, 1);
lean::inc(x_755);
lean::dec(x_210);
x_758 = l_List_append___rarg(x_674, x_743);
x_759 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_760 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_759, x_758);
if (lean::obj_tag(x_755) == 0)
{
obj* x_761; obj* x_762; obj* x_763; obj* x_764; obj* x_765; 
x_761 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_762 = lean::box(0);
x_763 = l_Lean_KVMap_setName(x_754, x_761, x_762);
x_764 = lean_expr_mk_mdata(x_763, x_760);
if (lean::is_scalar(x_747)) {
 x_765 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_765 = x_747;
}
lean::cnstr_set(x_765, 0, x_764);
lean::cnstr_set(x_765, 1, x_745);
x_15 = x_765;
goto lbl_16;
}
else
{
obj* x_766; obj* x_769; obj* x_772; obj* x_773; obj* x_774; obj* x_775; obj* x_776; 
x_766 = lean::cnstr_get(x_755, 0);
lean::inc(x_766);
lean::dec(x_755);
x_769 = lean::cnstr_get(x_766, 0);
lean::inc(x_769);
lean::dec(x_766);
x_772 = l_Lean_Elaborator_mangleIdent(x_769);
x_773 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_774 = l_Lean_KVMap_setName(x_754, x_773, x_772);
x_775 = lean_expr_mk_mdata(x_774, x_760);
if (lean::is_scalar(x_747)) {
 x_776 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_776 = x_747;
}
lean::cnstr_set(x_776, 0, x_775);
lean::cnstr_set(x_776, 1, x_745);
x_15 = x_776;
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
obj* x_779; 
lean::inc(x_2);
lean::inc(x_10);
x_779 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_779) == 0)
{
obj* x_784; obj* x_786; obj* x_787; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_784 = lean::cnstr_get(x_779, 0);
if (lean::is_exclusive(x_779)) {
 x_786 = x_779;
} else {
 lean::inc(x_784);
 lean::dec(x_779);
 x_786 = lean::box(0);
}
if (lean::is_scalar(x_786)) {
 x_787 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_787 = x_786;
}
lean::cnstr_set(x_787, 0, x_784);
return x_787;
}
else
{
obj* x_788; obj* x_791; obj* x_793; obj* x_795; obj* x_796; 
x_788 = lean::cnstr_get(x_779, 0);
lean::inc(x_788);
lean::dec(x_779);
x_791 = lean::cnstr_get(x_788, 0);
x_793 = lean::cnstr_get(x_788, 1);
if (lean::is_exclusive(x_788)) {
 lean::cnstr_set(x_788, 0, lean::box(0));
 lean::cnstr_set(x_788, 1, lean::box(0));
 x_795 = x_788;
} else {
 lean::inc(x_791);
 lean::inc(x_793);
 lean::dec(x_788);
 x_795 = lean::box(0);
}
x_796 = l_List_reverse___rarg(x_791);
if (lean::obj_tag(x_796) == 0)
{
obj* x_800; obj* x_801; obj* x_803; 
lean::dec(x_795);
lean::dec(x_10);
lean::inc(x_0);
x_800 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_800, 0, x_0);
x_801 = l_Lean_Elaborator_toPexpr___main___closed__28;
lean::inc(x_2);
x_803 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_800, x_801, x_1, x_2, x_793);
lean::dec(x_793);
lean::dec(x_800);
if (lean::obj_tag(x_803) == 0)
{
obj* x_809; obj* x_811; obj* x_812; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_809 = lean::cnstr_get(x_803, 0);
if (lean::is_exclusive(x_803)) {
 x_811 = x_803;
} else {
 lean::inc(x_809);
 lean::dec(x_803);
 x_811 = lean::box(0);
}
if (lean::is_scalar(x_811)) {
 x_812 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_812 = x_811;
}
lean::cnstr_set(x_812, 0, x_809);
return x_812;
}
else
{
obj* x_813; 
x_813 = lean::cnstr_get(x_803, 0);
lean::inc(x_813);
lean::dec(x_803);
x_15 = x_813;
goto lbl_16;
}
}
else
{
obj* x_816; obj* x_818; obj* x_821; obj* x_822; obj* x_824; obj* x_825; obj* x_826; obj* x_827; obj* x_828; obj* x_830; obj* x_831; 
x_816 = lean::cnstr_get(x_796, 0);
lean::inc(x_816);
x_818 = lean::cnstr_get(x_796, 1);
lean::inc(x_818);
lean::dec(x_796);
x_821 = lean::mk_nat_obj(0ul);
x_822 = l_List_lengthAux___main___rarg(x_10, x_821);
lean::dec(x_10);
x_824 = lean::box(0);
x_825 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_826 = l_Lean_KVMap_setNat(x_824, x_825, x_822);
x_827 = l_List_reverse___rarg(x_818);
x_828 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_816, x_827);
lean::dec(x_816);
x_830 = lean_expr_mk_mdata(x_826, x_828);
if (lean::is_scalar(x_795)) {
 x_831 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_831 = x_795;
}
lean::cnstr_set(x_831, 0, x_830);
lean::cnstr_set(x_831, 1, x_793);
x_15 = x_831;
goto lbl_16;
}
}
}
}
else
{
obj* x_834; obj* x_835; obj* x_839; obj* x_840; 
lean::dec(x_8);
lean::dec(x_10);
x_834 = l_Lean_Parser_stringLit_HasView;
x_835 = lean::cnstr_get(x_834, 0);
lean::inc(x_835);
lean::dec(x_834);
lean::inc(x_0);
x_839 = lean::apply_1(x_835, x_0);
x_840 = l_Lean_Parser_stringLit_View_value(x_839);
if (lean::obj_tag(x_840) == 0)
{
if (x_20 == 0)
{
obj* x_841; 
x_841 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_841) == 0)
{
obj* x_844; obj* x_845; obj* x_846; 
lean::dec(x_2);
x_844 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_845 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_845, 0, x_844);
lean::cnstr_set(x_845, 1, x_3);
x_846 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_846, 0, x_845);
return x_846;
}
else
{
obj* x_847; obj* x_850; obj* x_853; obj* x_856; obj* x_857; obj* x_859; obj* x_860; obj* x_861; obj* x_862; obj* x_865; obj* x_866; obj* x_867; obj* x_868; obj* x_869; obj* x_870; 
x_847 = lean::cnstr_get(x_841, 0);
lean::inc(x_847);
lean::dec(x_841);
x_850 = lean::cnstr_get(x_2, 0);
lean::inc(x_850);
lean::dec(x_2);
x_853 = lean::cnstr_get(x_850, 2);
lean::inc(x_853);
lean::dec(x_850);
x_856 = l_Lean_FileMap_toPosition(x_853, x_847);
x_857 = lean::cnstr_get(x_856, 1);
lean::inc(x_857);
x_859 = lean::box(0);
x_860 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_861 = l_Lean_KVMap_setNat(x_859, x_860, x_857);
x_862 = lean::cnstr_get(x_856, 0);
lean::inc(x_862);
lean::dec(x_856);
x_865 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_866 = l_Lean_KVMap_setNat(x_861, x_865, x_862);
x_867 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_868 = lean_expr_mk_mdata(x_866, x_867);
x_869 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_869, 0, x_868);
lean::cnstr_set(x_869, 1, x_3);
x_870 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_870, 0, x_869);
return x_870;
}
}
else
{
obj* x_873; obj* x_874; obj* x_875; 
lean::dec(x_0);
lean::dec(x_2);
x_873 = l_Lean_Elaborator_toPexpr___main___closed__30;
x_874 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_874, 0, x_873);
lean::cnstr_set(x_874, 1, x_3);
x_875 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_875, 0, x_874);
return x_875;
}
}
else
{
obj* x_876; obj* x_879; obj* x_880; 
x_876 = lean::cnstr_get(x_840, 0);
lean::inc(x_876);
lean::dec(x_840);
x_879 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_879, 0, x_876);
x_880 = lean_expr_mk_lit(x_879);
if (x_20 == 0)
{
obj* x_881; 
x_881 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_881) == 0)
{
obj* x_884; obj* x_885; 
lean::dec(x_2);
x_884 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_884, 0, x_880);
lean::cnstr_set(x_884, 1, x_3);
x_885 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_885, 0, x_884);
return x_885;
}
else
{
obj* x_886; obj* x_889; obj* x_892; obj* x_895; obj* x_896; obj* x_898; obj* x_899; obj* x_900; obj* x_901; obj* x_904; obj* x_905; obj* x_906; obj* x_907; obj* x_908; 
x_886 = lean::cnstr_get(x_881, 0);
lean::inc(x_886);
lean::dec(x_881);
x_889 = lean::cnstr_get(x_2, 0);
lean::inc(x_889);
lean::dec(x_2);
x_892 = lean::cnstr_get(x_889, 2);
lean::inc(x_892);
lean::dec(x_889);
x_895 = l_Lean_FileMap_toPosition(x_892, x_886);
x_896 = lean::cnstr_get(x_895, 1);
lean::inc(x_896);
x_898 = lean::box(0);
x_899 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_900 = l_Lean_KVMap_setNat(x_898, x_899, x_896);
x_901 = lean::cnstr_get(x_895, 0);
lean::inc(x_901);
lean::dec(x_895);
x_904 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_905 = l_Lean_KVMap_setNat(x_900, x_904, x_901);
x_906 = lean_expr_mk_mdata(x_905, x_880);
x_907 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_907, 0, x_906);
lean::cnstr_set(x_907, 1, x_3);
x_908 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_908, 0, x_907);
return x_908;
}
}
else
{
obj* x_911; obj* x_912; 
lean::dec(x_0);
lean::dec(x_2);
x_911 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_911, 0, x_880);
lean::cnstr_set(x_911, 1, x_3);
x_912 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_912, 0, x_911);
return x_912;
}
}
}
}
else
{
obj* x_915; obj* x_916; obj* x_920; obj* x_921; obj* x_922; obj* x_923; 
lean::dec(x_8);
lean::dec(x_10);
x_915 = l_Lean_Parser_number_HasView;
x_916 = lean::cnstr_get(x_915, 0);
lean::inc(x_916);
lean::dec(x_915);
lean::inc(x_0);
x_920 = lean::apply_1(x_916, x_0);
x_921 = l_Lean_Parser_number_View_toNat___main(x_920);
x_922 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_922, 0, x_921);
x_923 = lean_expr_mk_lit(x_922);
if (x_20 == 0)
{
obj* x_924; 
x_924 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_924) == 0)
{
obj* x_927; obj* x_928; 
lean::dec(x_2);
x_927 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_927, 0, x_923);
lean::cnstr_set(x_927, 1, x_3);
x_928 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_928, 0, x_927);
return x_928;
}
else
{
obj* x_929; obj* x_932; obj* x_935; obj* x_938; obj* x_939; obj* x_941; obj* x_942; obj* x_943; obj* x_944; obj* x_947; obj* x_948; obj* x_949; obj* x_950; obj* x_951; 
x_929 = lean::cnstr_get(x_924, 0);
lean::inc(x_929);
lean::dec(x_924);
x_932 = lean::cnstr_get(x_2, 0);
lean::inc(x_932);
lean::dec(x_2);
x_935 = lean::cnstr_get(x_932, 2);
lean::inc(x_935);
lean::dec(x_932);
x_938 = l_Lean_FileMap_toPosition(x_935, x_929);
x_939 = lean::cnstr_get(x_938, 1);
lean::inc(x_939);
x_941 = lean::box(0);
x_942 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_943 = l_Lean_KVMap_setNat(x_941, x_942, x_939);
x_944 = lean::cnstr_get(x_938, 0);
lean::inc(x_944);
lean::dec(x_938);
x_947 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_948 = l_Lean_KVMap_setNat(x_943, x_947, x_944);
x_949 = lean_expr_mk_mdata(x_948, x_923);
x_950 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_950, 0, x_949);
lean::cnstr_set(x_950, 1, x_3);
x_951 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_951, 0, x_950);
return x_951;
}
}
else
{
obj* x_954; obj* x_955; 
lean::dec(x_0);
lean::dec(x_2);
x_954 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_954, 0, x_923);
lean::cnstr_set(x_954, 1, x_3);
x_955 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_955, 0, x_954);
return x_955;
}
}
}
else
{
obj* x_958; obj* x_959; obj* x_963; obj* x_964; obj* x_968; 
lean::dec(x_8);
lean::dec(x_10);
x_958 = l_Lean_Parser_Term_borrowed_HasView;
x_959 = lean::cnstr_get(x_958, 0);
lean::inc(x_959);
lean::dec(x_958);
lean::inc(x_0);
x_963 = lean::apply_1(x_959, x_0);
x_964 = lean::cnstr_get(x_963, 1);
lean::inc(x_964);
lean::dec(x_963);
lean::inc(x_2);
x_968 = l_Lean_Elaborator_toPexpr___main(x_964, x_1, x_2, x_3);
if (lean::obj_tag(x_968) == 0)
{
obj* x_971; obj* x_973; obj* x_974; 
lean::dec(x_0);
lean::dec(x_2);
x_971 = lean::cnstr_get(x_968, 0);
if (lean::is_exclusive(x_968)) {
 x_973 = x_968;
} else {
 lean::inc(x_971);
 lean::dec(x_968);
 x_973 = lean::box(0);
}
if (lean::is_scalar(x_973)) {
 x_974 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_974 = x_973;
}
lean::cnstr_set(x_974, 0, x_971);
return x_974;
}
else
{
obj* x_975; obj* x_977; obj* x_978; obj* x_980; obj* x_982; obj* x_983; obj* x_984; 
x_975 = lean::cnstr_get(x_968, 0);
if (lean::is_exclusive(x_968)) {
 lean::cnstr_set(x_968, 0, lean::box(0));
 x_977 = x_968;
} else {
 lean::inc(x_975);
 lean::dec(x_968);
 x_977 = lean::box(0);
}
x_978 = lean::cnstr_get(x_975, 0);
x_980 = lean::cnstr_get(x_975, 1);
if (lean::is_exclusive(x_975)) {
 lean::cnstr_set(x_975, 0, lean::box(0));
 lean::cnstr_set(x_975, 1, lean::box(0));
 x_982 = x_975;
} else {
 lean::inc(x_978);
 lean::inc(x_980);
 lean::dec(x_975);
 x_982 = lean::box(0);
}
x_983 = l_Lean_Elaborator_toPexpr___main___closed__31;
x_984 = l_Lean_Elaborator_Expr_mkAnnotation(x_983, x_978);
if (x_20 == 0)
{
obj* x_985; 
x_985 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_985) == 0)
{
obj* x_988; obj* x_989; 
lean::dec(x_2);
if (lean::is_scalar(x_982)) {
 x_988 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_988 = x_982;
}
lean::cnstr_set(x_988, 0, x_984);
lean::cnstr_set(x_988, 1, x_980);
if (lean::is_scalar(x_977)) {
 x_989 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_989 = x_977;
}
lean::cnstr_set(x_989, 0, x_988);
return x_989;
}
else
{
obj* x_990; obj* x_993; obj* x_996; obj* x_999; obj* x_1000; obj* x_1002; obj* x_1003; obj* x_1004; obj* x_1005; obj* x_1008; obj* x_1009; obj* x_1010; obj* x_1011; obj* x_1012; 
x_990 = lean::cnstr_get(x_985, 0);
lean::inc(x_990);
lean::dec(x_985);
x_993 = lean::cnstr_get(x_2, 0);
lean::inc(x_993);
lean::dec(x_2);
x_996 = lean::cnstr_get(x_993, 2);
lean::inc(x_996);
lean::dec(x_993);
x_999 = l_Lean_FileMap_toPosition(x_996, x_990);
x_1000 = lean::cnstr_get(x_999, 1);
lean::inc(x_1000);
x_1002 = lean::box(0);
x_1003 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1004 = l_Lean_KVMap_setNat(x_1002, x_1003, x_1000);
x_1005 = lean::cnstr_get(x_999, 0);
lean::inc(x_1005);
lean::dec(x_999);
x_1008 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1009 = l_Lean_KVMap_setNat(x_1004, x_1008, x_1005);
x_1010 = lean_expr_mk_mdata(x_1009, x_984);
if (lean::is_scalar(x_982)) {
 x_1011 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1011 = x_982;
}
lean::cnstr_set(x_1011, 0, x_1010);
lean::cnstr_set(x_1011, 1, x_980);
if (lean::is_scalar(x_977)) {
 x_1012 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1012 = x_977;
}
lean::cnstr_set(x_1012, 0, x_1011);
return x_1012;
}
}
else
{
obj* x_1015; obj* x_1016; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_982)) {
 x_1015 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1015 = x_982;
}
lean::cnstr_set(x_1015, 0, x_984);
lean::cnstr_set(x_1015, 1, x_980);
if (lean::is_scalar(x_977)) {
 x_1016 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1016 = x_977;
}
lean::cnstr_set(x_1016, 0, x_1015);
return x_1016;
}
}
}
}
else
{
obj* x_1019; obj* x_1020; obj* x_1024; obj* x_1025; obj* x_1029; 
lean::dec(x_8);
lean::dec(x_10);
x_1019 = l_Lean_Parser_Term_inaccessible_HasView;
x_1020 = lean::cnstr_get(x_1019, 0);
lean::inc(x_1020);
lean::dec(x_1019);
lean::inc(x_0);
x_1024 = lean::apply_1(x_1020, x_0);
x_1025 = lean::cnstr_get(x_1024, 1);
lean::inc(x_1025);
lean::dec(x_1024);
lean::inc(x_2);
x_1029 = l_Lean_Elaborator_toPexpr___main(x_1025, x_1, x_2, x_3);
if (lean::obj_tag(x_1029) == 0)
{
obj* x_1032; obj* x_1034; obj* x_1035; 
lean::dec(x_0);
lean::dec(x_2);
x_1032 = lean::cnstr_get(x_1029, 0);
if (lean::is_exclusive(x_1029)) {
 x_1034 = x_1029;
} else {
 lean::inc(x_1032);
 lean::dec(x_1029);
 x_1034 = lean::box(0);
}
if (lean::is_scalar(x_1034)) {
 x_1035 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1035 = x_1034;
}
lean::cnstr_set(x_1035, 0, x_1032);
return x_1035;
}
else
{
obj* x_1036; obj* x_1038; obj* x_1039; obj* x_1041; obj* x_1043; obj* x_1044; obj* x_1045; 
x_1036 = lean::cnstr_get(x_1029, 0);
if (lean::is_exclusive(x_1029)) {
 lean::cnstr_set(x_1029, 0, lean::box(0));
 x_1038 = x_1029;
} else {
 lean::inc(x_1036);
 lean::dec(x_1029);
 x_1038 = lean::box(0);
}
x_1039 = lean::cnstr_get(x_1036, 0);
x_1041 = lean::cnstr_get(x_1036, 1);
if (lean::is_exclusive(x_1036)) {
 lean::cnstr_set(x_1036, 0, lean::box(0));
 lean::cnstr_set(x_1036, 1, lean::box(0));
 x_1043 = x_1036;
} else {
 lean::inc(x_1039);
 lean::inc(x_1041);
 lean::dec(x_1036);
 x_1043 = lean::box(0);
}
x_1044 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_1045 = l_Lean_Elaborator_Expr_mkAnnotation(x_1044, x_1039);
if (x_20 == 0)
{
obj* x_1046; 
x_1046 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1046) == 0)
{
obj* x_1049; obj* x_1050; 
lean::dec(x_2);
if (lean::is_scalar(x_1043)) {
 x_1049 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1049 = x_1043;
}
lean::cnstr_set(x_1049, 0, x_1045);
lean::cnstr_set(x_1049, 1, x_1041);
if (lean::is_scalar(x_1038)) {
 x_1050 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1050 = x_1038;
}
lean::cnstr_set(x_1050, 0, x_1049);
return x_1050;
}
else
{
obj* x_1051; obj* x_1054; obj* x_1057; obj* x_1060; obj* x_1061; obj* x_1063; obj* x_1064; obj* x_1065; obj* x_1066; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; obj* x_1073; 
x_1051 = lean::cnstr_get(x_1046, 0);
lean::inc(x_1051);
lean::dec(x_1046);
x_1054 = lean::cnstr_get(x_2, 0);
lean::inc(x_1054);
lean::dec(x_2);
x_1057 = lean::cnstr_get(x_1054, 2);
lean::inc(x_1057);
lean::dec(x_1054);
x_1060 = l_Lean_FileMap_toPosition(x_1057, x_1051);
x_1061 = lean::cnstr_get(x_1060, 1);
lean::inc(x_1061);
x_1063 = lean::box(0);
x_1064 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1065 = l_Lean_KVMap_setNat(x_1063, x_1064, x_1061);
x_1066 = lean::cnstr_get(x_1060, 0);
lean::inc(x_1066);
lean::dec(x_1060);
x_1069 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1070 = l_Lean_KVMap_setNat(x_1065, x_1069, x_1066);
x_1071 = lean_expr_mk_mdata(x_1070, x_1045);
if (lean::is_scalar(x_1043)) {
 x_1072 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1072 = x_1043;
}
lean::cnstr_set(x_1072, 0, x_1071);
lean::cnstr_set(x_1072, 1, x_1041);
if (lean::is_scalar(x_1038)) {
 x_1073 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1073 = x_1038;
}
lean::cnstr_set(x_1073, 0, x_1072);
return x_1073;
}
}
else
{
obj* x_1076; obj* x_1077; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1043)) {
 x_1076 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1076 = x_1043;
}
lean::cnstr_set(x_1076, 0, x_1045);
lean::cnstr_set(x_1076, 1, x_1041);
if (lean::is_scalar(x_1038)) {
 x_1077 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1077 = x_1038;
}
lean::cnstr_set(x_1077, 0, x_1076);
return x_1077;
}
}
}
}
else
{
obj* x_1080; obj* x_1081; obj* x_1085; obj* x_1086; obj* x_1088; obj* x_1089; obj* x_1092; obj* x_1095; 
lean::dec(x_8);
lean::dec(x_10);
x_1080 = l_Lean_Parser_Term_explicit_HasView;
x_1081 = lean::cnstr_get(x_1080, 0);
lean::inc(x_1081);
lean::dec(x_1080);
lean::inc(x_0);
x_1085 = lean::apply_1(x_1081, x_0);
x_1086 = lean::cnstr_get(x_1085, 0);
lean::inc(x_1086);
x_1088 = l_Lean_Parser_identUnivs_HasView;
x_1089 = lean::cnstr_get(x_1088, 1);
lean::inc(x_1089);
lean::dec(x_1088);
x_1092 = lean::cnstr_get(x_1085, 1);
lean::inc(x_1092);
lean::dec(x_1085);
x_1095 = lean::apply_1(x_1089, x_1092);
if (lean::obj_tag(x_1086) == 0)
{
obj* x_1098; 
lean::dec(x_1086);
lean::inc(x_2);
x_1098 = l_Lean_Elaborator_toPexpr___main(x_1095, x_1, x_2, x_3);
if (lean::obj_tag(x_1098) == 0)
{
obj* x_1101; obj* x_1103; obj* x_1104; 
lean::dec(x_0);
lean::dec(x_2);
x_1101 = lean::cnstr_get(x_1098, 0);
if (lean::is_exclusive(x_1098)) {
 x_1103 = x_1098;
} else {
 lean::inc(x_1101);
 lean::dec(x_1098);
 x_1103 = lean::box(0);
}
if (lean::is_scalar(x_1103)) {
 x_1104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1104 = x_1103;
}
lean::cnstr_set(x_1104, 0, x_1101);
return x_1104;
}
else
{
obj* x_1105; obj* x_1107; obj* x_1108; obj* x_1110; obj* x_1112; obj* x_1113; obj* x_1114; 
x_1105 = lean::cnstr_get(x_1098, 0);
if (lean::is_exclusive(x_1098)) {
 lean::cnstr_set(x_1098, 0, lean::box(0));
 x_1107 = x_1098;
} else {
 lean::inc(x_1105);
 lean::dec(x_1098);
 x_1107 = lean::box(0);
}
x_1108 = lean::cnstr_get(x_1105, 0);
x_1110 = lean::cnstr_get(x_1105, 1);
if (lean::is_exclusive(x_1105)) {
 lean::cnstr_set(x_1105, 0, lean::box(0));
 lean::cnstr_set(x_1105, 1, lean::box(0));
 x_1112 = x_1105;
} else {
 lean::inc(x_1108);
 lean::inc(x_1110);
 lean::dec(x_1105);
 x_1112 = lean::box(0);
}
x_1113 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_1114 = l_Lean_Elaborator_Expr_mkAnnotation(x_1113, x_1108);
if (x_20 == 0)
{
obj* x_1115; 
x_1115 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1115) == 0)
{
obj* x_1118; obj* x_1119; 
lean::dec(x_2);
if (lean::is_scalar(x_1112)) {
 x_1118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1118 = x_1112;
}
lean::cnstr_set(x_1118, 0, x_1114);
lean::cnstr_set(x_1118, 1, x_1110);
if (lean::is_scalar(x_1107)) {
 x_1119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1119 = x_1107;
}
lean::cnstr_set(x_1119, 0, x_1118);
return x_1119;
}
else
{
obj* x_1120; obj* x_1123; obj* x_1126; obj* x_1129; obj* x_1130; obj* x_1132; obj* x_1133; obj* x_1134; obj* x_1135; obj* x_1138; obj* x_1139; obj* x_1140; obj* x_1141; obj* x_1142; 
x_1120 = lean::cnstr_get(x_1115, 0);
lean::inc(x_1120);
lean::dec(x_1115);
x_1123 = lean::cnstr_get(x_2, 0);
lean::inc(x_1123);
lean::dec(x_2);
x_1126 = lean::cnstr_get(x_1123, 2);
lean::inc(x_1126);
lean::dec(x_1123);
x_1129 = l_Lean_FileMap_toPosition(x_1126, x_1120);
x_1130 = lean::cnstr_get(x_1129, 1);
lean::inc(x_1130);
x_1132 = lean::box(0);
x_1133 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1134 = l_Lean_KVMap_setNat(x_1132, x_1133, x_1130);
x_1135 = lean::cnstr_get(x_1129, 0);
lean::inc(x_1135);
lean::dec(x_1129);
x_1138 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1139 = l_Lean_KVMap_setNat(x_1134, x_1138, x_1135);
x_1140 = lean_expr_mk_mdata(x_1139, x_1114);
if (lean::is_scalar(x_1112)) {
 x_1141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1141 = x_1112;
}
lean::cnstr_set(x_1141, 0, x_1140);
lean::cnstr_set(x_1141, 1, x_1110);
if (lean::is_scalar(x_1107)) {
 x_1142 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1142 = x_1107;
}
lean::cnstr_set(x_1142, 0, x_1141);
return x_1142;
}
}
else
{
obj* x_1145; obj* x_1146; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1112)) {
 x_1145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1145 = x_1112;
}
lean::cnstr_set(x_1145, 0, x_1114);
lean::cnstr_set(x_1145, 1, x_1110);
if (lean::is_scalar(x_1107)) {
 x_1146 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1146 = x_1107;
}
lean::cnstr_set(x_1146, 0, x_1145);
return x_1146;
}
}
}
else
{
obj* x_1149; 
lean::dec(x_1086);
lean::inc(x_2);
x_1149 = l_Lean_Elaborator_toPexpr___main(x_1095, x_1, x_2, x_3);
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
obj* x_1156; obj* x_1158; obj* x_1159; obj* x_1161; obj* x_1163; obj* x_1164; obj* x_1165; 
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
if (x_20 == 0)
{
obj* x_1166; 
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
else
{
obj* x_1196; obj* x_1197; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1163)) {
 x_1196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1196 = x_1163;
}
lean::cnstr_set(x_1196, 0, x_1165);
lean::cnstr_set(x_1196, 1, x_1161);
if (lean::is_scalar(x_1158)) {
 x_1197 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1197 = x_1158;
}
lean::cnstr_set(x_1197, 0, x_1196);
return x_1197;
}
}
}
}
}
else
{
obj* x_1200; obj* x_1201; obj* x_1205; obj* x_1206; 
lean::dec(x_8);
lean::dec(x_10);
x_1200 = l_Lean_Parser_Term_projection_HasView;
x_1201 = lean::cnstr_get(x_1200, 0);
lean::inc(x_1201);
lean::dec(x_1200);
lean::inc(x_0);
x_1205 = lean::apply_1(x_1201, x_0);
x_1206 = lean::cnstr_get(x_1205, 2);
lean::inc(x_1206);
if (lean::obj_tag(x_1206) == 0)
{
obj* x_1208; obj* x_1211; obj* x_1215; 
x_1208 = lean::cnstr_get(x_1205, 0);
lean::inc(x_1208);
lean::dec(x_1205);
x_1211 = lean::cnstr_get(x_1206, 0);
lean::inc(x_1211);
lean::dec(x_1206);
lean::inc(x_2);
x_1215 = l_Lean_Elaborator_toPexpr___main(x_1208, x_1, x_2, x_3);
if (lean::obj_tag(x_1215) == 0)
{
obj* x_1219; obj* x_1221; obj* x_1222; 
lean::dec(x_1211);
lean::dec(x_0);
lean::dec(x_2);
x_1219 = lean::cnstr_get(x_1215, 0);
if (lean::is_exclusive(x_1215)) {
 x_1221 = x_1215;
} else {
 lean::inc(x_1219);
 lean::dec(x_1215);
 x_1221 = lean::box(0);
}
if (lean::is_scalar(x_1221)) {
 x_1222 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1222 = x_1221;
}
lean::cnstr_set(x_1222, 0, x_1219);
return x_1222;
}
else
{
obj* x_1223; obj* x_1225; obj* x_1226; obj* x_1228; obj* x_1230; obj* x_1231; obj* x_1234; obj* x_1235; obj* x_1236; obj* x_1237; obj* x_1238; 
x_1223 = lean::cnstr_get(x_1215, 0);
if (lean::is_exclusive(x_1215)) {
 lean::cnstr_set(x_1215, 0, lean::box(0));
 x_1225 = x_1215;
} else {
 lean::inc(x_1223);
 lean::dec(x_1215);
 x_1225 = lean::box(0);
}
x_1226 = lean::cnstr_get(x_1223, 0);
x_1228 = lean::cnstr_get(x_1223, 1);
if (lean::is_exclusive(x_1223)) {
 lean::cnstr_set(x_1223, 0, lean::box(0));
 lean::cnstr_set(x_1223, 1, lean::box(0));
 x_1230 = x_1223;
} else {
 lean::inc(x_1226);
 lean::inc(x_1228);
 lean::dec(x_1223);
 x_1230 = lean::box(0);
}
x_1231 = lean::cnstr_get(x_1211, 2);
lean::inc(x_1231);
lean::dec(x_1211);
x_1234 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1234, 0, x_1231);
x_1235 = lean::box(0);
x_1236 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1237 = l_Lean_KVMap_insertCore___main(x_1235, x_1236, x_1234);
x_1238 = lean_expr_mk_mdata(x_1237, x_1226);
if (x_20 == 0)
{
obj* x_1239; 
x_1239 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1239) == 0)
{
obj* x_1242; obj* x_1243; 
lean::dec(x_2);
if (lean::is_scalar(x_1230)) {
 x_1242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1242 = x_1230;
}
lean::cnstr_set(x_1242, 0, x_1238);
lean::cnstr_set(x_1242, 1, x_1228);
if (lean::is_scalar(x_1225)) {
 x_1243 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1243 = x_1225;
}
lean::cnstr_set(x_1243, 0, x_1242);
return x_1243;
}
else
{
obj* x_1244; obj* x_1247; obj* x_1250; obj* x_1253; obj* x_1254; obj* x_1256; obj* x_1257; obj* x_1258; obj* x_1261; obj* x_1262; obj* x_1263; obj* x_1264; obj* x_1265; 
x_1244 = lean::cnstr_get(x_1239, 0);
lean::inc(x_1244);
lean::dec(x_1239);
x_1247 = lean::cnstr_get(x_2, 0);
lean::inc(x_1247);
lean::dec(x_2);
x_1250 = lean::cnstr_get(x_1247, 2);
lean::inc(x_1250);
lean::dec(x_1247);
x_1253 = l_Lean_FileMap_toPosition(x_1250, x_1244);
x_1254 = lean::cnstr_get(x_1253, 1);
lean::inc(x_1254);
x_1256 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1257 = l_Lean_KVMap_setNat(x_1235, x_1256, x_1254);
x_1258 = lean::cnstr_get(x_1253, 0);
lean::inc(x_1258);
lean::dec(x_1253);
x_1261 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1262 = l_Lean_KVMap_setNat(x_1257, x_1261, x_1258);
x_1263 = lean_expr_mk_mdata(x_1262, x_1238);
if (lean::is_scalar(x_1230)) {
 x_1264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1264 = x_1230;
}
lean::cnstr_set(x_1264, 0, x_1263);
lean::cnstr_set(x_1264, 1, x_1228);
if (lean::is_scalar(x_1225)) {
 x_1265 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1265 = x_1225;
}
lean::cnstr_set(x_1265, 0, x_1264);
return x_1265;
}
}
else
{
obj* x_1268; obj* x_1269; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1230)) {
 x_1268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1268 = x_1230;
}
lean::cnstr_set(x_1268, 0, x_1238);
lean::cnstr_set(x_1268, 1, x_1228);
if (lean::is_scalar(x_1225)) {
 x_1269 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1269 = x_1225;
}
lean::cnstr_set(x_1269, 0, x_1268);
return x_1269;
}
}
}
else
{
obj* x_1270; obj* x_1273; obj* x_1277; 
x_1270 = lean::cnstr_get(x_1205, 0);
lean::inc(x_1270);
lean::dec(x_1205);
x_1273 = lean::cnstr_get(x_1206, 0);
lean::inc(x_1273);
lean::dec(x_1206);
lean::inc(x_2);
x_1277 = l_Lean_Elaborator_toPexpr___main(x_1270, x_1, x_2, x_3);
if (lean::obj_tag(x_1277) == 0)
{
obj* x_1281; obj* x_1283; obj* x_1284; 
lean::dec(x_1273);
lean::dec(x_0);
lean::dec(x_2);
x_1281 = lean::cnstr_get(x_1277, 0);
if (lean::is_exclusive(x_1277)) {
 x_1283 = x_1277;
} else {
 lean::inc(x_1281);
 lean::dec(x_1277);
 x_1283 = lean::box(0);
}
if (lean::is_scalar(x_1283)) {
 x_1284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1284 = x_1283;
}
lean::cnstr_set(x_1284, 0, x_1281);
return x_1284;
}
else
{
obj* x_1285; obj* x_1287; obj* x_1288; obj* x_1290; obj* x_1292; obj* x_1293; obj* x_1294; obj* x_1295; obj* x_1296; obj* x_1297; obj* x_1298; 
x_1285 = lean::cnstr_get(x_1277, 0);
if (lean::is_exclusive(x_1277)) {
 lean::cnstr_set(x_1277, 0, lean::box(0));
 x_1287 = x_1277;
} else {
 lean::inc(x_1285);
 lean::dec(x_1277);
 x_1287 = lean::box(0);
}
x_1288 = lean::cnstr_get(x_1285, 0);
x_1290 = lean::cnstr_get(x_1285, 1);
if (lean::is_exclusive(x_1285)) {
 lean::cnstr_set(x_1285, 0, lean::box(0));
 lean::cnstr_set(x_1285, 1, lean::box(0));
 x_1292 = x_1285;
} else {
 lean::inc(x_1288);
 lean::inc(x_1290);
 lean::dec(x_1285);
 x_1292 = lean::box(0);
}
x_1293 = l_Lean_Parser_number_View_toNat___main(x_1273);
x_1294 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1294, 0, x_1293);
x_1295 = lean::box(0);
x_1296 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1297 = l_Lean_KVMap_insertCore___main(x_1295, x_1296, x_1294);
x_1298 = lean_expr_mk_mdata(x_1297, x_1288);
if (x_20 == 0)
{
obj* x_1299; 
x_1299 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1299) == 0)
{
obj* x_1302; obj* x_1303; 
lean::dec(x_2);
if (lean::is_scalar(x_1292)) {
 x_1302 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1302 = x_1292;
}
lean::cnstr_set(x_1302, 0, x_1298);
lean::cnstr_set(x_1302, 1, x_1290);
if (lean::is_scalar(x_1287)) {
 x_1303 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1303 = x_1287;
}
lean::cnstr_set(x_1303, 0, x_1302);
return x_1303;
}
else
{
obj* x_1304; obj* x_1307; obj* x_1310; obj* x_1313; obj* x_1314; obj* x_1316; obj* x_1317; obj* x_1318; obj* x_1321; obj* x_1322; obj* x_1323; obj* x_1324; obj* x_1325; 
x_1304 = lean::cnstr_get(x_1299, 0);
lean::inc(x_1304);
lean::dec(x_1299);
x_1307 = lean::cnstr_get(x_2, 0);
lean::inc(x_1307);
lean::dec(x_2);
x_1310 = lean::cnstr_get(x_1307, 2);
lean::inc(x_1310);
lean::dec(x_1307);
x_1313 = l_Lean_FileMap_toPosition(x_1310, x_1304);
x_1314 = lean::cnstr_get(x_1313, 1);
lean::inc(x_1314);
x_1316 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1317 = l_Lean_KVMap_setNat(x_1295, x_1316, x_1314);
x_1318 = lean::cnstr_get(x_1313, 0);
lean::inc(x_1318);
lean::dec(x_1313);
x_1321 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1322 = l_Lean_KVMap_setNat(x_1317, x_1321, x_1318);
x_1323 = lean_expr_mk_mdata(x_1322, x_1298);
if (lean::is_scalar(x_1292)) {
 x_1324 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1324 = x_1292;
}
lean::cnstr_set(x_1324, 0, x_1323);
lean::cnstr_set(x_1324, 1, x_1290);
if (lean::is_scalar(x_1287)) {
 x_1325 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1325 = x_1287;
}
lean::cnstr_set(x_1325, 0, x_1324);
return x_1325;
}
}
else
{
obj* x_1328; obj* x_1329; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1292)) {
 x_1328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1328 = x_1292;
}
lean::cnstr_set(x_1328, 0, x_1298);
lean::cnstr_set(x_1328, 1, x_1290);
if (lean::is_scalar(x_1287)) {
 x_1329 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1329 = x_1287;
}
lean::cnstr_set(x_1329, 0, x_1328);
return x_1329;
}
}
}
}
}
else
{
obj* x_1331; obj* x_1332; obj* x_1336; obj* x_1337; 
lean::dec(x_10);
x_1331 = l_Lean_Parser_Term_let_HasView;
x_1332 = lean::cnstr_get(x_1331, 0);
lean::inc(x_1332);
lean::dec(x_1331);
lean::inc(x_0);
x_1336 = lean::apply_1(x_1332, x_0);
x_1337 = lean::cnstr_get(x_1336, 1);
lean::inc(x_1337);
if (lean::obj_tag(x_1337) == 0)
{
obj* x_1339; obj* x_1342; 
x_1339 = lean::cnstr_get(x_1337, 0);
lean::inc(x_1339);
lean::dec(x_1337);
x_1342 = lean::cnstr_get(x_1339, 1);
lean::inc(x_1342);
if (lean::obj_tag(x_1342) == 0)
{
obj* x_1344; 
x_1344 = lean::cnstr_get(x_1339, 2);
lean::inc(x_1344);
if (lean::obj_tag(x_1344) == 0)
{
obj* x_1349; obj* x_1350; obj* x_1352; 
lean::dec(x_1336);
lean::dec(x_1339);
lean::inc(x_0);
x_1349 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1349, 0, x_0);
x_1350 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1352 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1349, x_1350, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1349);
if (lean::obj_tag(x_1352) == 0)
{
obj* x_1358; obj* x_1360; obj* x_1361; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1358 = lean::cnstr_get(x_1352, 0);
if (lean::is_exclusive(x_1352)) {
 x_1360 = x_1352;
} else {
 lean::inc(x_1358);
 lean::dec(x_1352);
 x_1360 = lean::box(0);
}
if (lean::is_scalar(x_1360)) {
 x_1361 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1361 = x_1360;
}
lean::cnstr_set(x_1361, 0, x_1358);
return x_1361;
}
else
{
obj* x_1362; 
x_1362 = lean::cnstr_get(x_1352, 0);
lean::inc(x_1362);
lean::dec(x_1352);
x_15 = x_1362;
goto lbl_16;
}
}
else
{
obj* x_1365; obj* x_1368; obj* x_1371; obj* x_1375; 
x_1365 = lean::cnstr_get(x_1339, 0);
lean::inc(x_1365);
lean::dec(x_1339);
x_1368 = lean::cnstr_get(x_1344, 0);
lean::inc(x_1368);
lean::dec(x_1344);
x_1371 = lean::cnstr_get(x_1368, 1);
lean::inc(x_1371);
lean::dec(x_1368);
lean::inc(x_2);
x_1375 = l_Lean_Elaborator_toPexpr___main(x_1371, x_1, x_2, x_3);
if (lean::obj_tag(x_1375) == 0)
{
obj* x_1381; obj* x_1383; obj* x_1384; 
lean::dec(x_1336);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1365);
x_1381 = lean::cnstr_get(x_1375, 0);
if (lean::is_exclusive(x_1375)) {
 x_1383 = x_1375;
} else {
 lean::inc(x_1381);
 lean::dec(x_1375);
 x_1383 = lean::box(0);
}
if (lean::is_scalar(x_1383)) {
 x_1384 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1384 = x_1383;
}
lean::cnstr_set(x_1384, 0, x_1381);
return x_1384;
}
else
{
obj* x_1385; obj* x_1388; obj* x_1390; obj* x_1393; obj* x_1396; 
x_1385 = lean::cnstr_get(x_1375, 0);
lean::inc(x_1385);
lean::dec(x_1375);
x_1388 = lean::cnstr_get(x_1385, 0);
lean::inc(x_1388);
x_1390 = lean::cnstr_get(x_1385, 1);
lean::inc(x_1390);
lean::dec(x_1385);
x_1393 = lean::cnstr_get(x_1336, 3);
lean::inc(x_1393);
lean::inc(x_2);
x_1396 = l_Lean_Elaborator_toPexpr___main(x_1393, x_1, x_2, x_1390);
if (lean::obj_tag(x_1396) == 0)
{
obj* x_1403; obj* x_1405; obj* x_1406; 
lean::dec(x_1336);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1365);
lean::dec(x_1388);
x_1403 = lean::cnstr_get(x_1396, 0);
if (lean::is_exclusive(x_1396)) {
 x_1405 = x_1396;
} else {
 lean::inc(x_1403);
 lean::dec(x_1396);
 x_1405 = lean::box(0);
}
if (lean::is_scalar(x_1405)) {
 x_1406 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1406 = x_1405;
}
lean::cnstr_set(x_1406, 0, x_1403);
return x_1406;
}
else
{
obj* x_1407; obj* x_1410; obj* x_1412; obj* x_1415; obj* x_1419; 
x_1407 = lean::cnstr_get(x_1396, 0);
lean::inc(x_1407);
lean::dec(x_1396);
x_1410 = lean::cnstr_get(x_1407, 0);
lean::inc(x_1410);
x_1412 = lean::cnstr_get(x_1407, 1);
lean::inc(x_1412);
lean::dec(x_1407);
x_1415 = lean::cnstr_get(x_1336, 5);
lean::inc(x_1415);
lean::dec(x_1336);
lean::inc(x_2);
x_1419 = l_Lean_Elaborator_toPexpr___main(x_1415, x_1, x_2, x_1412);
if (lean::obj_tag(x_1419) == 0)
{
obj* x_1426; obj* x_1428; obj* x_1429; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1365);
lean::dec(x_1410);
lean::dec(x_1388);
x_1426 = lean::cnstr_get(x_1419, 0);
if (lean::is_exclusive(x_1419)) {
 x_1428 = x_1419;
} else {
 lean::inc(x_1426);
 lean::dec(x_1419);
 x_1428 = lean::box(0);
}
if (lean::is_scalar(x_1428)) {
 x_1429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1429 = x_1428;
}
lean::cnstr_set(x_1429, 0, x_1426);
return x_1429;
}
else
{
obj* x_1430; obj* x_1433; obj* x_1435; obj* x_1437; obj* x_1438; obj* x_1439; obj* x_1440; 
x_1430 = lean::cnstr_get(x_1419, 0);
lean::inc(x_1430);
lean::dec(x_1419);
x_1433 = lean::cnstr_get(x_1430, 0);
x_1435 = lean::cnstr_get(x_1430, 1);
if (lean::is_exclusive(x_1430)) {
 x_1437 = x_1430;
} else {
 lean::inc(x_1433);
 lean::inc(x_1435);
 lean::dec(x_1430);
 x_1437 = lean::box(0);
}
x_1438 = l_Lean_Elaborator_mangleIdent(x_1365);
x_1439 = lean_expr_mk_let(x_1438, x_1388, x_1410, x_1433);
if (lean::is_scalar(x_1437)) {
 x_1440 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1440 = x_1437;
}
lean::cnstr_set(x_1440, 0, x_1439);
lean::cnstr_set(x_1440, 1, x_1435);
x_15 = x_1440;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1445; obj* x_1446; obj* x_1448; 
lean::dec(x_1336);
lean::dec(x_1339);
lean::dec(x_1342);
lean::inc(x_0);
x_1445 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1445, 0, x_0);
x_1446 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1448 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1445, x_1446, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1445);
if (lean::obj_tag(x_1448) == 0)
{
obj* x_1454; obj* x_1456; obj* x_1457; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1454 = lean::cnstr_get(x_1448, 0);
if (lean::is_exclusive(x_1448)) {
 x_1456 = x_1448;
} else {
 lean::inc(x_1454);
 lean::dec(x_1448);
 x_1456 = lean::box(0);
}
if (lean::is_scalar(x_1456)) {
 x_1457 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1457 = x_1456;
}
lean::cnstr_set(x_1457, 0, x_1454);
return x_1457;
}
else
{
obj* x_1458; 
x_1458 = lean::cnstr_get(x_1448, 0);
lean::inc(x_1458);
lean::dec(x_1448);
x_15 = x_1458;
goto lbl_16;
}
}
}
else
{
obj* x_1464; obj* x_1465; obj* x_1467; 
lean::dec(x_1336);
lean::dec(x_1337);
lean::inc(x_0);
x_1464 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1464, 0, x_0);
x_1465 = l_Lean_Elaborator_toPexpr___main___closed__35;
lean::inc(x_2);
x_1467 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1464, x_1465, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1464);
if (lean::obj_tag(x_1467) == 0)
{
obj* x_1473; obj* x_1475; obj* x_1476; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1473 = lean::cnstr_get(x_1467, 0);
if (lean::is_exclusive(x_1467)) {
 x_1475 = x_1467;
} else {
 lean::inc(x_1473);
 lean::dec(x_1467);
 x_1475 = lean::box(0);
}
if (lean::is_scalar(x_1475)) {
 x_1476 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1476 = x_1475;
}
lean::cnstr_set(x_1476, 0, x_1473);
return x_1476;
}
else
{
obj* x_1477; 
x_1477 = lean::cnstr_get(x_1467, 0);
lean::inc(x_1477);
lean::dec(x_1467);
x_15 = x_1477;
goto lbl_16;
}
}
}
}
else
{
obj* x_1482; obj* x_1483; obj* x_1487; obj* x_1488; obj* x_1491; 
lean::dec(x_8);
lean::dec(x_10);
x_1482 = l_Lean_Parser_Term_show_HasView;
x_1483 = lean::cnstr_get(x_1482, 0);
lean::inc(x_1483);
lean::dec(x_1482);
lean::inc(x_0);
x_1487 = lean::apply_1(x_1483, x_0);
x_1488 = lean::cnstr_get(x_1487, 1);
lean::inc(x_1488);
lean::inc(x_2);
x_1491 = l_Lean_Elaborator_toPexpr___main(x_1488, x_1, x_2, x_3);
if (lean::obj_tag(x_1491) == 0)
{
obj* x_1495; obj* x_1497; obj* x_1498; 
lean::dec(x_1487);
lean::dec(x_0);
lean::dec(x_2);
x_1495 = lean::cnstr_get(x_1491, 0);
if (lean::is_exclusive(x_1491)) {
 x_1497 = x_1491;
} else {
 lean::inc(x_1495);
 lean::dec(x_1491);
 x_1497 = lean::box(0);
}
if (lean::is_scalar(x_1497)) {
 x_1498 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1498 = x_1497;
}
lean::cnstr_set(x_1498, 0, x_1495);
return x_1498;
}
else
{
obj* x_1499; obj* x_1502; obj* x_1504; obj* x_1507; obj* x_1510; obj* x_1514; 
x_1499 = lean::cnstr_get(x_1491, 0);
lean::inc(x_1499);
lean::dec(x_1491);
x_1502 = lean::cnstr_get(x_1499, 0);
lean::inc(x_1502);
x_1504 = lean::cnstr_get(x_1499, 1);
lean::inc(x_1504);
lean::dec(x_1499);
x_1507 = lean::cnstr_get(x_1487, 3);
lean::inc(x_1507);
lean::dec(x_1487);
x_1510 = lean::cnstr_get(x_1507, 1);
lean::inc(x_1510);
lean::dec(x_1507);
lean::inc(x_2);
x_1514 = l_Lean_Elaborator_toPexpr___main(x_1510, x_1, x_2, x_1504);
if (lean::obj_tag(x_1514) == 0)
{
obj* x_1518; obj* x_1520; obj* x_1521; 
lean::dec(x_1502);
lean::dec(x_0);
lean::dec(x_2);
x_1518 = lean::cnstr_get(x_1514, 0);
if (lean::is_exclusive(x_1514)) {
 x_1520 = x_1514;
} else {
 lean::inc(x_1518);
 lean::dec(x_1514);
 x_1520 = lean::box(0);
}
if (lean::is_scalar(x_1520)) {
 x_1521 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1521 = x_1520;
}
lean::cnstr_set(x_1521, 0, x_1518);
return x_1521;
}
else
{
obj* x_1522; obj* x_1524; obj* x_1525; obj* x_1527; obj* x_1529; obj* x_1530; uint8 x_1531; obj* x_1532; obj* x_1533; obj* x_1534; obj* x_1535; obj* x_1536; 
x_1522 = lean::cnstr_get(x_1514, 0);
if (lean::is_exclusive(x_1514)) {
 lean::cnstr_set(x_1514, 0, lean::box(0));
 x_1524 = x_1514;
} else {
 lean::inc(x_1522);
 lean::dec(x_1514);
 x_1524 = lean::box(0);
}
x_1525 = lean::cnstr_get(x_1522, 0);
x_1527 = lean::cnstr_get(x_1522, 1);
if (lean::is_exclusive(x_1522)) {
 lean::cnstr_set(x_1522, 0, lean::box(0));
 lean::cnstr_set(x_1522, 1, lean::box(0));
 x_1529 = x_1522;
} else {
 lean::inc(x_1525);
 lean::inc(x_1527);
 lean::dec(x_1522);
 x_1529 = lean::box(0);
}
x_1530 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1531 = 0;
x_1532 = l_Lean_Elaborator_toPexpr___main___closed__37;
x_1533 = lean_expr_mk_lambda(x_1530, x_1531, x_1502, x_1532);
x_1534 = lean_expr_mk_app(x_1533, x_1525);
x_1535 = l_Lean_Elaborator_toPexpr___main___closed__38;
x_1536 = l_Lean_Elaborator_Expr_mkAnnotation(x_1535, x_1534);
if (x_20 == 0)
{
obj* x_1537; 
x_1537 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1537) == 0)
{
obj* x_1540; obj* x_1541; 
lean::dec(x_2);
if (lean::is_scalar(x_1529)) {
 x_1540 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1540 = x_1529;
}
lean::cnstr_set(x_1540, 0, x_1536);
lean::cnstr_set(x_1540, 1, x_1527);
if (lean::is_scalar(x_1524)) {
 x_1541 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1541 = x_1524;
}
lean::cnstr_set(x_1541, 0, x_1540);
return x_1541;
}
else
{
obj* x_1542; obj* x_1545; obj* x_1548; obj* x_1551; obj* x_1552; obj* x_1554; obj* x_1555; obj* x_1556; obj* x_1557; obj* x_1560; obj* x_1561; obj* x_1562; obj* x_1563; obj* x_1564; 
x_1542 = lean::cnstr_get(x_1537, 0);
lean::inc(x_1542);
lean::dec(x_1537);
x_1545 = lean::cnstr_get(x_2, 0);
lean::inc(x_1545);
lean::dec(x_2);
x_1548 = lean::cnstr_get(x_1545, 2);
lean::inc(x_1548);
lean::dec(x_1545);
x_1551 = l_Lean_FileMap_toPosition(x_1548, x_1542);
x_1552 = lean::cnstr_get(x_1551, 1);
lean::inc(x_1552);
x_1554 = lean::box(0);
x_1555 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1556 = l_Lean_KVMap_setNat(x_1554, x_1555, x_1552);
x_1557 = lean::cnstr_get(x_1551, 0);
lean::inc(x_1557);
lean::dec(x_1551);
x_1560 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1561 = l_Lean_KVMap_setNat(x_1556, x_1560, x_1557);
x_1562 = lean_expr_mk_mdata(x_1561, x_1536);
if (lean::is_scalar(x_1529)) {
 x_1563 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1563 = x_1529;
}
lean::cnstr_set(x_1563, 0, x_1562);
lean::cnstr_set(x_1563, 1, x_1527);
if (lean::is_scalar(x_1524)) {
 x_1564 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1564 = x_1524;
}
lean::cnstr_set(x_1564, 0, x_1563);
return x_1564;
}
}
else
{
obj* x_1567; obj* x_1568; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1529)) {
 x_1567 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1567 = x_1529;
}
lean::cnstr_set(x_1567, 0, x_1536);
lean::cnstr_set(x_1567, 1, x_1527);
if (lean::is_scalar(x_1524)) {
 x_1568 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1568 = x_1524;
}
lean::cnstr_set(x_1568, 0, x_1567);
return x_1568;
}
}
}
}
}
else
{
obj* x_1570; obj* x_1571; obj* x_1575; obj* x_1576; 
lean::dec(x_10);
x_1570 = l_Lean_Parser_Term_have_HasView;
x_1571 = lean::cnstr_get(x_1570, 0);
lean::inc(x_1571);
lean::dec(x_1570);
lean::inc(x_0);
x_1575 = lean::apply_1(x_1571, x_0);
x_1576 = lean::cnstr_get(x_1575, 1);
lean::inc(x_1576);
if (lean::obj_tag(x_1576) == 0)
{
obj* x_1578; obj* x_1580; obj* x_1583; 
x_1578 = lean::cnstr_get(x_1575, 2);
lean::inc(x_1578);
x_1580 = lean::cnstr_get(x_1575, 5);
lean::inc(x_1580);
lean::inc(x_2);
x_1583 = l_Lean_Elaborator_toPexpr___main(x_1578, x_1, x_2, x_3);
if (lean::obj_tag(x_1583) == 0)
{
obj* x_1589; obj* x_1591; obj* x_1592; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1580);
lean::dec(x_1575);
x_1589 = lean::cnstr_get(x_1583, 0);
if (lean::is_exclusive(x_1583)) {
 x_1591 = x_1583;
} else {
 lean::inc(x_1589);
 lean::dec(x_1583);
 x_1591 = lean::box(0);
}
if (lean::is_scalar(x_1591)) {
 x_1592 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1592 = x_1591;
}
lean::cnstr_set(x_1592, 0, x_1589);
return x_1592;
}
else
{
obj* x_1593; obj* x_1596; obj* x_1598; obj* x_1602; 
x_1593 = lean::cnstr_get(x_1583, 0);
lean::inc(x_1593);
lean::dec(x_1583);
x_1596 = lean::cnstr_get(x_1593, 0);
lean::inc(x_1596);
x_1598 = lean::cnstr_get(x_1593, 1);
lean::inc(x_1598);
lean::dec(x_1593);
lean::inc(x_2);
x_1602 = l_Lean_Elaborator_toPexpr___main(x_1580, x_1, x_2, x_1598);
if (lean::obj_tag(x_1602) == 0)
{
obj* x_1608; obj* x_1610; obj* x_1611; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1575);
lean::dec(x_1596);
x_1608 = lean::cnstr_get(x_1602, 0);
if (lean::is_exclusive(x_1602)) {
 x_1610 = x_1602;
} else {
 lean::inc(x_1608);
 lean::dec(x_1602);
 x_1610 = lean::box(0);
}
if (lean::is_scalar(x_1610)) {
 x_1611 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1611 = x_1610;
}
lean::cnstr_set(x_1611, 0, x_1608);
return x_1611;
}
else
{
obj* x_1612; obj* x_1615; obj* x_1617; obj* x_1620; uint8 x_1621; obj* x_1622; obj* x_1623; 
x_1612 = lean::cnstr_get(x_1602, 0);
lean::inc(x_1612);
lean::dec(x_1602);
x_1615 = lean::cnstr_get(x_1612, 0);
lean::inc(x_1615);
x_1617 = lean::cnstr_get(x_1612, 1);
lean::inc(x_1617);
lean::dec(x_1612);
x_1620 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1621 = 0;
x_1622 = lean_expr_mk_lambda(x_1620, x_1621, x_1596, x_1615);
x_1623 = lean::cnstr_get(x_1575, 3);
lean::inc(x_1623);
lean::dec(x_1575);
if (lean::obj_tag(x_1623) == 0)
{
obj* x_1626; obj* x_1629; obj* x_1633; 
x_1626 = lean::cnstr_get(x_1623, 0);
lean::inc(x_1626);
lean::dec(x_1623);
x_1629 = lean::cnstr_get(x_1626, 1);
lean::inc(x_1629);
lean::dec(x_1626);
lean::inc(x_2);
x_1633 = l_Lean_Elaborator_toPexpr___main(x_1629, x_1, x_2, x_1617);
if (lean::obj_tag(x_1633) == 0)
{
obj* x_1638; obj* x_1640; obj* x_1641; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1622);
x_1638 = lean::cnstr_get(x_1633, 0);
if (lean::is_exclusive(x_1633)) {
 x_1640 = x_1633;
} else {
 lean::inc(x_1638);
 lean::dec(x_1633);
 x_1640 = lean::box(0);
}
if (lean::is_scalar(x_1640)) {
 x_1641 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1641 = x_1640;
}
lean::cnstr_set(x_1641, 0, x_1638);
return x_1641;
}
else
{
obj* x_1642; obj* x_1645; obj* x_1647; obj* x_1649; obj* x_1650; obj* x_1651; obj* x_1652; obj* x_1653; 
x_1642 = lean::cnstr_get(x_1633, 0);
lean::inc(x_1642);
lean::dec(x_1633);
x_1645 = lean::cnstr_get(x_1642, 0);
x_1647 = lean::cnstr_get(x_1642, 1);
if (lean::is_exclusive(x_1642)) {
 x_1649 = x_1642;
} else {
 lean::inc(x_1645);
 lean::inc(x_1647);
 lean::dec(x_1642);
 x_1649 = lean::box(0);
}
x_1650 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1651 = l_Lean_Elaborator_Expr_mkAnnotation(x_1650, x_1622);
x_1652 = lean_expr_mk_app(x_1651, x_1645);
if (lean::is_scalar(x_1649)) {
 x_1653 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1653 = x_1649;
}
lean::cnstr_set(x_1653, 0, x_1652);
lean::cnstr_set(x_1653, 1, x_1647);
x_15 = x_1653;
goto lbl_16;
}
}
else
{
obj* x_1654; obj* x_1657; obj* x_1660; obj* x_1664; 
x_1654 = lean::cnstr_get(x_1623, 0);
lean::inc(x_1654);
lean::dec(x_1623);
x_1657 = lean::cnstr_get(x_1654, 1);
lean::inc(x_1657);
lean::dec(x_1654);
x_1660 = lean::cnstr_get(x_1657, 1);
lean::inc(x_1660);
lean::dec(x_1657);
lean::inc(x_2);
x_1664 = l_Lean_Elaborator_toPexpr___main(x_1660, x_1, x_2, x_1617);
if (lean::obj_tag(x_1664) == 0)
{
obj* x_1669; obj* x_1671; obj* x_1672; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1622);
x_1669 = lean::cnstr_get(x_1664, 0);
if (lean::is_exclusive(x_1664)) {
 x_1671 = x_1664;
} else {
 lean::inc(x_1669);
 lean::dec(x_1664);
 x_1671 = lean::box(0);
}
if (lean::is_scalar(x_1671)) {
 x_1672 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1672 = x_1671;
}
lean::cnstr_set(x_1672, 0, x_1669);
return x_1672;
}
else
{
obj* x_1673; obj* x_1676; obj* x_1678; obj* x_1680; obj* x_1681; obj* x_1682; obj* x_1683; obj* x_1684; 
x_1673 = lean::cnstr_get(x_1664, 0);
lean::inc(x_1673);
lean::dec(x_1664);
x_1676 = lean::cnstr_get(x_1673, 0);
x_1678 = lean::cnstr_get(x_1673, 1);
if (lean::is_exclusive(x_1673)) {
 x_1680 = x_1673;
} else {
 lean::inc(x_1676);
 lean::inc(x_1678);
 lean::dec(x_1673);
 x_1680 = lean::box(0);
}
x_1681 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1682 = l_Lean_Elaborator_Expr_mkAnnotation(x_1681, x_1622);
x_1683 = lean_expr_mk_app(x_1682, x_1676);
if (lean::is_scalar(x_1680)) {
 x_1684 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1684 = x_1680;
}
lean::cnstr_set(x_1684, 0, x_1683);
lean::cnstr_set(x_1684, 1, x_1678);
x_15 = x_1684;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1685; obj* x_1687; obj* x_1689; obj* x_1693; 
x_1685 = lean::cnstr_get(x_1575, 2);
lean::inc(x_1685);
x_1687 = lean::cnstr_get(x_1575, 5);
lean::inc(x_1687);
x_1689 = lean::cnstr_get(x_1576, 0);
lean::inc(x_1689);
lean::dec(x_1576);
lean::inc(x_2);
x_1693 = l_Lean_Elaborator_toPexpr___main(x_1685, x_1, x_2, x_3);
if (lean::obj_tag(x_1693) == 0)
{
obj* x_1700; obj* x_1702; obj* x_1703; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1575);
lean::dec(x_1687);
lean::dec(x_1689);
x_1700 = lean::cnstr_get(x_1693, 0);
if (lean::is_exclusive(x_1693)) {
 x_1702 = x_1693;
} else {
 lean::inc(x_1700);
 lean::dec(x_1693);
 x_1702 = lean::box(0);
}
if (lean::is_scalar(x_1702)) {
 x_1703 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1703 = x_1702;
}
lean::cnstr_set(x_1703, 0, x_1700);
return x_1703;
}
else
{
obj* x_1704; obj* x_1707; obj* x_1709; obj* x_1713; 
x_1704 = lean::cnstr_get(x_1693, 0);
lean::inc(x_1704);
lean::dec(x_1693);
x_1707 = lean::cnstr_get(x_1704, 0);
lean::inc(x_1707);
x_1709 = lean::cnstr_get(x_1704, 1);
lean::inc(x_1709);
lean::dec(x_1704);
lean::inc(x_2);
x_1713 = l_Lean_Elaborator_toPexpr___main(x_1687, x_1, x_2, x_1709);
if (lean::obj_tag(x_1713) == 0)
{
obj* x_1720; obj* x_1722; obj* x_1723; 
lean::dec(x_1707);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1575);
lean::dec(x_1689);
x_1720 = lean::cnstr_get(x_1713, 0);
if (lean::is_exclusive(x_1713)) {
 x_1722 = x_1713;
} else {
 lean::inc(x_1720);
 lean::dec(x_1713);
 x_1722 = lean::box(0);
}
if (lean::is_scalar(x_1722)) {
 x_1723 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1723 = x_1722;
}
lean::cnstr_set(x_1723, 0, x_1720);
return x_1723;
}
else
{
obj* x_1724; obj* x_1727; obj* x_1729; obj* x_1732; obj* x_1735; uint8 x_1736; obj* x_1737; obj* x_1738; 
x_1724 = lean::cnstr_get(x_1713, 0);
lean::inc(x_1724);
lean::dec(x_1713);
x_1727 = lean::cnstr_get(x_1724, 0);
lean::inc(x_1727);
x_1729 = lean::cnstr_get(x_1724, 1);
lean::inc(x_1729);
lean::dec(x_1724);
x_1732 = lean::cnstr_get(x_1689, 0);
lean::inc(x_1732);
lean::dec(x_1689);
x_1735 = l_Lean_Elaborator_mangleIdent(x_1732);
x_1736 = 0;
x_1737 = lean_expr_mk_lambda(x_1735, x_1736, x_1707, x_1727);
x_1738 = lean::cnstr_get(x_1575, 3);
lean::inc(x_1738);
lean::dec(x_1575);
if (lean::obj_tag(x_1738) == 0)
{
obj* x_1741; obj* x_1744; obj* x_1748; 
x_1741 = lean::cnstr_get(x_1738, 0);
lean::inc(x_1741);
lean::dec(x_1738);
x_1744 = lean::cnstr_get(x_1741, 1);
lean::inc(x_1744);
lean::dec(x_1741);
lean::inc(x_2);
x_1748 = l_Lean_Elaborator_toPexpr___main(x_1744, x_1, x_2, x_1729);
if (lean::obj_tag(x_1748) == 0)
{
obj* x_1753; obj* x_1755; obj* x_1756; 
lean::dec(x_1737);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1753 = lean::cnstr_get(x_1748, 0);
if (lean::is_exclusive(x_1748)) {
 x_1755 = x_1748;
} else {
 lean::inc(x_1753);
 lean::dec(x_1748);
 x_1755 = lean::box(0);
}
if (lean::is_scalar(x_1755)) {
 x_1756 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1756 = x_1755;
}
lean::cnstr_set(x_1756, 0, x_1753);
return x_1756;
}
else
{
obj* x_1757; obj* x_1760; obj* x_1762; obj* x_1764; obj* x_1765; obj* x_1766; obj* x_1767; obj* x_1768; 
x_1757 = lean::cnstr_get(x_1748, 0);
lean::inc(x_1757);
lean::dec(x_1748);
x_1760 = lean::cnstr_get(x_1757, 0);
x_1762 = lean::cnstr_get(x_1757, 1);
if (lean::is_exclusive(x_1757)) {
 x_1764 = x_1757;
} else {
 lean::inc(x_1760);
 lean::inc(x_1762);
 lean::dec(x_1757);
 x_1764 = lean::box(0);
}
x_1765 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1766 = l_Lean_Elaborator_Expr_mkAnnotation(x_1765, x_1737);
x_1767 = lean_expr_mk_app(x_1766, x_1760);
if (lean::is_scalar(x_1764)) {
 x_1768 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1768 = x_1764;
}
lean::cnstr_set(x_1768, 0, x_1767);
lean::cnstr_set(x_1768, 1, x_1762);
x_15 = x_1768;
goto lbl_16;
}
}
else
{
obj* x_1769; obj* x_1772; obj* x_1775; obj* x_1779; 
x_1769 = lean::cnstr_get(x_1738, 0);
lean::inc(x_1769);
lean::dec(x_1738);
x_1772 = lean::cnstr_get(x_1769, 1);
lean::inc(x_1772);
lean::dec(x_1769);
x_1775 = lean::cnstr_get(x_1772, 1);
lean::inc(x_1775);
lean::dec(x_1772);
lean::inc(x_2);
x_1779 = l_Lean_Elaborator_toPexpr___main(x_1775, x_1, x_2, x_1729);
if (lean::obj_tag(x_1779) == 0)
{
obj* x_1784; obj* x_1786; obj* x_1787; 
lean::dec(x_1737);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1784 = lean::cnstr_get(x_1779, 0);
if (lean::is_exclusive(x_1779)) {
 x_1786 = x_1779;
} else {
 lean::inc(x_1784);
 lean::dec(x_1779);
 x_1786 = lean::box(0);
}
if (lean::is_scalar(x_1786)) {
 x_1787 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1787 = x_1786;
}
lean::cnstr_set(x_1787, 0, x_1784);
return x_1787;
}
else
{
obj* x_1788; obj* x_1791; obj* x_1793; obj* x_1795; obj* x_1796; obj* x_1797; obj* x_1798; obj* x_1799; 
x_1788 = lean::cnstr_get(x_1779, 0);
lean::inc(x_1788);
lean::dec(x_1779);
x_1791 = lean::cnstr_get(x_1788, 0);
x_1793 = lean::cnstr_get(x_1788, 1);
if (lean::is_exclusive(x_1788)) {
 x_1795 = x_1788;
} else {
 lean::inc(x_1791);
 lean::inc(x_1793);
 lean::dec(x_1788);
 x_1795 = lean::box(0);
}
x_1796 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1797 = l_Lean_Elaborator_Expr_mkAnnotation(x_1796, x_1737);
x_1798 = lean_expr_mk_app(x_1797, x_1791);
if (lean::is_scalar(x_1795)) {
 x_1799 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1799 = x_1795;
}
lean::cnstr_set(x_1799, 0, x_1798);
lean::cnstr_set(x_1799, 1, x_1793);
x_15 = x_1799;
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
lean::dec(x_8);
lean::dec(x_10);
if (x_20 == 0)
{
obj* x_1802; 
x_1802 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1802) == 0)
{
obj* x_1805; obj* x_1806; obj* x_1807; 
lean::dec(x_2);
x_1805 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1806 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1806, 0, x_1805);
lean::cnstr_set(x_1806, 1, x_3);
x_1807 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1807, 0, x_1806);
return x_1807;
}
else
{
obj* x_1808; obj* x_1811; obj* x_1814; obj* x_1817; obj* x_1818; obj* x_1820; obj* x_1821; obj* x_1822; obj* x_1823; obj* x_1826; obj* x_1827; obj* x_1828; obj* x_1829; obj* x_1830; obj* x_1831; 
x_1808 = lean::cnstr_get(x_1802, 0);
lean::inc(x_1808);
lean::dec(x_1802);
x_1811 = lean::cnstr_get(x_2, 0);
lean::inc(x_1811);
lean::dec(x_2);
x_1814 = lean::cnstr_get(x_1811, 2);
lean::inc(x_1814);
lean::dec(x_1811);
x_1817 = l_Lean_FileMap_toPosition(x_1814, x_1808);
x_1818 = lean::cnstr_get(x_1817, 1);
lean::inc(x_1818);
x_1820 = lean::box(0);
x_1821 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1822 = l_Lean_KVMap_setNat(x_1820, x_1821, x_1818);
x_1823 = lean::cnstr_get(x_1817, 0);
lean::inc(x_1823);
lean::dec(x_1817);
x_1826 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1827 = l_Lean_KVMap_setNat(x_1822, x_1826, x_1823);
x_1828 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1829 = lean_expr_mk_mdata(x_1827, x_1828);
x_1830 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1830, 0, x_1829);
lean::cnstr_set(x_1830, 1, x_3);
x_1831 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1831, 0, x_1830);
return x_1831;
}
}
else
{
obj* x_1834; obj* x_1835; obj* x_1836; 
lean::dec(x_0);
lean::dec(x_2);
x_1834 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1835 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1835, 0, x_1834);
lean::cnstr_set(x_1835, 1, x_3);
x_1836 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1836, 0, x_1835);
return x_1836;
}
}
}
else
{
obj* x_1839; obj* x_1840; obj* x_1844; obj* x_1845; obj* x_1848; obj* x_1849; obj* x_1850; obj* x_1852; 
lean::dec(x_8);
lean::dec(x_10);
x_1839 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_1840 = lean::cnstr_get(x_1839, 0);
lean::inc(x_1840);
lean::dec(x_1839);
lean::inc(x_0);
x_1844 = lean::apply_1(x_1840, x_0);
x_1845 = lean::cnstr_get(x_1844, 1);
lean::inc(x_1845);
lean::dec(x_1844);
x_1848 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_1845);
x_1849 = l_Lean_Expander_getOptType___main___closed__1;
x_1850 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_1849, x_1848);
lean::inc(x_2);
x_1852 = l_Lean_Elaborator_toPexpr___main(x_1850, x_1, x_2, x_3);
if (lean::obj_tag(x_1852) == 0)
{
obj* x_1855; obj* x_1857; obj* x_1858; 
lean::dec(x_0);
lean::dec(x_2);
x_1855 = lean::cnstr_get(x_1852, 0);
if (lean::is_exclusive(x_1852)) {
 x_1857 = x_1852;
} else {
 lean::inc(x_1855);
 lean::dec(x_1852);
 x_1857 = lean::box(0);
}
if (lean::is_scalar(x_1857)) {
 x_1858 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1858 = x_1857;
}
lean::cnstr_set(x_1858, 0, x_1855);
return x_1858;
}
else
{
obj* x_1859; obj* x_1861; obj* x_1862; obj* x_1864; obj* x_1866; obj* x_1867; obj* x_1868; 
x_1859 = lean::cnstr_get(x_1852, 0);
if (lean::is_exclusive(x_1852)) {
 lean::cnstr_set(x_1852, 0, lean::box(0));
 x_1861 = x_1852;
} else {
 lean::inc(x_1859);
 lean::dec(x_1852);
 x_1861 = lean::box(0);
}
x_1862 = lean::cnstr_get(x_1859, 0);
x_1864 = lean::cnstr_get(x_1859, 1);
if (lean::is_exclusive(x_1859)) {
 lean::cnstr_set(x_1859, 0, lean::box(0));
 lean::cnstr_set(x_1859, 1, lean::box(0));
 x_1866 = x_1859;
} else {
 lean::inc(x_1862);
 lean::inc(x_1864);
 lean::dec(x_1859);
 x_1866 = lean::box(0);
}
x_1867 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1868 = l_Lean_Elaborator_Expr_mkAnnotation(x_1867, x_1862);
if (x_20 == 0)
{
obj* x_1869; 
x_1869 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1869) == 0)
{
obj* x_1872; obj* x_1873; 
lean::dec(x_2);
if (lean::is_scalar(x_1866)) {
 x_1872 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1872 = x_1866;
}
lean::cnstr_set(x_1872, 0, x_1868);
lean::cnstr_set(x_1872, 1, x_1864);
if (lean::is_scalar(x_1861)) {
 x_1873 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1873 = x_1861;
}
lean::cnstr_set(x_1873, 0, x_1872);
return x_1873;
}
else
{
obj* x_1874; obj* x_1877; obj* x_1880; obj* x_1883; obj* x_1884; obj* x_1886; obj* x_1887; obj* x_1888; obj* x_1889; obj* x_1892; obj* x_1893; obj* x_1894; obj* x_1895; obj* x_1896; 
x_1874 = lean::cnstr_get(x_1869, 0);
lean::inc(x_1874);
lean::dec(x_1869);
x_1877 = lean::cnstr_get(x_2, 0);
lean::inc(x_1877);
lean::dec(x_2);
x_1880 = lean::cnstr_get(x_1877, 2);
lean::inc(x_1880);
lean::dec(x_1877);
x_1883 = l_Lean_FileMap_toPosition(x_1880, x_1874);
x_1884 = lean::cnstr_get(x_1883, 1);
lean::inc(x_1884);
x_1886 = lean::box(0);
x_1887 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1888 = l_Lean_KVMap_setNat(x_1886, x_1887, x_1884);
x_1889 = lean::cnstr_get(x_1883, 0);
lean::inc(x_1889);
lean::dec(x_1883);
x_1892 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1893 = l_Lean_KVMap_setNat(x_1888, x_1892, x_1889);
x_1894 = lean_expr_mk_mdata(x_1893, x_1868);
if (lean::is_scalar(x_1866)) {
 x_1895 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1895 = x_1866;
}
lean::cnstr_set(x_1895, 0, x_1894);
lean::cnstr_set(x_1895, 1, x_1864);
if (lean::is_scalar(x_1861)) {
 x_1896 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1896 = x_1861;
}
lean::cnstr_set(x_1896, 0, x_1895);
return x_1896;
}
}
else
{
obj* x_1899; obj* x_1900; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1866)) {
 x_1899 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1899 = x_1866;
}
lean::cnstr_set(x_1899, 0, x_1868);
lean::cnstr_set(x_1899, 1, x_1864);
if (lean::is_scalar(x_1861)) {
 x_1900 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1900 = x_1861;
}
lean::cnstr_set(x_1900, 0, x_1899);
return x_1900;
}
}
}
}
else
{
obj* x_1903; obj* x_1904; obj* x_1908; obj* x_1909; obj* x_1910; obj* x_1913; obj* x_1915; 
lean::dec(x_8);
lean::dec(x_10);
x_1903 = l_Lean_Parser_Term_sortApp_HasView;
x_1904 = lean::cnstr_get(x_1903, 0);
lean::inc(x_1904);
lean::dec(x_1903);
lean::inc(x_0);
x_1908 = lean::apply_1(x_1904, x_0);
x_1909 = l_Lean_Parser_Term_sort_HasView;
x_1910 = lean::cnstr_get(x_1909, 0);
lean::inc(x_1910);
lean::dec(x_1909);
x_1913 = lean::cnstr_get(x_1908, 0);
lean::inc(x_1913);
x_1915 = lean::apply_1(x_1910, x_1913);
if (lean::obj_tag(x_1915) == 0)
{
obj* x_1917; obj* x_1921; 
lean::dec(x_1915);
x_1917 = lean::cnstr_get(x_1908, 1);
lean::inc(x_1917);
lean::dec(x_1908);
lean::inc(x_2);
x_1921 = l_Lean_Elaborator_toLevel___main(x_1917, x_1, x_2, x_3);
if (lean::obj_tag(x_1921) == 0)
{
obj* x_1924; obj* x_1926; obj* x_1927; 
lean::dec(x_0);
lean::dec(x_2);
x_1924 = lean::cnstr_get(x_1921, 0);
if (lean::is_exclusive(x_1921)) {
 x_1926 = x_1921;
} else {
 lean::inc(x_1924);
 lean::dec(x_1921);
 x_1926 = lean::box(0);
}
if (lean::is_scalar(x_1926)) {
 x_1927 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1927 = x_1926;
}
lean::cnstr_set(x_1927, 0, x_1924);
return x_1927;
}
else
{
obj* x_1928; obj* x_1930; obj* x_1931; obj* x_1933; obj* x_1935; obj* x_1936; 
x_1928 = lean::cnstr_get(x_1921, 0);
if (lean::is_exclusive(x_1921)) {
 lean::cnstr_set(x_1921, 0, lean::box(0));
 x_1930 = x_1921;
} else {
 lean::inc(x_1928);
 lean::dec(x_1921);
 x_1930 = lean::box(0);
}
x_1931 = lean::cnstr_get(x_1928, 0);
x_1933 = lean::cnstr_get(x_1928, 1);
if (lean::is_exclusive(x_1928)) {
 lean::cnstr_set(x_1928, 0, lean::box(0));
 lean::cnstr_set(x_1928, 1, lean::box(0));
 x_1935 = x_1928;
} else {
 lean::inc(x_1931);
 lean::inc(x_1933);
 lean::dec(x_1928);
 x_1935 = lean::box(0);
}
x_1936 = lean_expr_mk_sort(x_1931);
if (x_20 == 0)
{
obj* x_1937; 
x_1937 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1937) == 0)
{
obj* x_1940; obj* x_1941; 
lean::dec(x_2);
if (lean::is_scalar(x_1935)) {
 x_1940 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1940 = x_1935;
}
lean::cnstr_set(x_1940, 0, x_1936);
lean::cnstr_set(x_1940, 1, x_1933);
if (lean::is_scalar(x_1930)) {
 x_1941 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1941 = x_1930;
}
lean::cnstr_set(x_1941, 0, x_1940);
return x_1941;
}
else
{
obj* x_1942; obj* x_1945; obj* x_1948; obj* x_1951; obj* x_1952; obj* x_1954; obj* x_1955; obj* x_1956; obj* x_1957; obj* x_1960; obj* x_1961; obj* x_1962; obj* x_1963; obj* x_1964; 
x_1942 = lean::cnstr_get(x_1937, 0);
lean::inc(x_1942);
lean::dec(x_1937);
x_1945 = lean::cnstr_get(x_2, 0);
lean::inc(x_1945);
lean::dec(x_2);
x_1948 = lean::cnstr_get(x_1945, 2);
lean::inc(x_1948);
lean::dec(x_1945);
x_1951 = l_Lean_FileMap_toPosition(x_1948, x_1942);
x_1952 = lean::cnstr_get(x_1951, 1);
lean::inc(x_1952);
x_1954 = lean::box(0);
x_1955 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1956 = l_Lean_KVMap_setNat(x_1954, x_1955, x_1952);
x_1957 = lean::cnstr_get(x_1951, 0);
lean::inc(x_1957);
lean::dec(x_1951);
x_1960 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1961 = l_Lean_KVMap_setNat(x_1956, x_1960, x_1957);
x_1962 = lean_expr_mk_mdata(x_1961, x_1936);
if (lean::is_scalar(x_1935)) {
 x_1963 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1963 = x_1935;
}
lean::cnstr_set(x_1963, 0, x_1962);
lean::cnstr_set(x_1963, 1, x_1933);
if (lean::is_scalar(x_1930)) {
 x_1964 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1964 = x_1930;
}
lean::cnstr_set(x_1964, 0, x_1963);
return x_1964;
}
}
else
{
obj* x_1967; obj* x_1968; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1935)) {
 x_1967 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1967 = x_1935;
}
lean::cnstr_set(x_1967, 0, x_1936);
lean::cnstr_set(x_1967, 1, x_1933);
if (lean::is_scalar(x_1930)) {
 x_1968 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1968 = x_1930;
}
lean::cnstr_set(x_1968, 0, x_1967);
return x_1968;
}
}
}
else
{
obj* x_1970; obj* x_1974; 
lean::dec(x_1915);
x_1970 = lean::cnstr_get(x_1908, 1);
lean::inc(x_1970);
lean::dec(x_1908);
lean::inc(x_2);
x_1974 = l_Lean_Elaborator_toLevel___main(x_1970, x_1, x_2, x_3);
if (lean::obj_tag(x_1974) == 0)
{
obj* x_1977; obj* x_1979; obj* x_1980; 
lean::dec(x_0);
lean::dec(x_2);
x_1977 = lean::cnstr_get(x_1974, 0);
if (lean::is_exclusive(x_1974)) {
 x_1979 = x_1974;
} else {
 lean::inc(x_1977);
 lean::dec(x_1974);
 x_1979 = lean::box(0);
}
if (lean::is_scalar(x_1979)) {
 x_1980 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1980 = x_1979;
}
lean::cnstr_set(x_1980, 0, x_1977);
return x_1980;
}
else
{
obj* x_1981; obj* x_1983; obj* x_1984; obj* x_1986; obj* x_1988; obj* x_1989; obj* x_1990; 
x_1981 = lean::cnstr_get(x_1974, 0);
if (lean::is_exclusive(x_1974)) {
 lean::cnstr_set(x_1974, 0, lean::box(0));
 x_1983 = x_1974;
} else {
 lean::inc(x_1981);
 lean::dec(x_1974);
 x_1983 = lean::box(0);
}
x_1984 = lean::cnstr_get(x_1981, 0);
x_1986 = lean::cnstr_get(x_1981, 1);
if (lean::is_exclusive(x_1981)) {
 lean::cnstr_set(x_1981, 0, lean::box(0));
 lean::cnstr_set(x_1981, 1, lean::box(0));
 x_1988 = x_1981;
} else {
 lean::inc(x_1984);
 lean::inc(x_1986);
 lean::dec(x_1981);
 x_1988 = lean::box(0);
}
x_1989 = level_mk_succ(x_1984);
x_1990 = lean_expr_mk_sort(x_1989);
if (x_20 == 0)
{
obj* x_1991; 
x_1991 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1991) == 0)
{
obj* x_1994; obj* x_1995; 
lean::dec(x_2);
if (lean::is_scalar(x_1988)) {
 x_1994 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1994 = x_1988;
}
lean::cnstr_set(x_1994, 0, x_1990);
lean::cnstr_set(x_1994, 1, x_1986);
if (lean::is_scalar(x_1983)) {
 x_1995 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1995 = x_1983;
}
lean::cnstr_set(x_1995, 0, x_1994);
return x_1995;
}
else
{
obj* x_1996; obj* x_1999; obj* x_2002; obj* x_2005; obj* x_2006; obj* x_2008; obj* x_2009; obj* x_2010; obj* x_2011; obj* x_2014; obj* x_2015; obj* x_2016; obj* x_2017; obj* x_2018; 
x_1996 = lean::cnstr_get(x_1991, 0);
lean::inc(x_1996);
lean::dec(x_1991);
x_1999 = lean::cnstr_get(x_2, 0);
lean::inc(x_1999);
lean::dec(x_2);
x_2002 = lean::cnstr_get(x_1999, 2);
lean::inc(x_2002);
lean::dec(x_1999);
x_2005 = l_Lean_FileMap_toPosition(x_2002, x_1996);
x_2006 = lean::cnstr_get(x_2005, 1);
lean::inc(x_2006);
x_2008 = lean::box(0);
x_2009 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2010 = l_Lean_KVMap_setNat(x_2008, x_2009, x_2006);
x_2011 = lean::cnstr_get(x_2005, 0);
lean::inc(x_2011);
lean::dec(x_2005);
x_2014 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2015 = l_Lean_KVMap_setNat(x_2010, x_2014, x_2011);
x_2016 = lean_expr_mk_mdata(x_2015, x_1990);
if (lean::is_scalar(x_1988)) {
 x_2017 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2017 = x_1988;
}
lean::cnstr_set(x_2017, 0, x_2016);
lean::cnstr_set(x_2017, 1, x_1986);
if (lean::is_scalar(x_1983)) {
 x_2018 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2018 = x_1983;
}
lean::cnstr_set(x_2018, 0, x_2017);
return x_2018;
}
}
else
{
obj* x_2021; obj* x_2022; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1988)) {
 x_2021 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2021 = x_1988;
}
lean::cnstr_set(x_2021, 0, x_1990);
lean::cnstr_set(x_2021, 1, x_1986);
if (lean::is_scalar(x_1983)) {
 x_2022 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2022 = x_1983;
}
lean::cnstr_set(x_2022, 0, x_2021);
return x_2022;
}
}
}
}
}
else
{
obj* x_2025; obj* x_2026; obj* x_2030; 
lean::dec(x_8);
lean::dec(x_10);
x_2025 = l_Lean_Parser_Term_sort_HasView;
x_2026 = lean::cnstr_get(x_2025, 0);
lean::inc(x_2026);
lean::dec(x_2025);
lean::inc(x_0);
x_2030 = lean::apply_1(x_2026, x_0);
if (lean::obj_tag(x_2030) == 0)
{
lean::dec(x_2030);
if (x_20 == 0)
{
obj* x_2032; 
x_2032 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2032) == 0)
{
obj* x_2035; obj* x_2036; obj* x_2037; 
lean::dec(x_2);
x_2035 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_2036 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2036, 0, x_2035);
lean::cnstr_set(x_2036, 1, x_3);
x_2037 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2037, 0, x_2036);
return x_2037;
}
else
{
obj* x_2038; obj* x_2041; obj* x_2044; obj* x_2047; obj* x_2048; obj* x_2050; obj* x_2051; obj* x_2052; obj* x_2053; obj* x_2056; obj* x_2057; obj* x_2058; obj* x_2059; obj* x_2060; obj* x_2061; 
x_2038 = lean::cnstr_get(x_2032, 0);
lean::inc(x_2038);
lean::dec(x_2032);
x_2041 = lean::cnstr_get(x_2, 0);
lean::inc(x_2041);
lean::dec(x_2);
x_2044 = lean::cnstr_get(x_2041, 2);
lean::inc(x_2044);
lean::dec(x_2041);
x_2047 = l_Lean_FileMap_toPosition(x_2044, x_2038);
x_2048 = lean::cnstr_get(x_2047, 1);
lean::inc(x_2048);
x_2050 = lean::box(0);
x_2051 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2052 = l_Lean_KVMap_setNat(x_2050, x_2051, x_2048);
x_2053 = lean::cnstr_get(x_2047, 0);
lean::inc(x_2053);
lean::dec(x_2047);
x_2056 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2057 = l_Lean_KVMap_setNat(x_2052, x_2056, x_2053);
x_2058 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_2059 = lean_expr_mk_mdata(x_2057, x_2058);
x_2060 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2060, 0, x_2059);
lean::cnstr_set(x_2060, 1, x_3);
x_2061 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2061, 0, x_2060);
return x_2061;
}
}
else
{
obj* x_2064; obj* x_2065; obj* x_2066; 
lean::dec(x_0);
lean::dec(x_2);
x_2064 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_2065 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2065, 0, x_2064);
lean::cnstr_set(x_2065, 1, x_3);
x_2066 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2066, 0, x_2065);
return x_2066;
}
}
else
{
lean::dec(x_2030);
if (x_20 == 0)
{
obj* x_2068; 
x_2068 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2068) == 0)
{
obj* x_2071; obj* x_2072; obj* x_2073; 
lean::dec(x_2);
x_2071 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2072 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2072, 0, x_2071);
lean::cnstr_set(x_2072, 1, x_3);
x_2073 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2073, 0, x_2072);
return x_2073;
}
else
{
obj* x_2074; obj* x_2077; obj* x_2080; obj* x_2083; obj* x_2084; obj* x_2086; obj* x_2087; obj* x_2088; obj* x_2089; obj* x_2092; obj* x_2093; obj* x_2094; obj* x_2095; obj* x_2096; obj* x_2097; 
x_2074 = lean::cnstr_get(x_2068, 0);
lean::inc(x_2074);
lean::dec(x_2068);
x_2077 = lean::cnstr_get(x_2, 0);
lean::inc(x_2077);
lean::dec(x_2);
x_2080 = lean::cnstr_get(x_2077, 2);
lean::inc(x_2080);
lean::dec(x_2077);
x_2083 = l_Lean_FileMap_toPosition(x_2080, x_2074);
x_2084 = lean::cnstr_get(x_2083, 1);
lean::inc(x_2084);
x_2086 = lean::box(0);
x_2087 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2088 = l_Lean_KVMap_setNat(x_2086, x_2087, x_2084);
x_2089 = lean::cnstr_get(x_2083, 0);
lean::inc(x_2089);
lean::dec(x_2083);
x_2092 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2093 = l_Lean_KVMap_setNat(x_2088, x_2092, x_2089);
x_2094 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2095 = lean_expr_mk_mdata(x_2093, x_2094);
x_2096 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2096, 0, x_2095);
lean::cnstr_set(x_2096, 1, x_3);
x_2097 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2097, 0, x_2096);
return x_2097;
}
}
else
{
obj* x_2100; obj* x_2101; obj* x_2102; 
lean::dec(x_0);
lean::dec(x_2);
x_2100 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_2101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2101, 0, x_2100);
lean::cnstr_set(x_2101, 1, x_3);
x_2102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2102, 0, x_2101);
return x_2102;
}
}
}
}
else
{
obj* x_2104; obj* x_2105; obj* x_2109; obj* x_2110; 
lean::dec(x_10);
x_2104 = l_Lean_Parser_Term_pi_HasView;
x_2105 = lean::cnstr_get(x_2104, 0);
lean::inc(x_2105);
lean::dec(x_2104);
lean::inc(x_0);
x_2109 = lean::apply_1(x_2105, x_0);
x_2110 = lean::cnstr_get(x_2109, 1);
lean::inc(x_2110);
if (lean::obj_tag(x_2110) == 0)
{
obj* x_2115; obj* x_2116; obj* x_2118; 
lean::dec(x_2109);
lean::dec(x_2110);
lean::inc(x_0);
x_2115 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2115, 0, x_0);
x_2116 = l_Lean_Elaborator_toPexpr___main___closed__43;
lean::inc(x_2);
x_2118 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2115, x_2116, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2115);
if (lean::obj_tag(x_2118) == 0)
{
obj* x_2124; obj* x_2126; obj* x_2127; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2124 = lean::cnstr_get(x_2118, 0);
if (lean::is_exclusive(x_2118)) {
 x_2126 = x_2118;
} else {
 lean::inc(x_2124);
 lean::dec(x_2118);
 x_2126 = lean::box(0);
}
if (lean::is_scalar(x_2126)) {
 x_2127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2127 = x_2126;
}
lean::cnstr_set(x_2127, 0, x_2124);
return x_2127;
}
else
{
obj* x_2128; 
x_2128 = lean::cnstr_get(x_2118, 0);
lean::inc(x_2128);
lean::dec(x_2118);
x_15 = x_2128;
goto lbl_16;
}
}
else
{
obj* x_2131; obj* x_2134; obj* x_2135; obj* x_2137; obj* x_2140; obj* x_2142; obj* x_2146; 
x_2131 = lean::cnstr_get(x_2110, 0);
lean::inc(x_2131);
lean::dec(x_2110);
x_2134 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2131);
x_2135 = lean::cnstr_get(x_2134, 1);
lean::inc(x_2135);
x_2137 = lean::cnstr_get(x_2134, 0);
lean::inc(x_2137);
lean::dec(x_2134);
x_2140 = lean::cnstr_get(x_2135, 0);
lean::inc(x_2140);
x_2142 = lean::cnstr_get(x_2135, 1);
lean::inc(x_2142);
lean::dec(x_2135);
lean::inc(x_2);
x_2146 = l_Lean_Elaborator_toPexpr___main(x_2142, x_1, x_2, x_3);
if (lean::obj_tag(x_2146) == 0)
{
obj* x_2153; obj* x_2155; obj* x_2156; 
lean::dec(x_2140);
lean::dec(x_2137);
lean::dec(x_2109);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2153 = lean::cnstr_get(x_2146, 0);
if (lean::is_exclusive(x_2146)) {
 x_2155 = x_2146;
} else {
 lean::inc(x_2153);
 lean::dec(x_2146);
 x_2155 = lean::box(0);
}
if (lean::is_scalar(x_2155)) {
 x_2156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2156 = x_2155;
}
lean::cnstr_set(x_2156, 0, x_2153);
return x_2156;
}
else
{
obj* x_2157; obj* x_2160; obj* x_2162; obj* x_2165; obj* x_2169; 
x_2157 = lean::cnstr_get(x_2146, 0);
lean::inc(x_2157);
lean::dec(x_2146);
x_2160 = lean::cnstr_get(x_2157, 0);
lean::inc(x_2160);
x_2162 = lean::cnstr_get(x_2157, 1);
lean::inc(x_2162);
lean::dec(x_2157);
x_2165 = lean::cnstr_get(x_2109, 3);
lean::inc(x_2165);
lean::dec(x_2109);
lean::inc(x_2);
x_2169 = l_Lean_Elaborator_toPexpr___main(x_2165, x_1, x_2, x_2162);
if (lean::obj_tag(x_2169) == 0)
{
obj* x_2176; obj* x_2178; obj* x_2179; 
lean::dec(x_2140);
lean::dec(x_2137);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2160);
x_2176 = lean::cnstr_get(x_2169, 0);
if (lean::is_exclusive(x_2169)) {
 x_2178 = x_2169;
} else {
 lean::inc(x_2176);
 lean::dec(x_2169);
 x_2178 = lean::box(0);
}
if (lean::is_scalar(x_2178)) {
 x_2179 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2179 = x_2178;
}
lean::cnstr_set(x_2179, 0, x_2176);
return x_2179;
}
else
{
obj* x_2180; obj* x_2183; obj* x_2185; obj* x_2187; obj* x_2188; uint8 x_2189; obj* x_2190; obj* x_2191; 
x_2180 = lean::cnstr_get(x_2169, 0);
lean::inc(x_2180);
lean::dec(x_2169);
x_2183 = lean::cnstr_get(x_2180, 0);
x_2185 = lean::cnstr_get(x_2180, 1);
if (lean::is_exclusive(x_2180)) {
 x_2187 = x_2180;
} else {
 lean::inc(x_2183);
 lean::inc(x_2185);
 lean::dec(x_2180);
 x_2187 = lean::box(0);
}
x_2188 = l_Lean_Elaborator_mangleIdent(x_2140);
x_2189 = lean::unbox(x_2137);
x_2190 = lean_expr_mk_pi(x_2188, x_2189, x_2160, x_2183);
if (lean::is_scalar(x_2187)) {
 x_2191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2191 = x_2187;
}
lean::cnstr_set(x_2191, 0, x_2190);
lean::cnstr_set(x_2191, 1, x_2185);
x_15 = x_2191;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2193; obj* x_2194; obj* x_2198; obj* x_2199; 
lean::dec(x_10);
x_2193 = l_Lean_Parser_Term_lambda_HasView;
x_2194 = lean::cnstr_get(x_2193, 0);
lean::inc(x_2194);
lean::dec(x_2193);
lean::inc(x_0);
x_2198 = lean::apply_1(x_2194, x_0);
x_2199 = lean::cnstr_get(x_2198, 1);
lean::inc(x_2199);
if (lean::obj_tag(x_2199) == 0)
{
obj* x_2204; obj* x_2205; obj* x_2207; 
lean::dec(x_2199);
lean::dec(x_2198);
lean::inc(x_0);
x_2204 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2204, 0, x_0);
x_2205 = l_Lean_Elaborator_toPexpr___main___closed__44;
lean::inc(x_2);
x_2207 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2204, x_2205, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2204);
if (lean::obj_tag(x_2207) == 0)
{
obj* x_2213; obj* x_2215; obj* x_2216; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2213 = lean::cnstr_get(x_2207, 0);
if (lean::is_exclusive(x_2207)) {
 x_2215 = x_2207;
} else {
 lean::inc(x_2213);
 lean::dec(x_2207);
 x_2215 = lean::box(0);
}
if (lean::is_scalar(x_2215)) {
 x_2216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2216 = x_2215;
}
lean::cnstr_set(x_2216, 0, x_2213);
return x_2216;
}
else
{
obj* x_2217; 
x_2217 = lean::cnstr_get(x_2207, 0);
lean::inc(x_2217);
lean::dec(x_2207);
x_15 = x_2217;
goto lbl_16;
}
}
else
{
obj* x_2220; obj* x_2223; obj* x_2224; obj* x_2226; obj* x_2229; obj* x_2231; obj* x_2235; 
x_2220 = lean::cnstr_get(x_2199, 0);
lean::inc(x_2220);
lean::dec(x_2199);
x_2223 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2220);
x_2224 = lean::cnstr_get(x_2223, 1);
lean::inc(x_2224);
x_2226 = lean::cnstr_get(x_2223, 0);
lean::inc(x_2226);
lean::dec(x_2223);
x_2229 = lean::cnstr_get(x_2224, 0);
lean::inc(x_2229);
x_2231 = lean::cnstr_get(x_2224, 1);
lean::inc(x_2231);
lean::dec(x_2224);
lean::inc(x_2);
x_2235 = l_Lean_Elaborator_toPexpr___main(x_2231, x_1, x_2, x_3);
if (lean::obj_tag(x_2235) == 0)
{
obj* x_2242; obj* x_2244; obj* x_2245; 
lean::dec(x_2198);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2229);
lean::dec(x_2226);
x_2242 = lean::cnstr_get(x_2235, 0);
if (lean::is_exclusive(x_2235)) {
 x_2244 = x_2235;
} else {
 lean::inc(x_2242);
 lean::dec(x_2235);
 x_2244 = lean::box(0);
}
if (lean::is_scalar(x_2244)) {
 x_2245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2245 = x_2244;
}
lean::cnstr_set(x_2245, 0, x_2242);
return x_2245;
}
else
{
obj* x_2246; obj* x_2249; obj* x_2251; obj* x_2254; obj* x_2258; 
x_2246 = lean::cnstr_get(x_2235, 0);
lean::inc(x_2246);
lean::dec(x_2235);
x_2249 = lean::cnstr_get(x_2246, 0);
lean::inc(x_2249);
x_2251 = lean::cnstr_get(x_2246, 1);
lean::inc(x_2251);
lean::dec(x_2246);
x_2254 = lean::cnstr_get(x_2198, 3);
lean::inc(x_2254);
lean::dec(x_2198);
lean::inc(x_2);
x_2258 = l_Lean_Elaborator_toPexpr___main(x_2254, x_1, x_2, x_2251);
if (lean::obj_tag(x_2258) == 0)
{
obj* x_2265; obj* x_2267; obj* x_2268; 
lean::dec(x_8);
lean::dec(x_2249);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2229);
lean::dec(x_2226);
x_2265 = lean::cnstr_get(x_2258, 0);
if (lean::is_exclusive(x_2258)) {
 x_2267 = x_2258;
} else {
 lean::inc(x_2265);
 lean::dec(x_2258);
 x_2267 = lean::box(0);
}
if (lean::is_scalar(x_2267)) {
 x_2268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2268 = x_2267;
}
lean::cnstr_set(x_2268, 0, x_2265);
return x_2268;
}
else
{
obj* x_2269; obj* x_2272; obj* x_2274; obj* x_2276; obj* x_2277; uint8 x_2278; obj* x_2279; obj* x_2280; 
x_2269 = lean::cnstr_get(x_2258, 0);
lean::inc(x_2269);
lean::dec(x_2258);
x_2272 = lean::cnstr_get(x_2269, 0);
x_2274 = lean::cnstr_get(x_2269, 1);
if (lean::is_exclusive(x_2269)) {
 x_2276 = x_2269;
} else {
 lean::inc(x_2272);
 lean::inc(x_2274);
 lean::dec(x_2269);
 x_2276 = lean::box(0);
}
x_2277 = l_Lean_Elaborator_mangleIdent(x_2229);
x_2278 = lean::unbox(x_2226);
x_2279 = lean_expr_mk_lambda(x_2277, x_2278, x_2249, x_2272);
if (lean::is_scalar(x_2276)) {
 x_2280 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2280 = x_2276;
}
lean::cnstr_set(x_2280, 0, x_2279);
lean::cnstr_set(x_2280, 1, x_2274);
x_15 = x_2280;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2283; obj* x_2284; obj* x_2288; obj* x_2289; obj* x_2292; 
lean::dec(x_8);
lean::dec(x_10);
x_2283 = l_Lean_Parser_Term_app_HasView;
x_2284 = lean::cnstr_get(x_2283, 0);
lean::inc(x_2284);
lean::dec(x_2283);
lean::inc(x_0);
x_2288 = lean::apply_1(x_2284, x_0);
x_2289 = lean::cnstr_get(x_2288, 0);
lean::inc(x_2289);
lean::inc(x_2);
x_2292 = l_Lean_Elaborator_toPexpr___main(x_2289, x_1, x_2, x_3);
if (lean::obj_tag(x_2292) == 0)
{
obj* x_2296; obj* x_2298; obj* x_2299; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2288);
x_2296 = lean::cnstr_get(x_2292, 0);
if (lean::is_exclusive(x_2292)) {
 x_2298 = x_2292;
} else {
 lean::inc(x_2296);
 lean::dec(x_2292);
 x_2298 = lean::box(0);
}
if (lean::is_scalar(x_2298)) {
 x_2299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2299 = x_2298;
}
lean::cnstr_set(x_2299, 0, x_2296);
return x_2299;
}
else
{
obj* x_2300; obj* x_2303; obj* x_2305; obj* x_2308; obj* x_2312; 
x_2300 = lean::cnstr_get(x_2292, 0);
lean::inc(x_2300);
lean::dec(x_2292);
x_2303 = lean::cnstr_get(x_2300, 0);
lean::inc(x_2303);
x_2305 = lean::cnstr_get(x_2300, 1);
lean::inc(x_2305);
lean::dec(x_2300);
x_2308 = lean::cnstr_get(x_2288, 1);
lean::inc(x_2308);
lean::dec(x_2288);
lean::inc(x_2);
x_2312 = l_Lean_Elaborator_toPexpr___main(x_2308, x_1, x_2, x_2305);
if (lean::obj_tag(x_2312) == 0)
{
obj* x_2316; obj* x_2318; obj* x_2319; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2303);
x_2316 = lean::cnstr_get(x_2312, 0);
if (lean::is_exclusive(x_2312)) {
 x_2318 = x_2312;
} else {
 lean::inc(x_2316);
 lean::dec(x_2312);
 x_2318 = lean::box(0);
}
if (lean::is_scalar(x_2318)) {
 x_2319 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2319 = x_2318;
}
lean::cnstr_set(x_2319, 0, x_2316);
return x_2319;
}
else
{
obj* x_2320; obj* x_2322; obj* x_2323; obj* x_2325; obj* x_2327; obj* x_2328; 
x_2320 = lean::cnstr_get(x_2312, 0);
if (lean::is_exclusive(x_2312)) {
 lean::cnstr_set(x_2312, 0, lean::box(0));
 x_2322 = x_2312;
} else {
 lean::inc(x_2320);
 lean::dec(x_2312);
 x_2322 = lean::box(0);
}
x_2323 = lean::cnstr_get(x_2320, 0);
x_2325 = lean::cnstr_get(x_2320, 1);
if (lean::is_exclusive(x_2320)) {
 lean::cnstr_set(x_2320, 0, lean::box(0));
 lean::cnstr_set(x_2320, 1, lean::box(0));
 x_2327 = x_2320;
} else {
 lean::inc(x_2323);
 lean::inc(x_2325);
 lean::dec(x_2320);
 x_2327 = lean::box(0);
}
x_2328 = lean_expr_mk_app(x_2303, x_2323);
if (x_20 == 0)
{
obj* x_2329; 
x_2329 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2329) == 0)
{
obj* x_2332; obj* x_2333; 
lean::dec(x_2);
if (lean::is_scalar(x_2327)) {
 x_2332 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2332 = x_2327;
}
lean::cnstr_set(x_2332, 0, x_2328);
lean::cnstr_set(x_2332, 1, x_2325);
if (lean::is_scalar(x_2322)) {
 x_2333 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2333 = x_2322;
}
lean::cnstr_set(x_2333, 0, x_2332);
return x_2333;
}
else
{
obj* x_2334; obj* x_2337; obj* x_2340; obj* x_2343; obj* x_2344; obj* x_2346; obj* x_2347; obj* x_2348; obj* x_2349; obj* x_2352; obj* x_2353; obj* x_2354; obj* x_2355; obj* x_2356; 
x_2334 = lean::cnstr_get(x_2329, 0);
lean::inc(x_2334);
lean::dec(x_2329);
x_2337 = lean::cnstr_get(x_2, 0);
lean::inc(x_2337);
lean::dec(x_2);
x_2340 = lean::cnstr_get(x_2337, 2);
lean::inc(x_2340);
lean::dec(x_2337);
x_2343 = l_Lean_FileMap_toPosition(x_2340, x_2334);
x_2344 = lean::cnstr_get(x_2343, 1);
lean::inc(x_2344);
x_2346 = lean::box(0);
x_2347 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2348 = l_Lean_KVMap_setNat(x_2346, x_2347, x_2344);
x_2349 = lean::cnstr_get(x_2343, 0);
lean::inc(x_2349);
lean::dec(x_2343);
x_2352 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2353 = l_Lean_KVMap_setNat(x_2348, x_2352, x_2349);
x_2354 = lean_expr_mk_mdata(x_2353, x_2328);
if (lean::is_scalar(x_2327)) {
 x_2355 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2355 = x_2327;
}
lean::cnstr_set(x_2355, 0, x_2354);
lean::cnstr_set(x_2355, 1, x_2325);
if (lean::is_scalar(x_2322)) {
 x_2356 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2356 = x_2322;
}
lean::cnstr_set(x_2356, 0, x_2355);
return x_2356;
}
}
else
{
obj* x_2359; obj* x_2360; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2327)) {
 x_2359 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2359 = x_2327;
}
lean::cnstr_set(x_2359, 0, x_2328);
lean::cnstr_set(x_2359, 1, x_2325);
if (lean::is_scalar(x_2322)) {
 x_2360 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2360 = x_2322;
}
lean::cnstr_set(x_2360, 0, x_2359);
return x_2360;
}
}
}
}
}
else
{
obj* x_2362; obj* x_2363; obj* x_2367; obj* x_2368; 
lean::dec(x_10);
x_2362 = l_Lean_Parser_identUnivs_HasView;
x_2363 = lean::cnstr_get(x_2362, 0);
lean::inc(x_2363);
lean::dec(x_2362);
lean::inc(x_0);
x_2367 = lean::apply_1(x_2363, x_0);
x_2368 = lean::cnstr_get(x_2367, 1);
lean::inc(x_2368);
if (lean::obj_tag(x_2368) == 0)
{
obj* x_2370; obj* x_2374; obj* x_2375; obj* x_2376; obj* x_2377; obj* x_2380; obj* x_2381; obj* x_2382; obj* x_2383; obj* x_2384; obj* x_2385; uint8 x_2386; 
x_2370 = lean::cnstr_get(x_2367, 0);
lean::inc(x_2370);
lean::dec(x_2367);
lean::inc(x_2370);
x_2374 = l_Lean_Elaborator_mangleIdent(x_2370);
x_2375 = lean::box(0);
x_2376 = lean_expr_mk_const(x_2374, x_2375);
x_2377 = lean::cnstr_get(x_2370, 3);
lean::inc(x_2377);
lean::dec(x_2370);
x_2380 = lean::mk_nat_obj(0ul);
x_2381 = l_List_enumFrom___main___rarg(x_2380, x_2377);
x_2382 = l_Lean_Elaborator_toPexpr___main___closed__45;
x_2383 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2382, x_2381);
x_2384 = lean_expr_mk_mdata(x_2383, x_2376);
x_2385 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2386 = lean_name_dec_eq(x_8, x_2385);
lean::dec(x_8);
if (x_2386 == 0)
{
obj* x_2388; 
x_2388 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2388) == 0)
{
obj* x_2391; obj* x_2392; 
lean::dec(x_2);
x_2391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2391, 0, x_2384);
lean::cnstr_set(x_2391, 1, x_3);
x_2392 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2392, 0, x_2391);
return x_2392;
}
else
{
obj* x_2393; obj* x_2396; obj* x_2399; obj* x_2402; obj* x_2403; obj* x_2405; obj* x_2406; obj* x_2407; obj* x_2410; obj* x_2411; obj* x_2412; obj* x_2413; obj* x_2414; 
x_2393 = lean::cnstr_get(x_2388, 0);
lean::inc(x_2393);
lean::dec(x_2388);
x_2396 = lean::cnstr_get(x_2, 0);
lean::inc(x_2396);
lean::dec(x_2);
x_2399 = lean::cnstr_get(x_2396, 2);
lean::inc(x_2399);
lean::dec(x_2396);
x_2402 = l_Lean_FileMap_toPosition(x_2399, x_2393);
x_2403 = lean::cnstr_get(x_2402, 1);
lean::inc(x_2403);
x_2405 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2406 = l_Lean_KVMap_setNat(x_2375, x_2405, x_2403);
x_2407 = lean::cnstr_get(x_2402, 0);
lean::inc(x_2407);
lean::dec(x_2402);
x_2410 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2411 = l_Lean_KVMap_setNat(x_2406, x_2410, x_2407);
x_2412 = lean_expr_mk_mdata(x_2411, x_2384);
x_2413 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2413, 0, x_2412);
lean::cnstr_set(x_2413, 1, x_3);
x_2414 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2414, 0, x_2413);
return x_2414;
}
}
else
{
obj* x_2417; obj* x_2418; 
lean::dec(x_0);
lean::dec(x_2);
x_2417 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2417, 0, x_2384);
lean::cnstr_set(x_2417, 1, x_3);
x_2418 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2418, 0, x_2417);
return x_2418;
}
}
else
{
obj* x_2419; obj* x_2422; obj* x_2425; obj* x_2429; 
x_2419 = lean::cnstr_get(x_2367, 0);
lean::inc(x_2419);
lean::dec(x_2367);
x_2422 = lean::cnstr_get(x_2368, 0);
lean::inc(x_2422);
lean::dec(x_2368);
x_2425 = lean::cnstr_get(x_2422, 1);
lean::inc(x_2425);
lean::dec(x_2422);
lean::inc(x_2);
x_2429 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_2425, x_1, x_2, x_3);
if (lean::obj_tag(x_2429) == 0)
{
obj* x_2434; obj* x_2436; obj* x_2437; 
lean::dec(x_2419);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2434 = lean::cnstr_get(x_2429, 0);
if (lean::is_exclusive(x_2429)) {
 x_2436 = x_2429;
} else {
 lean::inc(x_2434);
 lean::dec(x_2429);
 x_2436 = lean::box(0);
}
if (lean::is_scalar(x_2436)) {
 x_2437 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2437 = x_2436;
}
lean::cnstr_set(x_2437, 0, x_2434);
return x_2437;
}
else
{
obj* x_2438; obj* x_2440; obj* x_2441; obj* x_2443; obj* x_2445; obj* x_2447; obj* x_2448; obj* x_2449; obj* x_2452; obj* x_2453; obj* x_2454; obj* x_2455; obj* x_2456; obj* x_2457; uint8 x_2458; 
x_2438 = lean::cnstr_get(x_2429, 0);
if (lean::is_exclusive(x_2429)) {
 lean::cnstr_set(x_2429, 0, lean::box(0));
 x_2440 = x_2429;
} else {
 lean::inc(x_2438);
 lean::dec(x_2429);
 x_2440 = lean::box(0);
}
x_2441 = lean::cnstr_get(x_2438, 0);
x_2443 = lean::cnstr_get(x_2438, 1);
if (lean::is_exclusive(x_2438)) {
 lean::cnstr_set(x_2438, 0, lean::box(0));
 lean::cnstr_set(x_2438, 1, lean::box(0));
 x_2445 = x_2438;
} else {
 lean::inc(x_2441);
 lean::inc(x_2443);
 lean::dec(x_2438);
 x_2445 = lean::box(0);
}
lean::inc(x_2419);
x_2447 = l_Lean_Elaborator_mangleIdent(x_2419);
x_2448 = lean_expr_mk_const(x_2447, x_2441);
x_2449 = lean::cnstr_get(x_2419, 3);
lean::inc(x_2449);
lean::dec(x_2419);
x_2452 = lean::mk_nat_obj(0ul);
x_2453 = l_List_enumFrom___main___rarg(x_2452, x_2449);
x_2454 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2455 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_2454, x_2453);
x_2456 = lean_expr_mk_mdata(x_2455, x_2448);
x_2457 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2458 = lean_name_dec_eq(x_8, x_2457);
lean::dec(x_8);
if (x_2458 == 0)
{
obj* x_2460; obj* x_2461; 
x_2460 = lean::box(0);
x_2461 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2461) == 0)
{
obj* x_2464; obj* x_2465; 
lean::dec(x_2);
if (lean::is_scalar(x_2445)) {
 x_2464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2464 = x_2445;
}
lean::cnstr_set(x_2464, 0, x_2456);
lean::cnstr_set(x_2464, 1, x_2443);
if (lean::is_scalar(x_2440)) {
 x_2465 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2465 = x_2440;
}
lean::cnstr_set(x_2465, 0, x_2464);
return x_2465;
}
else
{
obj* x_2466; obj* x_2469; obj* x_2472; obj* x_2475; obj* x_2476; obj* x_2478; obj* x_2479; obj* x_2480; obj* x_2483; obj* x_2484; obj* x_2485; obj* x_2486; obj* x_2487; 
x_2466 = lean::cnstr_get(x_2461, 0);
lean::inc(x_2466);
lean::dec(x_2461);
x_2469 = lean::cnstr_get(x_2, 0);
lean::inc(x_2469);
lean::dec(x_2);
x_2472 = lean::cnstr_get(x_2469, 2);
lean::inc(x_2472);
lean::dec(x_2469);
x_2475 = l_Lean_FileMap_toPosition(x_2472, x_2466);
x_2476 = lean::cnstr_get(x_2475, 1);
lean::inc(x_2476);
x_2478 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2479 = l_Lean_KVMap_setNat(x_2460, x_2478, x_2476);
x_2480 = lean::cnstr_get(x_2475, 0);
lean::inc(x_2480);
lean::dec(x_2475);
x_2483 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2484 = l_Lean_KVMap_setNat(x_2479, x_2483, x_2480);
x_2485 = lean_expr_mk_mdata(x_2484, x_2456);
if (lean::is_scalar(x_2445)) {
 x_2486 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2486 = x_2445;
}
lean::cnstr_set(x_2486, 0, x_2485);
lean::cnstr_set(x_2486, 1, x_2443);
if (lean::is_scalar(x_2440)) {
 x_2487 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2487 = x_2440;
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
if (lean::is_scalar(x_2445)) {
 x_2490 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2490 = x_2445;
}
lean::cnstr_set(x_2490, 0, x_2456);
lean::cnstr_set(x_2490, 1, x_2443);
if (lean::is_scalar(x_2440)) {
 x_2491 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2491 = x_2440;
}
lean::cnstr_set(x_2491, 0, x_2490);
return x_2491;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2495; obj* x_2497; obj* x_2498; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2495 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2497 = x_13;
} else {
 lean::inc(x_2495);
 lean::dec(x_13);
 x_2497 = lean::box(0);
}
if (lean::is_scalar(x_2497)) {
 x_2498 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2498 = x_2497;
}
lean::cnstr_set(x_2498, 0, x_2495);
return x_2498;
}
else
{
obj* x_2499; obj* x_2501; obj* x_2502; obj* x_2504; obj* x_2506; obj* x_2507; uint8 x_2508; 
x_2499 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2501 = x_13;
} else {
 lean::inc(x_2499);
 lean::dec(x_13);
 x_2501 = lean::box(0);
}
x_2502 = lean::cnstr_get(x_2499, 0);
x_2504 = lean::cnstr_get(x_2499, 1);
if (lean::is_exclusive(x_2499)) {
 lean::cnstr_set(x_2499, 0, lean::box(0));
 lean::cnstr_set(x_2499, 1, lean::box(0));
 x_2506 = x_2499;
} else {
 lean::inc(x_2502);
 lean::inc(x_2504);
 lean::dec(x_2499);
 x_2506 = lean::box(0);
}
x_2507 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2508 = lean_name_dec_eq(x_8, x_2507);
lean::dec(x_8);
if (x_2508 == 0)
{
obj* x_2510; 
x_2510 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2510) == 0)
{
obj* x_2513; obj* x_2514; 
lean::dec(x_2);
if (lean::is_scalar(x_2506)) {
 x_2513 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2513 = x_2506;
}
lean::cnstr_set(x_2513, 0, x_2502);
lean::cnstr_set(x_2513, 1, x_2504);
if (lean::is_scalar(x_2501)) {
 x_2514 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2514 = x_2501;
}
lean::cnstr_set(x_2514, 0, x_2513);
return x_2514;
}
else
{
obj* x_2515; obj* x_2518; obj* x_2521; obj* x_2524; obj* x_2525; obj* x_2527; obj* x_2528; obj* x_2529; obj* x_2530; obj* x_2533; obj* x_2534; obj* x_2535; obj* x_2536; obj* x_2537; 
x_2515 = lean::cnstr_get(x_2510, 0);
lean::inc(x_2515);
lean::dec(x_2510);
x_2518 = lean::cnstr_get(x_2, 0);
lean::inc(x_2518);
lean::dec(x_2);
x_2521 = lean::cnstr_get(x_2518, 2);
lean::inc(x_2521);
lean::dec(x_2518);
x_2524 = l_Lean_FileMap_toPosition(x_2521, x_2515);
x_2525 = lean::cnstr_get(x_2524, 1);
lean::inc(x_2525);
x_2527 = lean::box(0);
x_2528 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2529 = l_Lean_KVMap_setNat(x_2527, x_2528, x_2525);
x_2530 = lean::cnstr_get(x_2524, 0);
lean::inc(x_2530);
lean::dec(x_2524);
x_2533 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2534 = l_Lean_KVMap_setNat(x_2529, x_2533, x_2530);
x_2535 = lean_expr_mk_mdata(x_2534, x_2502);
if (lean::is_scalar(x_2506)) {
 x_2536 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2536 = x_2506;
}
lean::cnstr_set(x_2536, 0, x_2535);
lean::cnstr_set(x_2536, 1, x_2504);
if (lean::is_scalar(x_2501)) {
 x_2537 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2537 = x_2501;
}
lean::cnstr_set(x_2537, 0, x_2536);
return x_2537;
}
}
else
{
obj* x_2540; obj* x_2541; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2506)) {
 x_2540 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2540 = x_2506;
}
lean::cnstr_set(x_2540, 0, x_2502);
lean::cnstr_set(x_2540, 1, x_2504);
if (lean::is_scalar(x_2501)) {
 x_2541 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2541 = x_2501;
}
lean::cnstr_set(x_2541, 0, x_2540);
return x_2541;
}
}
}
lbl_16:
{
obj* x_2542; obj* x_2544; obj* x_2546; obj* x_2547; uint8 x_2548; 
x_2542 = lean::cnstr_get(x_15, 0);
x_2544 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2546 = x_15;
} else {
 lean::inc(x_2542);
 lean::inc(x_2544);
 lean::dec(x_15);
 x_2546 = lean::box(0);
}
x_2547 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2548 = lean_name_dec_eq(x_8, x_2547);
lean::dec(x_8);
if (x_2548 == 0)
{
obj* x_2550; 
x_2550 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2550) == 0)
{
obj* x_2553; obj* x_2554; 
lean::dec(x_2);
if (lean::is_scalar(x_2546)) {
 x_2553 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2553 = x_2546;
}
lean::cnstr_set(x_2553, 0, x_2542);
lean::cnstr_set(x_2553, 1, x_2544);
x_2554 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2554, 0, x_2553);
return x_2554;
}
else
{
obj* x_2555; obj* x_2558; obj* x_2561; obj* x_2564; obj* x_2565; obj* x_2567; obj* x_2568; obj* x_2569; obj* x_2570; obj* x_2573; obj* x_2574; obj* x_2575; obj* x_2576; obj* x_2577; 
x_2555 = lean::cnstr_get(x_2550, 0);
lean::inc(x_2555);
lean::dec(x_2550);
x_2558 = lean::cnstr_get(x_2, 0);
lean::inc(x_2558);
lean::dec(x_2);
x_2561 = lean::cnstr_get(x_2558, 2);
lean::inc(x_2561);
lean::dec(x_2558);
x_2564 = l_Lean_FileMap_toPosition(x_2561, x_2555);
x_2565 = lean::cnstr_get(x_2564, 1);
lean::inc(x_2565);
x_2567 = lean::box(0);
x_2568 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2569 = l_Lean_KVMap_setNat(x_2567, x_2568, x_2565);
x_2570 = lean::cnstr_get(x_2564, 0);
lean::inc(x_2570);
lean::dec(x_2564);
x_2573 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2574 = l_Lean_KVMap_setNat(x_2569, x_2573, x_2570);
x_2575 = lean_expr_mk_mdata(x_2574, x_2542);
if (lean::is_scalar(x_2546)) {
 x_2576 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2576 = x_2546;
}
lean::cnstr_set(x_2576, 0, x_2575);
lean::cnstr_set(x_2576, 1, x_2544);
x_2577 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2577, 0, x_2576);
return x_2577;
}
}
else
{
obj* x_2580; obj* x_2581; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2546)) {
 x_2580 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2580 = x_2546;
}
lean::cnstr_set(x_2580, 0, x_2542);
lean::cnstr_set(x_2580, 1, x_2544);
x_2581 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2581, 0, x_2580);
return x_2581;
}
}
}
default:
{
obj* x_2582; 
x_2582 = lean::box(0);
x_4 = x_2582;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2585; obj* x_2586; obj* x_2587; obj* x_2588; obj* x_2589; obj* x_2590; obj* x_2592; 
lean::dec(x_4);
lean::inc(x_0);
x_2585 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2585, 0, x_0);
x_2586 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_2587 = l_Lean_Options_empty;
x_2588 = l_Lean_Format_pretty(x_2586, x_2587);
x_2589 = l_Lean_Elaborator_toPexpr___main___closed__1;
x_2590 = lean::string_append(x_2589, x_2588);
lean::dec(x_2588);
x_2592 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2585, x_2590, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2585);
return x_2592;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
x_17 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
}
}
obj* _init_l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_0;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1;
x_3 = l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8(x_1, x_2, x_0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
x_17 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12(x_0, x_10, x_2, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
}
}
obj* _init_l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Elaborator_OrderedRBMap_empty___closed__1;
return x_0;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1;
x_3 = l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16(x_1, x_2, x_0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__17(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__17(x_4);
x_9 = lean::box(0);
x_10 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19(x_7, x_8, x_2, x_9);
return x_10;
}
}
}
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1(x_8);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
x_13 = l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9(x_11);
x_14 = lean::cnstr_get(x_0, 4);
lean::inc(x_14);
x_16 = l_RBTree_ofList___main___at_Lean_Elaborator_oldElabCommand___spec__17(x_14);
x_17 = lean::cnstr_get(x_1, 6);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 7);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_0, 5);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_10);
lean::cnstr_set(x_25, 4, x_13);
lean::cnstr_set(x_25, 5, x_16);
lean::cnstr_set(x_25, 6, x_17);
lean::cnstr_set(x_25, 7, x_19);
lean::cnstr_set(x_25, 8, x_22);
return x_25;
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
x_77 = l_RBTree_toList___rarg(x_75);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__12(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_19; 
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
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::inc(x_2);
x_19 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1(x_16, x_1, x_2, x_3);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_12);
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
obj* x_28; obj* x_31; obj* x_33; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(x_10, x_1, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_31);
x_40 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_42 = x_36;
} else {
 lean::inc(x_40);
 lean::dec(x_36);
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
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_55; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_44 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_46 = x_36;
} else {
 lean::inc(x_44);
 lean::dec(x_36);
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
x_52 = lean::cnstr_get(x_13, 0);
lean::inc(x_52);
lean::dec(x_13);
x_55 = lean::cnstr_get(x_52, 2);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_Lean_Expr_mkCapp(x_55, x_31);
if (lean::is_scalar(x_12)) {
 x_59 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_59 = x_12;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_47);
if (lean::is_scalar(x_51)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_51;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_49);
if (lean::is_scalar(x_46)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_46;
}
lean::cnstr_set(x_61, 0, x_60);
return x_61;
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_25; 
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
lean::inc(x_2);
x_25 = l_Lean_Elaborator_toPexpr___main(x_21, x_1, x_2, x_3);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_16);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_33 = x_25;
} else {
 lean::inc(x_31);
 lean::dec(x_25);
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
obj* x_35; obj* x_38; obj* x_40; obj* x_43; 
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
lean::dec(x_25);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
x_43 = l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(x_10, x_1, x_2, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_12);
lean::dec(x_38);
lean::dec(x_16);
lean::dec(x_19);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; uint8 x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_52 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_54 = x_43;
} else {
 lean::inc(x_52);
 lean::dec(x_43);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_52, 0);
x_57 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_59 = x_52;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_52);
 x_59 = lean::box(0);
}
x_60 = l_Lean_Elaborator_mangleIdent(x_19);
x_61 = lean::unbox(x_16);
lean::inc(x_60);
x_63 = lean_expr_local(x_60, x_60, x_38, x_61);
if (lean::is_scalar(x_12)) {
 x_64 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_64 = x_12;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_55);
if (lean::is_scalar(x_59)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_59;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_54;
}
lean::cnstr_set(x_66, 0, x_65);
return x_66;
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
obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_60; 
x_51 = lean::cnstr_get(x_40, 0);
lean::inc(x_51);
lean::dec(x_40);
x_54 = lean::cnstr_get(x_51, 0);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_set(x_51, 1, lean::box(0));
 x_58 = x_51;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
lean::inc(x_0);
x_60 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_0, x_12, x_2, x_3, x_56);
if (lean::obj_tag(x_60) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_35);
lean::dec(x_31);
lean::dec(x_54);
lean::dec(x_58);
x_67 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_69 = x_60;
} else {
 lean::inc(x_67);
 lean::dec(x_60);
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
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_71 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_73 = x_60;
} else {
 lean::inc(x_71);
 lean::dec(x_60);
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
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_31);
lean::cnstr_set(x_79, 1, x_54);
if (lean::is_scalar(x_58)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_58;
}
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_79);
if (lean::is_scalar(x_14)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_14;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_74);
if (lean::is_scalar(x_35)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_35;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_76);
if (lean::is_scalar(x_73)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_73;
}
lean::cnstr_set(x_83, 0, x_82);
return x_83;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::box(0);
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
lean::dec(x_0);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5(x_3, x_10, x_1, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__8(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = level_mk_param(x_2);
x_9 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__3(x_0, x_2, x_8);
x_0 = x_9;
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
x_14 = l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__8(x_8, x_13);
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
lean::dec(x_16);
return x_18;
}
else
{
obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_31; obj* x_35; 
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
lean::inc(x_5);
x_35 = l_Lean_Elaborator_declModifiersToPexpr(x_1, x_4, x_5, x_6);
if (lean::obj_tag(x_35) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
x_44 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_46 = x_35;
} else {
 lean::inc(x_44);
 lean::dec(x_35);
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
obj* x_48; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
lean::dec(x_35);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
lean::dec(x_48);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_3);
x_58 = lean_expr_mk_lit(x_57);
if (lean::obj_tag(x_21) == 0)
{
obj* x_62; obj* x_65; 
x_62 = l_Lean_Expander_getOptType___main(x_28);
lean::dec(x_28);
lean::inc(x_5);
x_65 = l_Lean_Elaborator_toPexpr___main(x_62, x_4, x_5, x_53);
if (lean::obj_tag(x_21) == 0)
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_73 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_75 = x_65;
} else {
 lean::inc(x_73);
 lean::dec(x_65);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
return x_76;
}
else
{
obj* x_77; 
x_77 = lean::cnstr_get(x_65, 0);
lean::inc(x_77);
lean::dec(x_65);
x_59 = x_56;
x_60 = x_77;
goto lbl_61;
}
}
else
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_87 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_89 = x_65;
} else {
 lean::inc(x_87);
 lean::dec(x_65);
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
obj* x_91; obj* x_94; obj* x_97; obj* x_100; 
x_91 = lean::cnstr_get(x_21, 0);
lean::inc(x_91);
lean::dec(x_21);
x_94 = lean::cnstr_get(x_65, 0);
lean::inc(x_94);
lean::dec(x_65);
x_97 = lean::cnstr_get(x_91, 1);
lean::inc(x_97);
lean::dec(x_91);
x_100 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_97);
x_59 = x_100;
x_60 = x_94;
goto lbl_61;
}
}
}
else
{
obj* x_101; obj* x_104; obj* x_106; 
x_101 = lean::cnstr_get(x_21, 0);
lean::inc(x_101);
lean::inc(x_101);
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_104, 0, x_101);
lean::inc(x_5);
x_106 = l_Lean_Elaborator_modifyCurrentScope(x_104, x_4, x_5, x_53);
if (lean::obj_tag(x_106) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_28);
lean::dec(x_51);
lean::dec(x_101);
x_117 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 x_119 = x_106;
} else {
 lean::inc(x_117);
 lean::dec(x_106);
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
obj* x_121; obj* x_124; obj* x_127; obj* x_130; 
x_121 = lean::cnstr_get(x_106, 0);
lean::inc(x_121);
lean::dec(x_106);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
x_127 = l_Lean_Expander_getOptType___main(x_28);
lean::dec(x_28);
lean::inc(x_5);
x_130 = l_Lean_Elaborator_toPexpr___main(x_127, x_4, x_5, x_124);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_101);
if (lean::obj_tag(x_130) == 0)
{
obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
x_139 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_141 = x_130;
} else {
 lean::inc(x_139);
 lean::dec(x_130);
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
obj* x_143; 
x_143 = lean::cnstr_get(x_130, 0);
lean::inc(x_143);
lean::dec(x_130);
x_59 = x_56;
x_60 = x_143;
goto lbl_61;
}
}
else
{
lean::dec(x_21);
if (lean::obj_tag(x_130) == 0)
{
obj* x_155; obj* x_157; obj* x_158; 
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_51);
lean::dec(x_101);
x_155 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_157 = x_130;
} else {
 lean::inc(x_155);
 lean::dec(x_130);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
return x_158;
}
else
{
obj* x_159; obj* x_162; obj* x_165; 
x_159 = lean::cnstr_get(x_130, 0);
lean::inc(x_159);
lean::dec(x_130);
x_162 = lean::cnstr_get(x_101, 1);
lean::inc(x_162);
lean::dec(x_101);
x_165 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_162);
x_59 = x_165;
x_60 = x_159;
goto lbl_61;
}
}
}
}
lbl_61:
{
obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_175; uint8 x_176; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
x_166 = lean::cnstr_get(x_60, 0);
x_168 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_set(x_60, 0, lean::box(0));
 lean::cnstr_set(x_60, 1, lean::box(0));
 x_170 = x_60;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_60);
 x_170 = lean::box(0);
}
x_171 = l_Lean_Elaborator_namesToPexpr(x_59);
x_172 = lean::cnstr_get(x_23, 0);
lean::inc(x_172);
lean::dec(x_23);
x_175 = l_Lean_Elaborator_mangleIdent(x_172);
x_176 = 4;
lean::inc(x_166);
lean::inc(x_175);
lean::inc(x_175);
x_180 = lean_expr_local(x_175, x_175, x_166, x_176);
x_181 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_56);
x_182 = l_Lean_Elaborator_mkEqns___closed__1;
x_183 = l_Lean_Expr_mkCapp(x_182, x_181);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_189; obj* x_192; obj* x_196; 
lean::dec(x_170);
lean::dec(x_175);
lean::dec(x_166);
x_189 = lean::cnstr_get(x_25, 0);
lean::inc(x_189);
lean::dec(x_25);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
lean::dec(x_189);
lean::inc(x_5);
x_196 = l_Lean_Elaborator_toPexpr___main(x_192, x_4, x_5, x_168);
if (lean::obj_tag(x_196) == 0)
{
obj* x_204; obj* x_206; obj* x_207; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_204 = lean::cnstr_get(x_196, 0);
if (lean::is_exclusive(x_196)) {
 x_206 = x_196;
} else {
 lean::inc(x_204);
 lean::dec(x_196);
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
obj* x_208; 
x_208 = lean::cnstr_get(x_196, 0);
lean::inc(x_208);
lean::dec(x_196);
x_184 = x_208;
goto lbl_185;
}
}
case 1:
{
obj* x_213; obj* x_214; 
lean::dec(x_175);
lean::dec(x_25);
x_213 = l_Lean_Elaborator_mkEqns(x_166, x_56);
if (lean::is_scalar(x_170)) {
 x_214 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_214 = x_170;
}
lean::cnstr_set(x_214, 0, x_213);
lean::cnstr_set(x_214, 1, x_168);
x_184 = x_214;
goto lbl_185;
}
default:
{
obj* x_216; obj* x_220; 
lean::dec(x_170);
x_216 = lean::cnstr_get(x_25, 0);
lean::inc(x_216);
lean::dec(x_25);
lean::inc(x_5);
x_220 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_175, x_216, x_4, x_5, x_168);
if (lean::obj_tag(x_220) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_31);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_166);
lean::dec(x_171);
x_229 = lean::cnstr_get(x_220, 0);
if (lean::is_exclusive(x_220)) {
 x_231 = x_220;
} else {
 lean::inc(x_229);
 lean::dec(x_220);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
return x_232;
}
else
{
obj* x_233; obj* x_236; obj* x_238; obj* x_240; obj* x_241; obj* x_242; 
x_233 = lean::cnstr_get(x_220, 0);
lean::inc(x_233);
lean::dec(x_220);
x_236 = lean::cnstr_get(x_233, 0);
x_238 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 x_240 = x_233;
} else {
 lean::inc(x_236);
 lean::inc(x_238);
 lean::dec(x_233);
 x_240 = lean::box(0);
}
x_241 = l_Lean_Elaborator_mkEqns(x_166, x_236);
if (lean::is_scalar(x_240)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_240;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_238);
x_184 = x_242;
goto lbl_185;
}
}
}
lbl_185:
{
obj* x_243; obj* x_245; obj* x_249; 
x_243 = lean::cnstr_get(x_184, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_184, 1);
lean::inc(x_245);
lean::dec(x_184);
lean::inc(x_5);
x_249 = l_Lean_Elaborator_simpleBindersToPexpr(x_31, x_4, x_5, x_245);
if (lean::obj_tag(x_249) == 0)
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_243);
lean::dec(x_183);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_171);
x_257 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_259 = x_249;
} else {
 lean::inc(x_257);
 lean::dec(x_249);
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
obj* x_261; obj* x_264; obj* x_266; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
x_261 = lean::cnstr_get(x_249, 0);
lean::inc(x_261);
lean::dec(x_249);
x_264 = lean::cnstr_get(x_261, 0);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_261, 1);
lean::inc(x_266);
lean::dec(x_261);
x_269 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_269, 0, x_243);
lean::cnstr_set(x_269, 1, x_56);
x_270 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_270, 0, x_264);
lean::cnstr_set(x_270, 1, x_269);
x_271 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_271, 0, x_183);
lean::cnstr_set(x_271, 1, x_270);
x_272 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_272, 0, x_171);
lean::cnstr_set(x_272, 1, x_271);
x_273 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_273, 0, x_58);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_274, 0, x_51);
lean::cnstr_set(x_274, 1, x_273);
x_275 = l_Lean_Expr_mkCapp(x_182, x_274);
x_276 = l_Lean_Elaborator_elabDefLike___closed__2;
x_277 = lean_expr_mk_mdata(x_276, x_275);
x_278 = l_Lean_Elaborator_oldElabCommand(x_0, x_277, x_4, x_5, x_266);
lean::dec(x_0);
return x_278;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* _init_l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("Declaration.elaborate: unexpected input");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_19);
lean::inc(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_0);
x_26 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_28 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_25, x_26, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_35 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_37 = x_28;
} else {
 lean::inc(x_35);
 lean::dec(x_28);
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
obj* x_39; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_15 = x_39;
goto lbl_16;
}
}
else
{
obj* x_42; 
x_42 = lean::cnstr_get(x_19, 0);
lean::inc(x_42);
lean::dec(x_19);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; 
x_45 = lean::cnstr_get(x_17, 1);
lean::inc(x_45);
lean::dec(x_17);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; obj* x_51; obj* x_53; 
lean::dec(x_10);
lean::inc(x_0);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_0);
x_51 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_53 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_50, x_51, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_50);
if (lean::obj_tag(x_53) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_60 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_62 = x_53;
} else {
 lean::inc(x_60);
 lean::dec(x_53);
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
obj* x_64; 
x_64 = lean::cnstr_get(x_53, 0);
lean::inc(x_64);
lean::dec(x_53);
x_15 = x_64;
goto lbl_16;
}
}
else
{
obj* x_67; obj* x_70; obj* x_74; 
x_67 = lean::cnstr_get(x_45, 0);
lean::inc(x_67);
lean::dec(x_45);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
lean::inc(x_3);
x_74 = l_Lean_Elaborator_toPexpr___main(x_70, x_2, x_3, x_4);
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_12);
x_80 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_82 = x_74;
} else {
 lean::inc(x_80);
 lean::dec(x_74);
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
obj* x_84; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_95; uint8 x_96; obj* x_98; obj* x_99; 
x_84 = lean::cnstr_get(x_74, 0);
lean::inc(x_84);
lean::dec(x_74);
x_87 = lean::cnstr_get(x_84, 0);
x_89 = lean::cnstr_get(x_84, 1);
if (lean::is_exclusive(x_84)) {
 x_91 = x_84;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_84);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_10, 1);
lean::inc(x_92);
lean::dec(x_10);
x_95 = l_Lean_Elaborator_mangleIdent(x_92);
x_96 = 0;
lean::inc(x_95);
x_98 = lean_expr_local(x_95, x_95, x_87, x_96);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_89);
x_15 = x_99;
goto lbl_16;
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_42);
lean::inc(x_0);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_0);
x_105 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
lean::inc(x_3);
x_107 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_104, x_105, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_104);
if (lean::obj_tag(x_107) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_114 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_116 = x_107;
} else {
 lean::inc(x_114);
 lean::dec(x_107);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
return x_117;
}
else
{
obj* x_118; 
x_118 = lean::cnstr_get(x_107, 0);
lean::inc(x_118);
lean::dec(x_107);
x_15 = x_118;
goto lbl_16;
}
}
}
lbl_16:
{
obj* x_121; obj* x_123; obj* x_126; 
x_121 = lean::cnstr_get(x_15, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_15, 1);
lean::inc(x_123);
lean::dec(x_15);
x_126 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(x_0, x_12, x_2, x_3, x_123);
if (lean::obj_tag(x_126) == 0)
{
obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_14);
lean::dec(x_121);
x_129 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_131 = x_126;
} else {
 lean::inc(x_129);
 lean::dec(x_126);
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
obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_133 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_135 = x_126;
} else {
 lean::inc(x_133);
 lean::dec(x_126);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_133, 0);
x_138 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 x_140 = x_133;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_133);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_14;
}
lean::cnstr_set(x_141, 0, x_121);
lean::cnstr_set(x_141, 1, x_136);
if (lean::is_scalar(x_140)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_140;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
if (lean::is_scalar(x_135)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_135;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_10, x_1, x_2, x_30);
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_28 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
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
obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_92; obj* x_94; obj* x_97; obj* x_100; 
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
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
lean::dec(x_92);
x_97 = l_Lean_Expander_getOptType___main(x_94);
lean::dec(x_94);
lean::inc(x_4);
x_100 = l_Lean_Elaborator_toPexpr___main(x_97, x_3, x_4, x_84);
if (lean::obj_tag(x_100) == 0)
{
obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_87);
lean::dec(x_89);
x_108 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_110 = x_100;
} else {
 lean::inc(x_108);
 lean::dec(x_100);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
return x_111;
}
else
{
obj* x_112; obj* x_115; obj* x_117; obj* x_121; 
x_112 = lean::cnstr_get(x_100, 0);
lean::inc(x_112);
lean::dec(x_100);
x_115 = lean::cnstr_get(x_112, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
lean::dec(x_112);
lean::inc(x_1);
x_121 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_0, x_1, x_14, x_3, x_4, x_117);
if (lean::obj_tag(x_121) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_87);
lean::dec(x_89);
lean::dec(x_115);
x_127 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_129 = x_121;
} else {
 lean::inc(x_127);
 lean::dec(x_121);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_138; obj* x_139; uint8 x_140; obj* x_143; obj* x_144; obj* x_146; obj* x_147; obj* x_148; obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_131 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 x_133 = x_121;
} else {
 lean::inc(x_131);
 lean::dec(x_121);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_131, 0);
x_136 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_138 = x_131;
} else {
 lean::inc(x_134);
 lean::inc(x_136);
 lean::dec(x_131);
 x_138 = lean::box(0);
}
x_139 = l_Lean_Elaborator_dummy;
x_140 = lean::unbox(x_87);
lean::inc(x_1);
lean::inc(x_1);
x_143 = lean_expr_local(x_1, x_1, x_139, x_140);
x_144 = lean::cnstr_get(x_89, 0);
lean::inc(x_144);
x_146 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_144);
x_147 = l_Lean_Elaborator_namesToPexpr(x_146);
x_148 = lean::cnstr_get(x_89, 1);
lean::inc(x_148);
lean::dec(x_89);
x_151 = l_Lean_Elaborator_inferModToPexpr(x_148);
lean::dec(x_148);
x_153 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_154 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_154 = x_16;
}
lean::cnstr_set(x_154, 0, x_115);
lean::cnstr_set(x_154, 1, x_153);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set(x_155, 1, x_154);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_147);
lean::cnstr_set(x_156, 1, x_155);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_143);
lean::cnstr_set(x_157, 1, x_156);
x_158 = l_Lean_Expr_mkCapp(x_1, x_157);
x_159 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_134);
if (lean::is_scalar(x_138)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_138;
}
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_136);
if (lean::is_scalar(x_133)) {
 x_161 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_161 = x_133;
}
lean::cnstr_set(x_161, 0, x_160);
return x_161;
}
}
}
}
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_7);
x_13 = l_Lean_Elaborator_toPexpr___main(x_9, x_6, x_7, x_8);
if (lean::obj_tag(x_13) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
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
obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_Lean_Elaborator_identUnivParamsToPexpr(x_1);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_26);
lean::cnstr_set(x_32, 1, x_2);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Elaborator_mkEqns___closed__1;
x_36 = l_Lean_Expr_mkCapp(x_35, x_34);
x_37 = lean_expr_mk_mdata(x_3, x_36);
x_38 = l_Lean_Elaborator_oldElabCommand(x_4, x_37, x_6, x_7, x_28);
return x_38;
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
obj* x_21; 
lean::inc(x_11);
x_21 = l_Lean_Elaborator_attrsToPexpr(x_13, x_10, x_11, x_12);
if (lean::obj_tag(x_21) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_35; obj* x_38; obj* x_40; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_35 = lean::cnstr_get(x_21, 0);
lean::inc(x_35);
lean::dec(x_21);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
lean::inc(x_0);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_0);
x_45 = l_Lean_Elaborator_mkEqns___closed__1;
x_46 = l_Lean_Expr_mkCapp(x_45, x_44);
if (lean::obj_tag(x_6) == 0)
{
obj* x_50; obj* x_52; 
x_50 = l_Lean_Expander_getOptType___main(x_7);
lean::inc(x_11);
x_52 = l_Lean_Elaborator_toPexpr___main(x_50, x_10, x_11, x_40);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_62 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_64 = x_52;
} else {
 lean::inc(x_62);
 lean::dec(x_52);
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
obj* x_66; 
x_66 = lean::cnstr_get(x_52, 0);
lean::inc(x_66);
lean::dec(x_52);
lean::inc(x_0);
x_47 = x_0;
x_48 = x_66;
goto lbl_49;
}
}
else
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_81 = x_52;
} else {
 lean::inc(x_79);
 lean::dec(x_52);
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
obj* x_83; obj* x_86; obj* x_89; obj* x_92; 
x_83 = lean::cnstr_get(x_6, 0);
lean::inc(x_83);
lean::dec(x_6);
x_86 = lean::cnstr_get(x_52, 0);
lean::inc(x_86);
lean::dec(x_52);
x_89 = lean::cnstr_get(x_83, 1);
lean::inc(x_89);
lean::dec(x_83);
x_92 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_89);
x_47 = x_92;
x_48 = x_86;
goto lbl_49;
}
}
}
else
{
obj* x_93; obj* x_96; obj* x_98; 
x_93 = lean::cnstr_get(x_6, 0);
lean::inc(x_93);
lean::inc(x_93);
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_96, 0, x_93);
lean::inc(x_11);
x_98 = l_Lean_Elaborator_modifyCurrentScope(x_96, x_10, x_11, x_40);
if (lean::obj_tag(x_98) == 0)
{
obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_93);
lean::dec(x_46);
x_110 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 x_112 = x_98;
} else {
 lean::inc(x_110);
 lean::dec(x_98);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
return x_113;
}
else
{
obj* x_114; obj* x_117; obj* x_120; obj* x_122; 
x_114 = lean::cnstr_get(x_98, 0);
lean::inc(x_114);
lean::dec(x_98);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_120 = l_Lean_Expander_getOptType___main(x_7);
lean::inc(x_11);
x_122 = l_Lean_Elaborator_toPexpr___main(x_120, x_10, x_11, x_117);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_93);
if (lean::obj_tag(x_122) == 0)
{
obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_133 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_135 = x_122;
} else {
 lean::inc(x_133);
 lean::dec(x_122);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
return x_136;
}
else
{
obj* x_137; 
x_137 = lean::cnstr_get(x_122, 0);
lean::inc(x_137);
lean::dec(x_122);
lean::inc(x_0);
x_47 = x_0;
x_48 = x_137;
goto lbl_49;
}
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_122) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_93);
lean::dec(x_46);
x_152 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_154 = x_122;
} else {
 lean::inc(x_152);
 lean::dec(x_122);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
return x_155;
}
else
{
obj* x_156; obj* x_159; obj* x_162; 
x_156 = lean::cnstr_get(x_122, 0);
lean::inc(x_156);
lean::dec(x_122);
x_159 = lean::cnstr_get(x_93, 1);
lean::inc(x_159);
lean::dec(x_93);
x_162 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_159);
x_47 = x_162;
x_48 = x_156;
goto lbl_49;
}
}
}
}
lbl_49:
{
obj* x_163; obj* x_165; obj* x_169; 
x_163 = lean::cnstr_get(x_48, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_48, 1);
lean::inc(x_165);
lean::dec(x_48);
lean::inc(x_11);
x_169 = l_Lean_Elaborator_simpleBindersToPexpr(x_1, x_10, x_11, x_165);
if (lean::obj_tag(x_169) == 0)
{
obj* x_180; obj* x_182; obj* x_183; 
lean::dec(x_163);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_47);
x_180 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_182 = x_169;
} else {
 lean::inc(x_180);
 lean::dec(x_169);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
return x_183;
}
else
{
obj* x_184; obj* x_187; obj* x_189; obj* x_195; 
x_184 = lean::cnstr_get(x_169, 0);
lean::inc(x_184);
lean::dec(x_169);
x_187 = lean::cnstr_get(x_184, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 1);
lean::inc(x_189);
lean::dec(x_184);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_2);
x_195 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(x_2, x_3, x_10, x_11, x_189);
if (lean::obj_tag(x_195) == 0)
{
obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_187);
lean::dec(x_163);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
lean::dec(x_47);
x_207 = lean::cnstr_get(x_195, 0);
if (lean::is_exclusive(x_195)) {
 x_209 = x_195;
} else {
 lean::inc(x_207);
 lean::dec(x_195);
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
obj* x_211; obj* x_214; obj* x_216; obj* x_219; obj* x_220; obj* x_223; uint8 x_224; obj* x_226; obj* x_228; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
x_211 = lean::cnstr_get(x_195, 0);
lean::inc(x_211);
lean::dec(x_195);
x_214 = lean::cnstr_get(x_211, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_211, 1);
lean::inc(x_216);
lean::dec(x_211);
x_219 = l_Lean_Elaborator_namesToPexpr(x_47);
x_220 = lean::cnstr_get(x_4, 0);
lean::inc(x_220);
lean::dec(x_4);
x_223 = l_Lean_Elaborator_mangleIdent(x_220);
x_224 = 0;
lean::inc(x_223);
x_226 = lean_expr_local(x_223, x_223, x_163, x_224);
lean::inc(x_0);
x_228 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_228, 0, x_226);
lean::cnstr_set(x_228, 1, x_0);
x_229 = l_Lean_Expr_mkCapp(x_45, x_228);
x_230 = l_Lean_Expr_mkCapp(x_45, x_214);
lean::inc(x_0);
x_232 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_232, 0, x_230);
lean::cnstr_set(x_232, 1, x_0);
x_233 = l_Lean_Expr_mkCapp(x_45, x_232);
x_234 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(x_3);
x_235 = l_Lean_Expr_mkCapp(x_45, x_234);
lean::inc(x_0);
x_237 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_237, 0, x_235);
lean::cnstr_set(x_237, 1, x_0);
x_238 = l_Lean_Expr_mkCapp(x_45, x_237);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_0);
x_240 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_240, 0, x_233);
lean::cnstr_set(x_240, 1, x_239);
x_241 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_241, 0, x_187);
lean::cnstr_set(x_241, 1, x_240);
x_242 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_242, 0, x_229);
lean::cnstr_set(x_242, 1, x_241);
x_243 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_243, 0, x_219);
lean::cnstr_set(x_243, 1, x_242);
x_244 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_244, 0, x_46);
lean::cnstr_set(x_244, 1, x_243);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_9);
lean::cnstr_set(x_245, 1, x_244);
x_246 = l_Lean_Expr_mkCapp(x_45, x_245);
x_247 = lean_expr_mk_mdata(x_5, x_246);
x_248 = l_Lean_Elaborator_oldElabCommand(x_2, x_247, x_10, x_11, x_216);
lean::dec(x_2);
return x_248;
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
obj* x_17; obj* x_19; 
x_17 = l_Lean_Expander_getOptType___main(x_9);
lean::inc(x_12);
x_19 = l_Lean_Elaborator_toPexpr___main(x_17, x_11, x_12, x_13);
if (lean::obj_tag(x_8) == 0)
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_31 = x_19;
} else {
 lean::inc(x_29);
 lean::dec(x_19);
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
obj* x_33; 
x_33 = lean::cnstr_get(x_19, 0);
lean::inc(x_33);
lean::dec(x_19);
lean::inc(x_5);
x_14 = x_5;
x_15 = x_33;
goto lbl_16;
}
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_48 = x_19;
} else {
 lean::inc(x_46);
 lean::dec(x_19);
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
obj* x_50; obj* x_53; obj* x_56; obj* x_59; 
x_50 = lean::cnstr_get(x_8, 0);
lean::inc(x_50);
lean::dec(x_8);
x_53 = lean::cnstr_get(x_19, 0);
lean::inc(x_53);
lean::dec(x_19);
x_56 = lean::cnstr_get(x_50, 1);
lean::inc(x_56);
lean::dec(x_50);
x_59 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_56);
x_14 = x_59;
x_15 = x_53;
goto lbl_16;
}
}
}
else
{
obj* x_60; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_8, 0);
lean::inc(x_60);
lean::inc(x_60);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___lambda__1), 2, 1);
lean::closure_set(x_63, 0, x_60);
lean::inc(x_12);
x_65 = l_Lean_Elaborator_modifyCurrentScope(x_63, x_11, x_12, x_13);
if (lean::obj_tag(x_65) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_60);
x_77 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_79 = x_65;
} else {
 lean::inc(x_77);
 lean::dec(x_65);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_87; obj* x_89; 
x_81 = lean::cnstr_get(x_65, 0);
lean::inc(x_81);
lean::dec(x_65);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
lean::dec(x_81);
x_87 = l_Lean_Expander_getOptType___main(x_9);
lean::inc(x_12);
x_89 = l_Lean_Elaborator_toPexpr___main(x_87, x_11, x_12, x_84);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_60);
if (lean::obj_tag(x_89) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
x_100 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_102 = x_89;
} else {
 lean::inc(x_100);
 lean::dec(x_89);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
return x_103;
}
else
{
obj* x_104; 
x_104 = lean::cnstr_get(x_89, 0);
lean::inc(x_104);
lean::dec(x_89);
lean::inc(x_5);
x_14 = x_5;
x_15 = x_104;
goto lbl_16;
}
}
else
{
lean::dec(x_8);
if (lean::obj_tag(x_89) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_60);
x_119 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_121 = x_89;
} else {
 lean::inc(x_119);
 lean::dec(x_89);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
return x_122;
}
else
{
obj* x_123; obj* x_126; obj* x_129; 
x_123 = lean::cnstr_get(x_89, 0);
lean::inc(x_123);
lean::dec(x_89);
x_126 = lean::cnstr_get(x_60, 1);
lean::inc(x_126);
lean::dec(x_60);
x_129 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__2(x_126);
x_14 = x_129;
x_15 = x_123;
goto lbl_16;
}
}
}
}
lbl_16:
{
obj* x_130; obj* x_132; obj* x_136; 
x_130 = lean::cnstr_get(x_15, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_15, 1);
lean::inc(x_132);
lean::dec(x_15);
lean::inc(x_12);
x_136 = l_Lean_Elaborator_simpleBindersToPexpr(x_0, x_11, x_12, x_132);
if (lean::obj_tag(x_136) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_14);
x_147 = lean::cnstr_get(x_136, 0);
if (lean::is_exclusive(x_136)) {
 x_149 = x_136;
} else {
 lean::inc(x_147);
 lean::dec(x_136);
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
obj* x_151; obj* x_154; obj* x_156; obj* x_159; obj* x_160; obj* x_163; obj* x_164; uint8 x_165; obj* x_167; obj* x_168; 
x_151 = lean::cnstr_get(x_136, 0);
lean::inc(x_151);
lean::dec(x_136);
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_151, 1);
lean::inc(x_156);
lean::dec(x_151);
x_159 = l_Lean_Elaborator_namesToPexpr(x_14);
x_160 = lean::cnstr_get(x_1, 0);
lean::inc(x_160);
lean::dec(x_1);
x_163 = l_Lean_Elaborator_mangleIdent(x_160);
x_164 = l_Lean_Elaborator_dummy;
x_165 = 0;
lean::inc(x_163);
x_167 = lean_expr_local(x_163, x_163, x_164, x_165);
if (lean::obj_tag(x_7) == 0)
{
lean::inc(x_5);
x_168 = x_5;
goto lbl_169;
}
else
{
obj* x_171; obj* x_172; 
x_171 = lean::cnstr_get(x_7, 0);
x_172 = lean::cnstr_get(x_171, 1);
lean::inc(x_172);
x_168 = x_172;
goto lbl_169;
}
lbl_169:
{
obj* x_175; 
lean::inc(x_12);
x_175 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_168, x_11, x_12, x_156);
if (lean::obj_tag(x_175) == 0)
{
obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_187 = lean::cnstr_get(x_175, 0);
if (lean::is_exclusive(x_175)) {
 x_189 = x_175;
} else {
 lean::inc(x_187);
 lean::dec(x_175);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
return x_190;
}
else
{
obj* x_191; obj* x_194; obj* x_196; obj* x_199; obj* x_200; obj* x_203; obj* x_204; 
x_191 = lean::cnstr_get(x_175, 0);
lean::inc(x_191);
lean::dec(x_175);
x_194 = lean::cnstr_get(x_191, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_191, 1);
lean::inc(x_196);
lean::dec(x_191);
x_199 = l_Lean_Elaborator_mkEqns___closed__1;
x_200 = l_Lean_Expr_mkCapp(x_199, x_194);
lean::inc(x_12);
lean::inc(x_2);
x_203 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_2, x_199, x_3, x_11, x_12, x_196);
if (lean::obj_tag(x_4) == 0)
{
obj* x_206; 
x_206 = l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__2;
x_204 = x_206;
goto lbl_205;
}
else
{
obj* x_207; obj* x_209; obj* x_212; 
x_207 = lean::cnstr_get(x_4, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_207, 0);
lean::inc(x_209);
lean::dec(x_207);
x_212 = l_Lean_Elaborator_mangleIdent(x_209);
x_204 = x_212;
goto lbl_205;
}
lbl_205:
{
obj* x_214; 
lean::inc(x_204);
x_214 = lean_expr_local(x_204, x_204, x_164, x_165);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_203) == 0)
{
obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_200);
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_214);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_226 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_228 = x_203;
} else {
 lean::inc(x_226);
 lean::dec(x_203);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_226);
return x_229;
}
else
{
obj* x_230; obj* x_233; obj* x_235; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
x_230 = lean::cnstr_get(x_203, 0);
lean::inc(x_230);
lean::dec(x_203);
x_233 = lean::cnstr_get(x_230, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get(x_230, 1);
lean::inc(x_235);
lean::dec(x_230);
x_238 = l_Lean_Expr_mkCapp(x_199, x_233);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_5);
x_240 = l_Lean_Elaborator_Declaration_elaborate___lambda__3___closed__1;
x_241 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_241, 0, x_240);
lean::cnstr_set(x_241, 1, x_239);
x_242 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_242, 0, x_214);
lean::cnstr_set(x_242, 1, x_241);
x_243 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_243, 0, x_130);
lean::cnstr_set(x_243, 1, x_242);
x_244 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_244, 0, x_200);
lean::cnstr_set(x_244, 1, x_243);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_154);
lean::cnstr_set(x_245, 1, x_244);
x_246 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_246, 0, x_167);
lean::cnstr_set(x_246, 1, x_245);
x_247 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_247, 0, x_159);
lean::cnstr_set(x_247, 1, x_246);
x_248 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_248, 0, x_10);
lean::cnstr_set(x_248, 1, x_247);
x_249 = l_Lean_Expr_mkCapp(x_199, x_248);
x_250 = lean_expr_mk_mdata(x_6, x_249);
x_251 = l_Lean_Elaborator_oldElabCommand(x_2, x_250, x_11, x_12, x_235);
lean::dec(x_2);
return x_251;
}
}
else
{
if (lean::obj_tag(x_203) == 0)
{
obj* x_265; obj* x_267; obj* x_268; 
lean::dec(x_200);
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_130);
lean::dec(x_214);
lean::dec(x_167);
lean::dec(x_154);
lean::dec(x_159);
x_265 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_267 = x_203;
} else {
 lean::inc(x_265);
 lean::dec(x_203);
 x_267 = lean::box(0);
}
if (lean::is_scalar(x_267)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_267;
}
lean::cnstr_set(x_268, 0, x_265);
return x_268;
}
else
{
obj* x_269; obj* x_272; obj* x_275; obj* x_277; obj* x_280; obj* x_283; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
x_269 = lean::cnstr_get(x_203, 0);
lean::inc(x_269);
lean::dec(x_203);
x_272 = lean::cnstr_get(x_4, 0);
lean::inc(x_272);
lean::dec(x_4);
x_275 = lean::cnstr_get(x_269, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_269, 1);
lean::inc(x_277);
lean::dec(x_269);
x_280 = lean::cnstr_get(x_272, 1);
lean::inc(x_280);
lean::dec(x_272);
x_283 = l_Lean_Elaborator_inferModToPexpr(x_280);
lean::dec(x_280);
x_285 = l_Lean_Expr_mkCapp(x_199, x_275);
x_286 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_5);
x_287 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_287, 0, x_283);
lean::cnstr_set(x_287, 1, x_286);
x_288 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_288, 0, x_214);
lean::cnstr_set(x_288, 1, x_287);
x_289 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_289, 0, x_130);
lean::cnstr_set(x_289, 1, x_288);
x_290 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_290, 0, x_200);
lean::cnstr_set(x_290, 1, x_289);
x_291 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_291, 0, x_154);
lean::cnstr_set(x_291, 1, x_290);
x_292 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_292, 0, x_167);
lean::cnstr_set(x_292, 1, x_291);
x_293 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_293, 0, x_159);
lean::cnstr_set(x_293, 1, x_292);
x_294 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_294, 0, x_10);
lean::cnstr_set(x_294, 1, x_293);
x_295 = l_Lean_Expr_mkCapp(x_199, x_294);
x_296 = lean_expr_mk_mdata(x_6, x_295);
x_297 = l_Lean_Elaborator_oldElabCommand(x_2, x_296, x_11, x_12, x_277);
lean::dec(x_2);
return x_297;
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
x_104 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_105 = l_Lean_Elaborator_Declaration_elaborate___closed__2;
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
x_177 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
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
x_222 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
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
x_233 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Elaborator_Declaration_elaborate___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_4);
lean::dec(x_6);
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
lean::dec(x_10);
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
lean::dec(x_11);
return x_14;
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
x_14 = l_Lean_Name_quickLt(x_3, x_7);
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_5);
x_16 = l_Lean_Name_quickLt(x_7, x_3);
lean::dec(x_7);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_11);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_9);
return x_19;
}
else
{
lean::dec(x_9);
x_1 = lean::box(0);
x_2 = x_11;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(x_2, lean::box(0), x_3, x_1);
return x_6;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_variables_elaborate___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::box(0);
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
lean::dec(x_0);
lean::inc(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_2);
x_17 = l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(x_3, x_10, x_1, x_16);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_12, x_18);
lean::dec(x_12);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; 
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
x_21 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_variables_elaborate___spec__4(x_12, x_2, x_20);
x_22 = lean::cnstr_get(x_3, 5);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_3, 6);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_3, 7);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_3, 8);
lean::inc(x_28);
lean::dec(x_3);
x_31 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_6);
lean::cnstr_set(x_31, 2, x_8);
lean::cnstr_set(x_31, 3, x_10);
lean::cnstr_set(x_31, 4, x_21);
lean::cnstr_set(x_31, 5, x_22);
lean::cnstr_set(x_31, 6, x_24);
lean::cnstr_set(x_31, 7, x_26);
lean::cnstr_set(x_31, 8, x_28);
return x_31;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_47; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_59; 
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
x_59 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(x_56, x_55);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_18);
x_61 = lean::box(0);
x_62 = l_Lean_Name_toString___closed__1;
lean::inc(x_55);
x_64 = l_Lean_Name_toStringWithSep___main(x_62, x_55);
x_65 = l_Lean_Parser_Substring_ofString(x_64);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set(x_67, 2, x_55);
lean::cnstr_set(x_67, 3, x_66);
lean::cnstr_set(x_67, 4, x_66);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = l_String_splitAux___main___closed__1;
lean::inc(x_2);
x_72 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_69, x_70, x_1, x_2, x_52);
lean::dec(x_52);
lean::dec(x_69);
if (lean::obj_tag(x_72) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_79 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_81 = x_72;
} else {
 lean::inc(x_79);
 lean::dec(x_72);
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
obj* x_83; obj* x_86; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; 
x_83 = lean::cnstr_get(x_72, 0);
lean::inc(x_83);
lean::dec(x_72);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_88 = x_83;
} else {
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = 0;
x_90 = lean::box(x_89);
if (lean::is_scalar(x_88)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_88;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_86);
x_12 = x_91;
goto lbl_13;
}
}
else
{
obj* x_92; obj* x_95; obj* x_98; obj* x_100; 
x_92 = lean::cnstr_get(x_59, 0);
lean::inc(x_92);
lean::dec(x_59);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
x_98 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1___boxed), 4, 3);
lean::closure_set(x_98, 0, x_95);
lean::closure_set(x_98, 1, x_18);
lean::closure_set(x_98, 2, x_55);
lean::inc(x_2);
x_100 = l_Lean_Elaborator_modifyCurrentScope(x_98, x_1, x_2, x_52);
if (lean::obj_tag(x_100) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_2);
x_105 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_107 = x_100;
} else {
 lean::inc(x_105);
 lean::dec(x_100);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; uint8 x_115; obj* x_116; obj* x_117; 
x_109 = lean::cnstr_get(x_100, 0);
lean::inc(x_109);
lean::dec(x_100);
x_112 = lean::cnstr_get(x_109, 1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_114 = x_109;
} else {
 lean::inc(x_112);
 lean::dec(x_109);
 x_114 = lean::box(0);
}
x_115 = 0;
x_116 = lean::box(x_115);
if (lean::is_scalar(x_114)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_114;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_112);
x_12 = x_117;
goto lbl_13;
}
}
}
}
lbl_13:
{
obj* x_118; obj* x_120; obj* x_123; 
x_118 = lean::cnstr_get(x_12, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_12, 1);
lean::inc(x_120);
lean::dec(x_12);
x_123 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9(x_9, x_1, x_2, x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_118);
x_127 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_129 = x_123;
} else {
 lean::inc(x_127);
 lean::dec(x_123);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_131; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_set(x_123, 0, lean::box(0));
 x_133 = x_123;
} else {
 lean::inc(x_131);
 lean::dec(x_123);
 x_133 = lean::box(0);
}
x_134 = lean::unbox(x_118);
if (x_134 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_7);
lean::dec(x_11);
x_137 = lean::cnstr_get(x_131, 0);
x_139 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_141 = x_131;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_131);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set(x_142, 1, x_139);
if (lean::is_scalar(x_133)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_133;
}
lean::cnstr_set(x_143, 0, x_142);
return x_143;
}
else
{
obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_144 = lean::cnstr_get(x_131, 0);
x_146 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_148 = x_131;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::dec(x_131);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_11;
}
lean::cnstr_set(x_149, 0, x_7);
lean::cnstr_set(x_149, 1, x_144);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
if (lean::is_scalar(x_133)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_133;
}
lean::cnstr_set(x_151, 0, x_150);
return x_151;
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
x_59 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9(x_55, x_1, x_2, x_3);
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
obj* l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9(x_0, x_1, x_2, x_3);
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
x_9 = l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(x_0, x_7, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_registerNotationMacro___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2(x_3, x_0, x_1, x_2);
return x_4;
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
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
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_15, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_15, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_15, 5);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_15, 6);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 7);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
x_43 = l_RBMap_insert___main___at_Lean_Elaborator_registerNotationMacro___spec__1(x_40, x_13, x_21);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::cnstr_get(x_15, 8);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_15, 9);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_15, 10);
lean::inc(x_49);
lean::dec(x_15);
x_52 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_52, 0, x_22);
lean::cnstr_set(x_52, 1, x_24);
lean::cnstr_set(x_52, 2, x_26);
lean::cnstr_set(x_52, 3, x_28);
lean::cnstr_set(x_52, 4, x_30);
lean::cnstr_set(x_52, 5, x_32);
lean::cnstr_set(x_52, 6, x_34);
lean::cnstr_set(x_52, 7, x_44);
lean::cnstr_set(x_52, 8, x_45);
lean::cnstr_set(x_52, 9, x_47);
lean::cnstr_set(x_52, 10, x_49);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_registerNotationMacro___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; 
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
x_12 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__3(x_8, x_0, x_11);
x_13 = lean::cnstr_get(x_1, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 5);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 6);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_1, 7);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 8);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_24, 0, x_2);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_6);
lean::cnstr_set(x_24, 3, x_12);
lean::cnstr_set(x_24, 4, x_13);
lean::cnstr_set(x_24, 5, x_15);
lean::cnstr_set(x_24, 6, x_17);
lean::cnstr_set(x_24, 7, x_19);
lean::cnstr_set(x_24, 8, x_21);
return x_24;
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
obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_33; 
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
x_33 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__4(x_30, x_29);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_36; 
lean::dec(x_0);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_universe_elaborate___lambda__1), 2, 1);
lean::closure_set(x_35, 0, x_29);
x_36 = l_Lean_Elaborator_modifyCurrentScope(x_35, x_1, x_2, x_17);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_37 = x_33;
} else {
 lean::dec(x_33);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_0);
x_39 = l_Lean_Name_toString___closed__1;
x_40 = l_Lean_Name_toStringWithSep___main(x_39, x_29);
x_41 = l_Lean_Elaborator_universe_elaborate___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = l_Lean_Elaborator_universe_elaborate___closed__2;
x_45 = lean::string_append(x_42, x_44);
x_46 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_38, x_45, x_1, x_2, x_17);
lean::dec(x_17);
lean::dec(x_38);
return x_46;
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
obj* x_68; obj* x_71; obj* x_73; obj* x_74; 
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
x_74 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_68, x_1, x_2, x_3);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_71);
lean::dec(x_73);
x_77 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_79 = x_74;
} else {
 lean::inc(x_77);
 lean::dec(x_74);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
return x_80;
}
else
{
obj* x_81; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_81, 0);
x_86 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 x_88 = x_81;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_81);
 x_88 = lean::box(0);
}
x_89 = lean::box(0);
x_90 = lean_expr_mk_const(x_71, x_89);
if (lean::is_scalar(x_73)) {
 x_91 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_91 = x_73;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_84);
if (lean::is_scalar(x_88)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_88;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_86);
if (lean::is_scalar(x_83)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_83;
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
obj* x_4; obj* x_5; obj* x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; 
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
x_18 = l_Lean_Elaborator_attrsToPexpr(x_15, x_1, x_2, x_3);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_24 = x_18;
} else {
 lean::inc(x_22);
 lean::dec(x_18);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
return x_25;
}
else
{
obj* x_26; uint8 x_29; 
x_26 = lean::cnstr_get(x_18, 0);
lean::inc(x_26);
lean::dec(x_18);
x_29 = 0;
x_10 = x_29;
x_11 = x_26;
goto lbl_12;
}
}
else
{
lean::dec(x_13);
if (lean::obj_tag(x_18) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_36 = x_18;
} else {
 lean::inc(x_34);
 lean::dec(x_18);
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
obj* x_38; uint8 x_41; 
x_38 = lean::cnstr_get(x_18, 0);
lean::inc(x_38);
lean::dec(x_18);
x_41 = 1;
x_10 = x_41;
x_11 = x_38;
goto lbl_12;
}
}
lbl_12:
{
obj* x_42; obj* x_44; obj* x_47; obj* x_51; 
x_42 = lean::cnstr_get(x_11, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_11, 1);
lean::inc(x_44);
lean::dec(x_11);
x_47 = lean::cnstr_get(x_9, 5);
lean::inc(x_47);
lean::dec(x_9);
lean::inc(x_2);
x_51 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_47, x_1, x_2, x_44);
if (lean::obj_tag(x_51) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_42);
x_55 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_57 = x_51;
} else {
 lean::inc(x_55);
 lean::dec(x_51);
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
obj* x_59; obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_59 = lean::cnstr_get(x_51, 0);
lean::inc(x_59);
lean::dec(x_51);
x_62 = lean::cnstr_get(x_59, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
lean::dec(x_59);
x_67 = l_Lean_Elaborator_attribute_elaborate___closed__1;
x_68 = l_Lean_Elaborator_attribute_elaborate___closed__2;
x_69 = l_Lean_KVMap_setBool(x_67, x_68, x_10);
x_70 = l_Lean_Elaborator_mkEqns___closed__1;
x_71 = l_Lean_Expr_mkCapp(x_70, x_62);
x_72 = lean_expr_mk_app(x_42, x_71);
x_73 = lean_expr_mk_mdata(x_69, x_72);
x_74 = l_Lean_Elaborator_oldElabCommand(x_0, x_73, x_1, x_2, x_64);
lean::dec(x_0);
return x_74;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_14 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Name_quickLt(x_2, x_10);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = l_Lean_Name_quickLt(x_10, x_2);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_12);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_2);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_7);
x_22 = x_21;
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_14, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_7);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_8, x_2, x_3);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_10);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
lean::cnstr_set_scalar(x_27, sizeof(void*)*4, x_7);
x_28 = x_27;
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 1);
x_33 = lean::cnstr_get(x_1, 2);
x_35 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_37 = x_1;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Name_quickLt(x_2, x_31);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = l_Lean_Name_quickLt(x_31, x_2);
if (x_39 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_33);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_3);
lean::cnstr_set(x_42, 3, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_7);
x_43 = x_42;
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___main___rarg(x_35);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_37;
}
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_31);
lean::cnstr_set(x_46, 2, x_33);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_7);
x_47 = x_46;
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_31);
lean::cnstr_set(x_49, 2, x_33);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_7);
x_50 = x_49;
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_35, x_2, x_3);
x_52 = l_RBNode_balance2___main___rarg(x_50, x_51);
return x_52;
}
}
}
else
{
uint8 x_53; 
x_53 = l_RBNode_isRed___main___rarg(x_29);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_29, x_2, x_3);
if (lean::is_scalar(x_37)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_37;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_33);
lean::cnstr_set(x_55, 3, x_35);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_7);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_37;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_33);
lean::cnstr_set(x_58, 3, x_35);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_7);
x_59 = x_58;
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(x_0, x_1, x_8, x_10);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
}
}
obj* l_RBMap_fromList___at_Lean_Elaborator_elaborators___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Elaborator_elaborators() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
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
x_30 = l_Lean_Parser_command_Declaration;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate), 4, 0);
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
x_73 = l_RBMap_fromList___at_Lean_Elaborator_elaborators___spec__1(x_72);
return x_73;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
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
x_22 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(x_20, x_0);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_27; 
x_23 = lean::cnstr_get(x_15, 6);
lean::inc(x_23);
x_25 = lean::box(0);
lean::inc(x_0);
x_27 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__1(x_0, x_3, x_23, x_25);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_45; obj* x_46; 
x_28 = l_Lean_Elaborator_resolveContext___main___closed__1;
x_29 = lean::box(0);
lean::inc(x_0);
x_31 = l_Lean_Name_replacePrefix___main(x_0, x_28, x_29);
x_32 = lean::cnstr_get(x_3, 8);
lean::inc(x_32);
x_34 = lean_environment_contains(x_32, x_31);
x_35 = lean::cnstr_get(x_15, 7);
lean::inc(x_35);
lean::inc(x_0);
x_38 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__2(x_0, x_35);
x_39 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__3(x_32, x_38, x_25);
x_40 = lean::cnstr_get(x_3, 3);
lean::inc(x_40);
lean::dec(x_3);
x_43 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__4(x_15, x_40, x_25);
lean::dec(x_15);
x_45 = l_List_filterMap___main___at_Lean_Elaborator_resolveContext___main___spec__5(x_0, x_43);
x_46 = l_List_filterAux___main___at_Lean_Elaborator_resolveContext___main___spec__6(x_32, x_45, x_25);
lean::dec(x_32);
if (x_34 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_31);
x_49 = l_List_append___rarg(x_27, x_39);
x_50 = l_List_append___rarg(x_49, x_46);
if (lean::is_scalar(x_19)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_19;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_14;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_31);
lean::cnstr_set(x_53, 1, x_27);
x_54 = l_List_append___rarg(x_53, x_39);
x_55 = l_List_append___rarg(x_54, x_46);
if (lean::is_scalar(x_19)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_19;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_14;
}
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
else
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_3);
lean::dec(x_15);
x_60 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 1);
 x_62 = x_27;
} else {
 lean::inc(x_60);
 lean::dec(x_27);
 x_62 = lean::box(0);
}
x_63 = l_Lean_Name_append___main(x_60, x_0);
lean::dec(x_60);
if (lean::is_scalar(x_62)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_62;
}
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_25);
if (lean::is_scalar(x_19)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_19;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_14;
}
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
}
else
{
obj* x_72; obj* x_75; obj* x_77; obj* x_78; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
lean::dec(x_19);
x_72 = lean::cnstr_get(x_22, 0);
lean::inc(x_72);
lean::dec(x_22);
x_75 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_77 = x_72;
} else {
 lean::inc(x_75);
 lean::dec(x_72);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_81);
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_84 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_84 = x_14;
}
lean::cnstr_set(x_84, 0, x_83);
return x_84;
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
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
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
lean::inc(x_24);
x_26 = lean::cnstr_get(x_4, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_4, 2);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_4, 3);
lean::inc(x_30);
x_32 = l_List_append___rarg(x_19, x_30);
x_33 = lean::cnstr_get(x_4, 4);
lean::inc(x_33);
lean::dec(x_4);
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_24);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_28);
lean::cnstr_set(x_36, 3, x_32);
lean::cnstr_set(x_36, 4, x_33);
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
obj* x_40; obj* x_42; obj* x_43; obj* x_45; 
x_40 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
x_45 = l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(x_43, x_1, x_2, x_3);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_40);
lean::dec(x_42);
x_48 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_50 = x_45;
} else {
 lean::inc(x_48);
 lean::dec(x_45);
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
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_52 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_54 = x_45;
} else {
 lean::inc(x_52);
 lean::dec(x_45);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_52, 0);
x_57 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_59 = x_52;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_52);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_40, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_40, 2);
lean::inc(x_62);
lean::dec(x_40);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_60);
lean::cnstr_set(x_65, 1, x_55);
lean::cnstr_set(x_65, 2, x_62);
if (lean::is_scalar(x_42)) {
 x_66 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_66 = x_42;
}
lean::cnstr_set(x_66, 0, x_65);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_57);
if (lean::is_scalar(x_54)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_54;
}
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
}
default:
{
obj* x_70; obj* x_71; 
lean::dec(x_2);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_0);
lean::cnstr_set(x_70, 1, x_3);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
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
obj* _init_l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* _init_l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
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
obj* x_0; 
x_0 = l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1;
return x_0;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__4() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2;
return x_0;
}
}
obj* _init_l_Lean_Elaborator_mkState___closed__5() {
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::box(0);
x_4 = lean::box(0);
x_5 = l_Lean_Elaborator_mkState___closed__1;
x_6 = l_Lean_Elaborator_mkState___closed__2;
x_7 = l_Lean_Elaborator_mkState___closed__3;
x_8 = l_Lean_Elaborator_mkState___closed__4;
x_9 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
lean::cnstr_set(x_9, 5, x_4);
lean::cnstr_set(x_9, 6, x_3);
lean::cnstr_set(x_9, 7, x_3);
lean::cnstr_set(x_9, 8, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_Lean_Expander_builtinTransformers;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Lean_MessageLog_empty;
x_20 = l_Lean_Elaborator_mkState___closed__5;
x_21 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_21, 0, x_3);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_18);
lean::cnstr_set(x_21, 3, x_3);
lean::cnstr_set(x_21, 4, x_10);
lean::cnstr_set(x_21, 5, x_19);
lean::cnstr_set(x_21, 6, x_11);
lean::cnstr_set(x_21, 7, x_17);
lean::cnstr_set(x_21, 8, x_1);
lean::cnstr_set(x_21, 9, x_20);
lean::cnstr_set(x_21, 10, x_18);
return x_21;
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
obj* l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
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
x_25 = l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3(x_24, x_21);
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
obj* l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3(x_0, x_1);
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
 l_Lean_Elaborator_OrderedRBMap_empty___closed__1 = _init_l_Lean_Elaborator_OrderedRBMap_empty___closed__1();
lean::mark_persistent(l_Lean_Elaborator_OrderedRBMap_empty___closed__1);
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
 l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1 = _init_l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1();
lean::mark_persistent(l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1);
 l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1 = _init_l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1();
lean::mark_persistent(l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1);
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
 l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1);
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
 l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1 = _init_l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1();
lean::mark_persistent(l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1);
 l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2 = _init_l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2();
lean::mark_persistent(l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2);
 l_Lean_Elaborator_mkState___closed__1 = _init_l_Lean_Elaborator_mkState___closed__1();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__1);
 l_Lean_Elaborator_mkState___closed__2 = _init_l_Lean_Elaborator_mkState___closed__2();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__2);
 l_Lean_Elaborator_mkState___closed__3 = _init_l_Lean_Elaborator_mkState___closed__3();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__3);
 l_Lean_Elaborator_mkState___closed__4 = _init_l_Lean_Elaborator_mkState___closed__4();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__4);
 l_Lean_Elaborator_mkState___closed__5 = _init_l_Lean_Elaborator_mkState___closed__5();
lean::mark_persistent(l_Lean_Elaborator_mkState___closed__5);
 l_Lean_Elaborator_processCommand___lambda__1___closed__1 = _init_l_Lean_Elaborator_processCommand___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__1___closed__1);
 l_Lean_Elaborator_processCommand___lambda__1___closed__2 = _init_l_Lean_Elaborator_processCommand___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__1___closed__2);
 l_Lean_Elaborator_processCommand___closed__1 = _init_l_Lean_Elaborator_processCommand___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___closed__1);
return w;
}
