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
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__19(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_currentScope___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_variables_elaborate___spec__5(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_getOptType___main(obj*);
obj* l_Option_toMonad___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__1(obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__2;
obj* l_Lean_Elaborator_notation_elaborate(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_postprocessNotationSpec___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__20(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__2;
obj* l_Lean_Elaborator_include_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_precToNat(obj*);
obj* l_Lean_Parser_stringLit_View_value(obj*);
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__11(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_zipWith___main___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Expander_getOptType___main___closed__1;
obj* l_Lean_Elaborator_dummy;
obj* l_Lean_Elaborator_toPexpr___main___closed__8;
extern obj* l_Lean_MessageLog_empty;
obj* l_Lean_Elaborator_toPexpr___main___closed__46;
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__7(obj*);
obj* l_Lean_KVMap_setBool(obj*, obj*, uint8);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7___boxed(obj*);
uint8 l_List_foldr___main___at_Lean_Elaborator_matchOpenSpec___spec__1(obj*, uint8, obj*);
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1(obj*, uint8, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__3;
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__1;
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_mkState___spec__2;
obj* l_id___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__2(obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__1;
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9(obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg___closed__1;
obj* l_Lean_Elaborator_ElaboratorM_MonadExcept;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__6;
obj* l_Lean_Elaborator_toPexpr___main___closed__21;
obj* l_Lean_Elaborator_matchSpec(obj*, obj*);
obj* l_List_mmap_x_27___main___at_Lean_Elaborator_noKind_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_matchOpenSpec(obj*, obj*);
uint8 l_Option_isSome___main___rarg(obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__4(obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__3;
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1___closed__1;
extern obj* l_Lean_Parser_command_namespace;
extern obj* l_Lean_Parser_Level_trailing_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_lengthAux___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView_x_27___lambda__1___closed__5;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5(obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__2___closed__1;
obj* l_RBMap_insert___main___at_Lean_Elaborator_elaborators___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_CommandParserConfig_registerNotationTokens___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_identUnivParamsToPexpr(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___rarg(obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__11(obj*);
extern obj* l_Lean_Parser_Module_header;
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__22;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_ElaboratorM_MonadState;
obj* l_Lean_Elaborator_elaborators;
obj* l_StateT_Monad___rarg(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__13(obj*, obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_processCommand___spec__3(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___closed__1;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_section_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_variables_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_reserveNotation_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_processCommand___lambda__2(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Syntax_reprintLst___main___closed__1;
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
obj* l_Lean_Elaborator_resolveContext___main___lambda__2___boxed(obj*, obj*);
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__31;
extern obj* l_Lean_Parser_Term_structInst_HasView;
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___closed__1;
obj* l_List_map___main___at_Lean_Elaborator_namesToPexpr___spec__1(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_toList___rarg(obj*);
obj* l_Lean_Elaborator_mkNotationKind(obj*, obj*);
obj* l_Lean_Elaborator_command_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__34;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_export_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__45;
obj* l_Lean_Elaborator_toLevel___main___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__9(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__1;
obj* l_Lean_Elaborator_mkState___closed__4;
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18___boxed(obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14(obj*, obj*, obj*, obj*);
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_Lean_Elaborator_export_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_section;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__14;
obj* l_ExceptT_MonadExcept___rarg(obj*);
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_attribute_HasView;
obj* l_Lean_Elaborator_toPexpr___main___closed__32;
extern obj* l_Lean_Parser_command_reserveNotation_HasView;
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_export_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__15___boxed(obj*);
obj* l_Lean_Elaborator_resolveContext___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_inferModToPexpr___closed__1;
obj* l_Lean_Elaborator_notation_elaborateAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_insert___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_binderIdent_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__47;
obj* l_Lean_Elaborator_toPexpr___main___closed__18;
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__6;
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__10;
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l_Lean_Elaborator_include_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_toPexpr___main___lambda__1(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__44;
obj* l_id_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelAdd___main(obj*, obj*);
extern obj* l_Lean_Parser_command_end_HasView;
obj* l_Lean_Elaborator_attribute_elaborate___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__10(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__13(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elaborators___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_attribute_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__4;
obj* l_Lean_Elaborator_OrderedRBMap_insert(obj*, obj*, obj*);
obj* l_fix1___rarg___lambda__1___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_end;
extern obj* l_Lean_Parser_Term_sort_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Elaborator_toPexpr___main___closed__27;
obj* l_ReaderT_lift___rarg___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_preresolve___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_Module_header_elaborate(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toLevel___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* level_mk_param(obj*);
obj* l_Lean_Elaborator_processCommand___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
extern obj* l_Lean_Parser_command_export;
obj* l_Lean_Elaborator_end_elaborate___closed__4;
obj* l_Lean_Elaborator_mangleIdent(obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___lambda__1(obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__6(obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_isOpenNamespace___main(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
extern obj* l_Lean_Expander_error___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9___boxed(obj*, obj*);
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
obj* l_Lean_Elaborator_notation_elaborateAux___lambda__1(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__7(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__2;
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_registerNotationMacro(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__20;
extern obj* l_Lean_Parser_command_initQuot;
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__48;
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
obj* l_Lean_Elaborator_matchSpec___closed__1;
extern obj* l_Lean_Parser_command_open_HasView;
obj* l_Lean_Elaborator_inferModToPexpr___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_check;
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_elaborators___spec__5___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_explicit_HasView;
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__17;
obj* l_Lean_Elaborator_processCommand___lambda__2___closed__2;
obj* l_RBNode_insert___at_Lean_Elaborator_oldElabCommand___spec__19___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__16___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7___boxed(obj*, obj*, obj*, obj*);
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
obj* l_Lean_Elaborator_mkEqns___closed__1;
obj* l_RBNode_insert___at_Lean_Elaborator_elaborators___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
extern obj* l_Lean_Expander_builtinTransformers;
obj* l_List_mfilter___main___at_Lean_Elaborator_variables_elaborate___spec__9___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___boxed(obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__21(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__4;
extern obj* l_Char_HasRepr___closed__1;
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
obj* l_Lean_Elaborator_toPexpr___main___lambda__2___boxed(obj*);
obj* l_Lean_Elaborator_oldElabCommand___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__3;
obj* l_Lean_Elaborator_isOpenNamespace___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Module_header_HasView;
extern obj* l_Lean_Parser_command_setOption;
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__5(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__14(obj*);
obj* l_Lean_Elaborator_matchPrecedence___main___boxed(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_oldElabCommand___spec__8___boxed(obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Module_eoi;
obj* l_Lean_Elaborator_attrsToPexpr(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4___boxed(obj*, obj*);
obj* l_Lean_Elaborator_elaborateCommand___boxed(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
obj* l_Lean_Elaborator_toPexpr___main___lambda__1___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2(obj*);
obj* l_Lean_Elaborator_setOption_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_noKind_elaborate___closed__1;
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15___boxed(obj*, obj*);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(obj*);
extern obj* l_Lean_Parser_command_Declaration;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_Term_sortApp_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_trailing_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Elaborator_OrderedRBMap_find(obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___lambda__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4___boxed(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(obj*, obj*, obj*, obj*);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_open;
obj* l_Lean_Elaborator_OrderedRBMap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate(obj*, obj*, obj*, obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_notation_HasView;
obj* l_RBMap_fromList___at_Lean_Elaborator_elaborators___spec__1(obj*);
extern obj* l_Lean_Parser_command_section_HasView;
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__12(obj*);
obj* l_Lean_Elaborator_levelAdd___main___boxed(obj*, obj*);
uint8 l_Lean_Elaborator_resolveContext___main___lambda__1(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_app_HasView;
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6(obj*, obj*, obj*, obj*);
obj* l_coe___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__10(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__20(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate___lambda__1(obj*, obj*);
uint8 l_Lean_Elaborator_matchPrecedence(obj*, obj*);
obj* l_Lean_Elaborator_toLevel___main___closed__2;
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_projection_HasView;
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_simpleBindersToPexpr___spec__1___boxed(obj*, obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_maxPrec;
extern "C" obj* lean_expr_mk_bvar(obj*);
extern "C" obj* lean_elaborator_elaborate_command(obj*, obj*, obj*);
obj* l_Lean_Elaborator_setOption_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_open_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__18(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__5;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__50;
obj* l_RBMap_insert___main___at_Lean_Elaborator_registerNotationMacro___spec__1(obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Elaborator_updateParserConfig___spec__2(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_sortApp_HasView;
obj* l_Lean_Elaborator_mkNotationKind___boxed(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkEqns(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_resolveContext___main___lambda__3(obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_isOpenNamespace___boxed(obj*, obj*);
obj* l_String_trim(obj*);
extern obj* l_Lean_Parser_command_universe;
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8___boxed(obj*, obj*, obj*, obj*);
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(obj*, obj*);
extern obj* l_Lean_Parser_command_namespace_HasView;
obj* l_Lean_Elaborator_setOption_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_variables_elaborate___spec__2___boxed(obj*, obj*, obj*);
obj* l_List_filterMap___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___closed__1;
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_variables_elaborate___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_levelGetAppArgs___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_namespace_elaborate___closed__1;
obj* l_Lean_Elaborator_mkState___closed__1;
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope___closed__1;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(obj*, obj*);
obj* l_List_filter___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_oldElabCommand___spec__7(obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__3(obj*);
obj* l_Lean_Elaborator_getNamespace___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_universe_HasView;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_variables_elaborate___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_simpleBindersToPexpr(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Elaborator_OrderedRBMap_find___spec__2___boxed(obj*, obj*);
uint8 l_Lean_Elaborator_resolveContext___main___lambda__2(obj*, obj*);
obj* l_Lean_Elaborator_declModifiersToPexpr___closed__5;
obj* l_Lean_Elaborator_levelGetAppArgs___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_oldElabCommand___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_anonymousConstructor_HasView;
obj* l_Lean_Elaborator_end_elaborate(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__5(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig(obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_OrderedRBMap_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__4;
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_oldElabCommand___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__5;
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__4(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_empty___at_Lean_Elaborator_OrderedRBMap_ofList___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__24;
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__5___boxed(obj*, obj*, obj*, obj*);
uint8 l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1(obj*, obj*);
obj* l_Lean_Elaborator_initQuot_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_Lean_environment_contains___boxed(obj*, obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_OrderedRBMap_insert___spec__4(obj*, obj*, obj*);
obj* l_id_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_variables_elaborate___spec__4(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_Elaborator_variables_elaborate___spec__6___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Elaborator_toPexpr___main___lambda__2(obj*);
extern obj* l_Lean_Parser_Term_borrowed_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__26;
obj* l_List_span___main___rarg(obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_oldElabCommand___spec__11(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_Lean_Elaborator_eoi_elaborate___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(obj*, obj*, obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser___closed__1;
obj* l_Lean_Parser_RecT_recurse___rarg(obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___lambda__1(obj*, obj*);
obj* l_Lean_Elaborator_elabDefLike___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" uint8 lean_environment_contains(obj*, obj*);
obj* l_ExceptT_Monad___rarg(obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
obj* l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__6(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(obj*, obj*);
obj* l_Lean_Elaborator_preresolve___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__2(obj*);
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__38;
extern obj* l_Lean_Parser_command_check_HasView;
obj* l_id_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_variables_elaborate___closed__2;
obj* l_Lean_Elaborator_processCommand___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_insertCore___main(obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__16;
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__22(obj*, obj*);
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__35;
obj* l_Lean_Elaborator_toPexpr___main___closed__7;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Elaborator_Module_header_elaborate___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Elaborator_declModifiersToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__6(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21___boxed(obj*, obj*, obj*, obj*);
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
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__2___closed__5;
obj* l_id_bind___boxed(obj*, obj*);
obj* l_Lean_Elaborator_variables_elaborate___closed__1;
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_oldElabCommand___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_modifyCurrentScope(obj*, obj*, obj*, obj*);
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
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__2(obj*, obj*);
extern obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Elaborator_toLevel___main(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1;
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
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__3(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_attrsToPexpr___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkNotationKind___rarg(obj*);
obj* l_Lean_Elaborator_elaboratorConfigCoeFrontendConfig___boxed(obj*);
obj* l_Lean_Expr_local___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_RBMap_insert___main___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_preresolve___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___closed__1;
obj* l_Lean_Elaborator_toPexpr___main___closed__49;
extern obj* l_Lean_Parser_command_Declaration_HasView;
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__3(obj*);
extern obj* l_Lean_Expander_noExpansion___closed__1;
extern obj* l_Lean_Parser_Term_sort_HasView;
obj* l_Lean_Elaborator_resolveContext(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__23;
obj* l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1___closed__1;
obj* l_ReaderT_lift___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Elaborator_Declaration_elaborate___closed__2;
obj* l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborate___closed__2;
extern obj* l_Lean_Parser_command_reserveNotation;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Elaborator_check_elaborate___closed__1;
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__9(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Elaborator_notation_elaborate___spec__1___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_OrderedRBMap_ofList___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__9___closed__1;
uint8 l_Lean_Elaborator_matchPrecedence___main(obj*, obj*);
obj* l_Lean_Elaborator_attrsToPexpr___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_mkState___closed__2;
obj* l_Lean_Elaborator_initQuot_elaborate___closed__1;
obj* l_Lean_Parser_Syntax_toFormat___main(obj*);
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2;
obj* l_StateT_MonadState___rarg(obj*);
obj* l_List_decidableMem___main___at_Lean_Elaborator_isOpenNamespace___main___spec__1___boxed(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_universe_elaborate(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_CommandParserConfig_registerNotationParser(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_notation_elaborateAux___closed__1;
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_getNamespace(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_let_HasView;
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_toNat___main(obj*);
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_Parser_Term_binders_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Elaborator_registerNotationMacro___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_pi_HasView;
obj* l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elaborator_OrderedRBMap_ofList___at_Lean_Elaborator_oldElabCommand___spec__1___closed__1;
obj* l_List_mmap___main___at_Lean_Elaborator_matchSpec___spec__1(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__42;
obj* l_Lean_Elaborator_toPexpr___main___closed__15;
obj* l_Lean_Elaborator_postprocessNotationSpec(obj*);
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__5(obj*, obj*, obj*, obj*);
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
x_11 = l_ExceptT_Monad___rarg(x_9);
x_12 = l_ExceptT_MonadExcept___rarg(x_9);
x_13 = l_StateT_MonadExcept___rarg(x_11, lean::box(0), x_12);
x_14 = l_ReaderT_MonadExcept___rarg(x_13);
x_15 = l_ReaderT_MonadExcept___rarg(x_14);
return x_15;
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
x_14 = l_Lean_Expander_error___rarg___lambda__1___closed__1;
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
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_Lean_Parser_Syntax_getPos(x_21);
x_23 = lean::mk_nat_obj(0ul);
x_24 = l_Option_getOrElse___main___rarg(x_22, x_23);
lean::dec(x_22);
x_26 = l_Lean_FileMap_toPosition(x_10, x_24);
x_27 = 2;
x_28 = l_String_splitAux___main___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_1);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
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
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_30 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_10, x_1, x_2, x_27);
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
x_9 = level_mk_imax(x_3, x_8);
return x_9;
}
}
}
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::box(0);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7(x_2, lean::box(0), x_3, x_1);
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
x_223 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_204, x_1, x_2, x_220);
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
x_237 = l_List_foldr___main___at_Lean_Elaborator_toLevel___main___spec__4(x_218, x_232);
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
x_295 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5(x_292, x_291);
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
obj* l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toLevel___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_Lean_Elaborator_toLevel___main___spec__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_Lean_Elaborator_toLevel___main___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5(x_0, x_1);
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_10, x_1, x_2, x_30);
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
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("field");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("toPexpr: unreachable");
return x_0;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_0, x_15, x_2, x_3, x_39);
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
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1;
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
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_0, x_70, x_2, x_3, x_93);
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_16, x_2, x_3, x_39);
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
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_66, x_2, x_3, x_89);
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
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_110, x_2, x_3, x_131);
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_15, x_2, x_3, x_39);
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
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1;
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
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_70, x_2, x_3, x_93);
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1;
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
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
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
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_16, x_2, x_3, x_39);
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
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_66, x_2, x_3, x_89);
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
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_110, x_2, x_3, x_131);
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_15, x_2, x_3, x_39);
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
x_63 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1;
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
x_75 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_96 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_70, x_2, x_3, x_93);
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_21 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_42 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_16, x_2, x_3, x_39);
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
x_71 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
x_92 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_66, x_2, x_3, x_89);
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
x_134 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_110, x_2, x_3, x_131);
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(obj* x_0, obj* x_1) {
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
x_8 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(x_0, x_5);
x_9 = lean_expr_mk_app(x_3, x_8);
return x_9;
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__19(obj* x_0) {
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
x_10 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__19(x_4);
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
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__20(obj* x_0, obj* x_1) {
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_30 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(x_10, x_1, x_2, x_27);
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
obj* l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__22(obj* x_0, obj* x_1) {
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
uint8 l_Lean_Elaborator_toPexpr___main___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
uint8 l_Lean_Elaborator_toPexpr___main___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_3, 1);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
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
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toPexpr___main___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__24() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_toPexpr___main___lambda__2___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__25() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure instance");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("catchall");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__27() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean_expr_mk_sort(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__28() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("struct");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__29() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = l_Option_getOrElse___main___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__30() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__31() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__33() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("NOTAString");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrowed");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__35() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__36() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__37() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("fieldNotation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__38() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__39() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean_expr_mk_bvar(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_Option_getOrElse___main___rarg(x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__44() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_dummy;
x_2 = lean_expr_mk_mvar(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__45() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymousConstructor");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__46() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__47() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed pi");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__48() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed lambda");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__49() {
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
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__50() {
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
x_174 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_170, x_1, x_2, x_161);
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
x_200 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2;
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
obj* x_205; obj* x_206; obj* x_210; obj* x_211; obj* x_213; obj* x_214; obj* x_215; obj* x_217; obj* x_220; obj* x_221; obj* x_222; 
x_205 = l_Lean_Parser_Term_structInst_HasView;
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
lean::dec(x_205);
lean::inc(x_0);
x_210 = lean::apply_1(x_206, x_0);
x_211 = lean::cnstr_get(x_210, 3);
lean::inc(x_211);
x_213 = l_Lean_Elaborator_toPexpr___main___closed__23;
x_214 = l_List_span___main___rarg(x_213, x_211);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
x_220 = l_Lean_Elaborator_toPexpr___main___closed__24;
x_221 = l_List_span___main___rarg(x_220, x_217);
x_222 = lean::cnstr_get(x_221, 1);
lean::inc(x_222);
if (lean::obj_tag(x_222) == 0)
{
obj* x_224; obj* x_229; 
x_224 = lean::cnstr_get(x_221, 0);
lean::inc(x_224);
lean::dec(x_221);
lean::inc(x_2);
lean::inc(x_0);
x_229 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_0, x_215, x_1, x_2, x_3);
if (lean::obj_tag(x_229) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_224);
lean::dec(x_210);
x_235 = lean::cnstr_get(x_229, 0);
if (lean::is_exclusive(x_229)) {
 x_237 = x_229;
} else {
 lean::inc(x_235);
 lean::dec(x_229);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_235);
return x_238;
}
else
{
obj* x_239; obj* x_242; obj* x_244; obj* x_247; obj* x_251; 
x_239 = lean::cnstr_get(x_229, 0);
lean::inc(x_239);
lean::dec(x_229);
x_242 = lean::cnstr_get(x_239, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_239, 1);
lean::inc(x_244);
lean::dec(x_239);
lean::inc(x_2);
lean::inc(x_0);
x_251 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_224, x_1, x_2, x_244);
if (lean::obj_tag(x_251) == 0)
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_242);
lean::dec(x_210);
x_257 = lean::cnstr_get(x_251, 0);
if (lean::is_exclusive(x_251)) {
 x_259 = x_251;
} else {
 lean::inc(x_257);
 lean::dec(x_251);
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
x_261 = lean::cnstr_get(x_251, 0);
lean::inc(x_261);
lean::dec(x_251);
x_264 = lean::cnstr_get(x_210, 2);
lean::inc(x_264);
if (lean::obj_tag(x_264) == 0)
{
obj* x_266; obj* x_268; obj* x_270; obj* x_271; 
x_266 = lean::cnstr_get(x_261, 0);
x_268 = lean::cnstr_get(x_261, 1);
if (lean::is_exclusive(x_261)) {
 x_270 = x_261;
} else {
 lean::inc(x_266);
 lean::inc(x_268);
 lean::dec(x_261);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_266);
lean::cnstr_set(x_271, 1, x_268);
x_247 = x_271;
goto lbl_248;
}
else
{
obj* x_272; obj* x_274; obj* x_277; obj* x_280; obj* x_284; 
x_272 = lean::cnstr_get(x_261, 0);
lean::inc(x_272);
x_274 = lean::cnstr_get(x_261, 1);
lean::inc(x_274);
lean::dec(x_261);
x_277 = lean::cnstr_get(x_264, 0);
lean::inc(x_277);
lean::dec(x_264);
x_280 = lean::cnstr_get(x_277, 0);
lean::inc(x_280);
lean::dec(x_277);
lean::inc(x_2);
x_284 = l_Lean_Elaborator_toPexpr___main(x_280, x_1, x_2, x_274);
if (lean::obj_tag(x_284) == 0)
{
obj* x_291; obj* x_293; obj* x_294; 
lean::dec(x_272);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_242);
lean::dec(x_210);
x_291 = lean::cnstr_get(x_284, 0);
if (lean::is_exclusive(x_284)) {
 x_293 = x_284;
} else {
 lean::inc(x_291);
 lean::dec(x_284);
 x_293 = lean::box(0);
}
if (lean::is_scalar(x_293)) {
 x_294 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_294 = x_293;
}
lean::cnstr_set(x_294, 0, x_291);
return x_294;
}
else
{
obj* x_295; obj* x_298; obj* x_300; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
x_295 = lean::cnstr_get(x_284, 0);
lean::inc(x_295);
lean::dec(x_284);
x_298 = lean::cnstr_get(x_295, 0);
x_300 = lean::cnstr_get(x_295, 1);
if (lean::is_exclusive(x_295)) {
 x_302 = x_295;
} else {
 lean::inc(x_298);
 lean::inc(x_300);
 lean::dec(x_295);
 x_302 = lean::box(0);
}
x_303 = lean::box(0);
x_304 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_304, 0, x_298);
lean::cnstr_set(x_304, 1, x_303);
x_305 = l_List_append___rarg(x_272, x_304);
if (lean::is_scalar(x_302)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_302;
}
lean::cnstr_set(x_306, 0, x_305);
lean::cnstr_set(x_306, 1, x_300);
x_247 = x_306;
goto lbl_248;
}
}
}
lbl_248:
{
obj* x_307; obj* x_309; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; uint8 x_318; obj* x_319; obj* x_320; obj* x_323; obj* x_324; obj* x_325; 
x_307 = lean::cnstr_get(x_247, 0);
x_309 = lean::cnstr_get(x_247, 1);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_set(x_247, 0, lean::box(0));
 lean::cnstr_set(x_247, 1, lean::box(0));
 x_311 = x_247;
} else {
 lean::inc(x_307);
 lean::inc(x_309);
 lean::dec(x_247);
 x_311 = lean::box(0);
}
x_312 = lean::mk_nat_obj(0ul);
x_313 = l_List_lengthAux___main___rarg(x_242, x_312);
x_314 = lean::box(0);
x_315 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_316 = l_Lean_KVMap_setNat(x_314, x_315, x_313);
x_317 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_318 = 0;
x_319 = l_Lean_KVMap_setBool(x_316, x_317, x_318);
x_320 = lean::cnstr_get(x_210, 1);
lean::inc(x_320);
lean::dec(x_210);
x_323 = l_List_append___rarg(x_242, x_307);
x_324 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_325 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_324, x_323);
if (lean::obj_tag(x_320) == 0)
{
obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
x_326 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_327 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_328 = l_Lean_KVMap_setName(x_319, x_326, x_327);
x_329 = lean_expr_mk_mdata(x_328, x_325);
if (lean::is_scalar(x_311)) {
 x_330 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_330 = x_311;
}
lean::cnstr_set(x_330, 0, x_329);
lean::cnstr_set(x_330, 1, x_309);
x_15 = x_330;
goto lbl_16;
}
else
{
obj* x_331; obj* x_333; obj* x_334; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
x_331 = lean::cnstr_get(x_320, 0);
if (lean::is_exclusive(x_320)) {
 x_333 = x_320;
} else {
 lean::inc(x_331);
 lean::dec(x_320);
 x_333 = lean::box(0);
}
x_334 = lean::cnstr_get(x_331, 0);
lean::inc(x_334);
lean::dec(x_331);
x_337 = l_Lean_Elaborator_mangleIdent(x_334);
if (lean::is_scalar(x_333)) {
 x_338 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_338 = x_333;
}
lean::cnstr_set(x_338, 0, x_337);
x_339 = lean::box(0);
x_340 = l_Option_getOrElse___main___rarg(x_338, x_339);
lean::dec(x_338);
x_342 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_343 = l_Lean_KVMap_setName(x_319, x_342, x_340);
x_344 = lean_expr_mk_mdata(x_343, x_325);
if (lean::is_scalar(x_311)) {
 x_345 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_345 = x_311;
}
lean::cnstr_set(x_345, 0, x_344);
lean::cnstr_set(x_345, 1, x_309);
x_15 = x_345;
goto lbl_16;
}
}
}
}
else
{
obj* x_346; obj* x_348; 
x_346 = lean::cnstr_get(x_222, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_346, 0);
lean::inc(x_348);
lean::dec(x_346);
if (lean::obj_tag(x_348) == 0)
{
obj* x_351; obj* x_352; obj* x_355; obj* x_356; obj* x_359; obj* x_360; obj* x_361; obj* x_363; 
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 lean::cnstr_release(x_222, 1);
 x_351 = x_222;
} else {
 lean::dec(x_222);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_221, 0);
lean::inc(x_352);
lean::dec(x_221);
x_355 = l_Lean_Parser_Term_structInstItem_HasView;
x_356 = lean::cnstr_get(x_355, 1);
lean::inc(x_356);
lean::dec(x_355);
x_359 = lean::apply_1(x_356, x_348);
x_360 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_360, 0, x_359);
x_361 = l_Lean_Elaborator_toPexpr___main___closed__30;
lean::inc(x_2);
x_363 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_360, x_361, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_360);
if (lean::obj_tag(x_363) == 0)
{
obj* x_373; obj* x_375; obj* x_376; 
lean::dec(x_351);
lean::dec(x_352);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_215);
lean::dec(x_210);
x_373 = lean::cnstr_get(x_363, 0);
if (lean::is_exclusive(x_363)) {
 x_375 = x_363;
} else {
 lean::inc(x_373);
 lean::dec(x_363);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_373);
return x_376;
}
else
{
obj* x_377; obj* x_380; obj* x_382; obj* x_387; 
x_377 = lean::cnstr_get(x_363, 0);
lean::inc(x_377);
lean::dec(x_363);
x_380 = lean::cnstr_get(x_377, 0);
lean::inc(x_380);
x_382 = lean::cnstr_get(x_377, 1);
lean::inc(x_382);
lean::dec(x_377);
lean::inc(x_2);
lean::inc(x_0);
x_387 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_215, x_1, x_2, x_382);
if (lean::obj_tag(x_387) == 0)
{
obj* x_395; obj* x_397; obj* x_398; 
lean::dec(x_351);
lean::dec(x_352);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_380);
lean::dec(x_2);
lean::dec(x_210);
x_395 = lean::cnstr_get(x_387, 0);
if (lean::is_exclusive(x_387)) {
 x_397 = x_387;
} else {
 lean::inc(x_395);
 lean::dec(x_387);
 x_397 = lean::box(0);
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_395);
return x_398;
}
else
{
obj* x_399; obj* x_402; obj* x_404; obj* x_407; obj* x_411; 
x_399 = lean::cnstr_get(x_387, 0);
lean::inc(x_399);
lean::dec(x_387);
x_402 = lean::cnstr_get(x_399, 0);
lean::inc(x_402);
x_404 = lean::cnstr_get(x_399, 1);
lean::inc(x_404);
lean::dec(x_399);
lean::inc(x_2);
lean::inc(x_0);
x_411 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_352, x_1, x_2, x_404);
if (lean::obj_tag(x_411) == 0)
{
obj* x_419; obj* x_421; obj* x_422; 
lean::dec(x_351);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_380);
lean::dec(x_2);
lean::dec(x_402);
lean::dec(x_210);
x_419 = lean::cnstr_get(x_411, 0);
if (lean::is_exclusive(x_411)) {
 x_421 = x_411;
} else {
 lean::inc(x_419);
 lean::dec(x_411);
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
x_423 = lean::cnstr_get(x_411, 0);
lean::inc(x_423);
lean::dec(x_411);
x_426 = lean::cnstr_get(x_210, 2);
lean::inc(x_426);
if (lean::obj_tag(x_426) == 0)
{
obj* x_429; obj* x_431; obj* x_433; obj* x_434; 
lean::dec(x_351);
x_429 = lean::cnstr_get(x_423, 0);
x_431 = lean::cnstr_get(x_423, 1);
if (lean::is_exclusive(x_423)) {
 x_433 = x_423;
} else {
 lean::inc(x_429);
 lean::inc(x_431);
 lean::dec(x_423);
 x_433 = lean::box(0);
}
if (lean::is_scalar(x_433)) {
 x_434 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_434 = x_433;
}
lean::cnstr_set(x_434, 0, x_429);
lean::cnstr_set(x_434, 1, x_431);
x_407 = x_434;
goto lbl_408;
}
else
{
obj* x_435; obj* x_437; obj* x_440; obj* x_443; obj* x_447; 
x_435 = lean::cnstr_get(x_423, 0);
lean::inc(x_435);
x_437 = lean::cnstr_get(x_423, 1);
lean::inc(x_437);
lean::dec(x_423);
x_440 = lean::cnstr_get(x_426, 0);
lean::inc(x_440);
lean::dec(x_426);
x_443 = lean::cnstr_get(x_440, 0);
lean::inc(x_443);
lean::dec(x_440);
lean::inc(x_2);
x_447 = l_Lean_Elaborator_toPexpr___main(x_443, x_1, x_2, x_437);
if (lean::obj_tag(x_447) == 0)
{
obj* x_456; obj* x_458; obj* x_459; 
lean::dec(x_351);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_380);
lean::dec(x_2);
lean::dec(x_435);
lean::dec(x_402);
lean::dec(x_210);
x_456 = lean::cnstr_get(x_447, 0);
if (lean::is_exclusive(x_447)) {
 x_458 = x_447;
} else {
 lean::inc(x_456);
 lean::dec(x_447);
 x_458 = lean::box(0);
}
if (lean::is_scalar(x_458)) {
 x_459 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_459 = x_458;
}
lean::cnstr_set(x_459, 0, x_456);
return x_459;
}
else
{
obj* x_460; obj* x_463; obj* x_465; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; 
x_460 = lean::cnstr_get(x_447, 0);
lean::inc(x_460);
lean::dec(x_447);
x_463 = lean::cnstr_get(x_460, 0);
x_465 = lean::cnstr_get(x_460, 1);
if (lean::is_exclusive(x_460)) {
 x_467 = x_460;
} else {
 lean::inc(x_463);
 lean::inc(x_465);
 lean::dec(x_460);
 x_467 = lean::box(0);
}
x_468 = lean::box(0);
if (lean::is_scalar(x_351)) {
 x_469 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_469 = x_351;
}
lean::cnstr_set(x_469, 0, x_463);
lean::cnstr_set(x_469, 1, x_468);
x_470 = l_List_append___rarg(x_435, x_469);
if (lean::is_scalar(x_467)) {
 x_471 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_471 = x_467;
}
lean::cnstr_set(x_471, 0, x_470);
lean::cnstr_set(x_471, 1, x_465);
x_407 = x_471;
goto lbl_408;
}
}
}
lbl_408:
{
obj* x_472; obj* x_474; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; uint8 x_483; obj* x_484; obj* x_485; obj* x_488; obj* x_489; obj* x_490; 
x_472 = lean::cnstr_get(x_407, 0);
x_474 = lean::cnstr_get(x_407, 1);
if (lean::is_exclusive(x_407)) {
 lean::cnstr_set(x_407, 0, lean::box(0));
 lean::cnstr_set(x_407, 1, lean::box(0));
 x_476 = x_407;
} else {
 lean::inc(x_472);
 lean::inc(x_474);
 lean::dec(x_407);
 x_476 = lean::box(0);
}
x_477 = lean::mk_nat_obj(0ul);
x_478 = l_List_lengthAux___main___rarg(x_402, x_477);
x_479 = lean::box(0);
x_480 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_481 = l_Lean_KVMap_setNat(x_479, x_480, x_478);
x_482 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_483 = lean::unbox(x_380);
x_484 = l_Lean_KVMap_setBool(x_481, x_482, x_483);
x_485 = lean::cnstr_get(x_210, 1);
lean::inc(x_485);
lean::dec(x_210);
x_488 = l_List_append___rarg(x_402, x_472);
x_489 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_490 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_489, x_488);
if (lean::obj_tag(x_485) == 0)
{
obj* x_491; obj* x_492; obj* x_493; obj* x_494; obj* x_495; 
x_491 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_492 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_493 = l_Lean_KVMap_setName(x_484, x_491, x_492);
x_494 = lean_expr_mk_mdata(x_493, x_490);
if (lean::is_scalar(x_476)) {
 x_495 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_495 = x_476;
}
lean::cnstr_set(x_495, 0, x_494);
lean::cnstr_set(x_495, 1, x_474);
x_15 = x_495;
goto lbl_16;
}
else
{
obj* x_496; obj* x_498; obj* x_499; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_507; obj* x_508; obj* x_509; obj* x_510; 
x_496 = lean::cnstr_get(x_485, 0);
if (lean::is_exclusive(x_485)) {
 x_498 = x_485;
} else {
 lean::inc(x_496);
 lean::dec(x_485);
 x_498 = lean::box(0);
}
x_499 = lean::cnstr_get(x_496, 0);
lean::inc(x_499);
lean::dec(x_496);
x_502 = l_Lean_Elaborator_mangleIdent(x_499);
if (lean::is_scalar(x_498)) {
 x_503 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_503 = x_498;
}
lean::cnstr_set(x_503, 0, x_502);
x_504 = lean::box(0);
x_505 = l_Option_getOrElse___main___rarg(x_503, x_504);
lean::dec(x_503);
x_507 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_508 = l_Lean_KVMap_setName(x_484, x_507, x_505);
x_509 = lean_expr_mk_mdata(x_508, x_490);
if (lean::is_scalar(x_476)) {
 x_510 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_510 = x_476;
}
lean::cnstr_set(x_510, 0, x_509);
lean::cnstr_set(x_510, 1, x_474);
x_15 = x_510;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_511; obj* x_513; 
x_511 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 lean::cnstr_set(x_222, 1, lean::box(0));
 x_513 = x_222;
} else {
 lean::inc(x_511);
 lean::dec(x_222);
 x_513 = lean::box(0);
}
if (lean::obj_tag(x_511) == 0)
{
obj* x_515; obj* x_520; 
lean::dec(x_348);
x_515 = lean::cnstr_get(x_221, 0);
lean::inc(x_515);
lean::dec(x_221);
lean::inc(x_2);
lean::inc(x_0);
x_520 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_215, x_1, x_2, x_3);
if (lean::obj_tag(x_520) == 0)
{
obj* x_527; obj* x_529; obj* x_530; 
lean::dec(x_513);
lean::dec(x_515);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
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
obj* x_531; obj* x_534; obj* x_536; obj* x_539; obj* x_543; 
x_531 = lean::cnstr_get(x_520, 0);
lean::inc(x_531);
lean::dec(x_520);
x_534 = lean::cnstr_get(x_531, 0);
lean::inc(x_534);
x_536 = lean::cnstr_get(x_531, 1);
lean::inc(x_536);
lean::dec(x_531);
lean::inc(x_2);
lean::inc(x_0);
x_543 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_515, x_1, x_2, x_536);
if (lean::obj_tag(x_543) == 0)
{
obj* x_550; obj* x_552; obj* x_553; 
lean::dec(x_513);
lean::dec(x_534);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_550 = lean::cnstr_get(x_543, 0);
if (lean::is_exclusive(x_543)) {
 x_552 = x_543;
} else {
 lean::inc(x_550);
 lean::dec(x_543);
 x_552 = lean::box(0);
}
if (lean::is_scalar(x_552)) {
 x_553 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_553 = x_552;
}
lean::cnstr_set(x_553, 0, x_550);
return x_553;
}
else
{
obj* x_554; obj* x_557; 
x_554 = lean::cnstr_get(x_543, 0);
lean::inc(x_554);
lean::dec(x_543);
x_557 = lean::cnstr_get(x_210, 2);
lean::inc(x_557);
if (lean::obj_tag(x_557) == 0)
{
obj* x_560; obj* x_562; obj* x_564; obj* x_565; 
lean::dec(x_513);
x_560 = lean::cnstr_get(x_554, 0);
x_562 = lean::cnstr_get(x_554, 1);
if (lean::is_exclusive(x_554)) {
 x_564 = x_554;
} else {
 lean::inc(x_560);
 lean::inc(x_562);
 lean::dec(x_554);
 x_564 = lean::box(0);
}
if (lean::is_scalar(x_564)) {
 x_565 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_565 = x_564;
}
lean::cnstr_set(x_565, 0, x_560);
lean::cnstr_set(x_565, 1, x_562);
x_539 = x_565;
goto lbl_540;
}
else
{
obj* x_566; obj* x_568; obj* x_571; obj* x_574; obj* x_578; 
x_566 = lean::cnstr_get(x_554, 0);
lean::inc(x_566);
x_568 = lean::cnstr_get(x_554, 1);
lean::inc(x_568);
lean::dec(x_554);
x_571 = lean::cnstr_get(x_557, 0);
lean::inc(x_571);
lean::dec(x_557);
x_574 = lean::cnstr_get(x_571, 0);
lean::inc(x_574);
lean::dec(x_571);
lean::inc(x_2);
x_578 = l_Lean_Elaborator_toPexpr___main(x_574, x_1, x_2, x_568);
if (lean::obj_tag(x_578) == 0)
{
obj* x_586; obj* x_588; obj* x_589; 
lean::dec(x_513);
lean::dec(x_566);
lean::dec(x_534);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
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
obj* x_590; obj* x_593; obj* x_595; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; 
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
x_598 = lean::box(0);
if (lean::is_scalar(x_513)) {
 x_599 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_599 = x_513;
}
lean::cnstr_set(x_599, 0, x_593);
lean::cnstr_set(x_599, 1, x_598);
x_600 = l_List_append___rarg(x_566, x_599);
if (lean::is_scalar(x_597)) {
 x_601 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_601 = x_597;
}
lean::cnstr_set(x_601, 0, x_600);
lean::cnstr_set(x_601, 1, x_595);
x_539 = x_601;
goto lbl_540;
}
}
}
lbl_540:
{
obj* x_602; obj* x_604; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; uint8 x_613; obj* x_614; obj* x_615; obj* x_618; obj* x_619; obj* x_620; 
x_602 = lean::cnstr_get(x_539, 0);
x_604 = lean::cnstr_get(x_539, 1);
if (lean::is_exclusive(x_539)) {
 lean::cnstr_set(x_539, 0, lean::box(0));
 lean::cnstr_set(x_539, 1, lean::box(0));
 x_606 = x_539;
} else {
 lean::inc(x_602);
 lean::inc(x_604);
 lean::dec(x_539);
 x_606 = lean::box(0);
}
x_607 = lean::mk_nat_obj(0ul);
x_608 = l_List_lengthAux___main___rarg(x_534, x_607);
x_609 = lean::box(0);
x_610 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_611 = l_Lean_KVMap_setNat(x_609, x_610, x_608);
x_612 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_613 = 1;
x_614 = l_Lean_KVMap_setBool(x_611, x_612, x_613);
x_615 = lean::cnstr_get(x_210, 1);
lean::inc(x_615);
lean::dec(x_210);
x_618 = l_List_append___rarg(x_534, x_602);
x_619 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_620 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_619, x_618);
if (lean::obj_tag(x_615) == 0)
{
obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; 
x_621 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_622 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_623 = l_Lean_KVMap_setName(x_614, x_621, x_622);
x_624 = lean_expr_mk_mdata(x_623, x_620);
if (lean::is_scalar(x_606)) {
 x_625 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_625 = x_606;
}
lean::cnstr_set(x_625, 0, x_624);
lean::cnstr_set(x_625, 1, x_604);
x_15 = x_625;
goto lbl_16;
}
else
{
obj* x_626; obj* x_628; obj* x_629; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_637; obj* x_638; obj* x_639; obj* x_640; 
x_626 = lean::cnstr_get(x_615, 0);
if (lean::is_exclusive(x_615)) {
 x_628 = x_615;
} else {
 lean::inc(x_626);
 lean::dec(x_615);
 x_628 = lean::box(0);
}
x_629 = lean::cnstr_get(x_626, 0);
lean::inc(x_629);
lean::dec(x_626);
x_632 = l_Lean_Elaborator_mangleIdent(x_629);
if (lean::is_scalar(x_628)) {
 x_633 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_633 = x_628;
}
lean::cnstr_set(x_633, 0, x_632);
x_634 = lean::box(0);
x_635 = l_Option_getOrElse___main___rarg(x_633, x_634);
lean::dec(x_633);
x_637 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_638 = l_Lean_KVMap_setName(x_614, x_637, x_635);
x_639 = lean_expr_mk_mdata(x_638, x_620);
if (lean::is_scalar(x_606)) {
 x_640 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_640 = x_606;
}
lean::cnstr_set(x_640, 0, x_639);
lean::cnstr_set(x_640, 1, x_604);
x_15 = x_640;
goto lbl_16;
}
}
}
}
else
{
obj* x_642; obj* x_643; obj* x_646; obj* x_647; obj* x_650; obj* x_651; obj* x_652; obj* x_654; 
lean::dec(x_513);
if (lean::is_exclusive(x_511)) {
 lean::cnstr_release(x_511, 0);
 lean::cnstr_release(x_511, 1);
 x_642 = x_511;
} else {
 lean::dec(x_511);
 x_642 = lean::box(0);
}
x_643 = lean::cnstr_get(x_221, 0);
lean::inc(x_643);
lean::dec(x_221);
x_646 = l_Lean_Parser_Term_structInstItem_HasView;
x_647 = lean::cnstr_get(x_646, 1);
lean::inc(x_647);
lean::dec(x_646);
x_650 = lean::apply_1(x_647, x_348);
x_651 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_651, 0, x_650);
x_652 = l_Lean_Elaborator_toPexpr___main___closed__30;
lean::inc(x_2);
x_654 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_651, x_652, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_651);
if (lean::obj_tag(x_654) == 0)
{
obj* x_664; obj* x_666; obj* x_667; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_643);
lean::dec(x_642);
lean::dec(x_215);
lean::dec(x_210);
x_664 = lean::cnstr_get(x_654, 0);
if (lean::is_exclusive(x_654)) {
 x_666 = x_654;
} else {
 lean::inc(x_664);
 lean::dec(x_654);
 x_666 = lean::box(0);
}
if (lean::is_scalar(x_666)) {
 x_667 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_667 = x_666;
}
lean::cnstr_set(x_667, 0, x_664);
return x_667;
}
else
{
obj* x_668; obj* x_671; obj* x_673; obj* x_678; 
x_668 = lean::cnstr_get(x_654, 0);
lean::inc(x_668);
lean::dec(x_654);
x_671 = lean::cnstr_get(x_668, 0);
lean::inc(x_671);
x_673 = lean::cnstr_get(x_668, 1);
lean::inc(x_673);
lean::dec(x_668);
lean::inc(x_2);
lean::inc(x_0);
x_678 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_215, x_1, x_2, x_673);
if (lean::obj_tag(x_678) == 0)
{
obj* x_686; obj* x_688; obj* x_689; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_671);
lean::dec(x_643);
lean::dec(x_642);
lean::dec(x_210);
x_686 = lean::cnstr_get(x_678, 0);
if (lean::is_exclusive(x_678)) {
 x_688 = x_678;
} else {
 lean::inc(x_686);
 lean::dec(x_678);
 x_688 = lean::box(0);
}
if (lean::is_scalar(x_688)) {
 x_689 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_689 = x_688;
}
lean::cnstr_set(x_689, 0, x_686);
return x_689;
}
else
{
obj* x_690; obj* x_693; obj* x_695; obj* x_698; obj* x_702; 
x_690 = lean::cnstr_get(x_678, 0);
lean::inc(x_690);
lean::dec(x_678);
x_693 = lean::cnstr_get(x_690, 0);
lean::inc(x_693);
x_695 = lean::cnstr_get(x_690, 1);
lean::inc(x_695);
lean::dec(x_690);
lean::inc(x_2);
lean::inc(x_0);
x_702 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_643, x_1, x_2, x_695);
if (lean::obj_tag(x_702) == 0)
{
obj* x_710; obj* x_712; obj* x_713; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_671);
lean::dec(x_693);
lean::dec(x_642);
lean::dec(x_210);
x_710 = lean::cnstr_get(x_702, 0);
if (lean::is_exclusive(x_702)) {
 x_712 = x_702;
} else {
 lean::inc(x_710);
 lean::dec(x_702);
 x_712 = lean::box(0);
}
if (lean::is_scalar(x_712)) {
 x_713 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_713 = x_712;
}
lean::cnstr_set(x_713, 0, x_710);
return x_713;
}
else
{
obj* x_714; obj* x_717; 
x_714 = lean::cnstr_get(x_702, 0);
lean::inc(x_714);
lean::dec(x_702);
x_717 = lean::cnstr_get(x_210, 2);
lean::inc(x_717);
if (lean::obj_tag(x_717) == 0)
{
obj* x_720; obj* x_722; obj* x_724; obj* x_725; 
lean::dec(x_642);
x_720 = lean::cnstr_get(x_714, 0);
x_722 = lean::cnstr_get(x_714, 1);
if (lean::is_exclusive(x_714)) {
 x_724 = x_714;
} else {
 lean::inc(x_720);
 lean::inc(x_722);
 lean::dec(x_714);
 x_724 = lean::box(0);
}
if (lean::is_scalar(x_724)) {
 x_725 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_725 = x_724;
}
lean::cnstr_set(x_725, 0, x_720);
lean::cnstr_set(x_725, 1, x_722);
x_698 = x_725;
goto lbl_699;
}
else
{
obj* x_726; obj* x_728; obj* x_731; obj* x_734; obj* x_738; 
x_726 = lean::cnstr_get(x_714, 0);
lean::inc(x_726);
x_728 = lean::cnstr_get(x_714, 1);
lean::inc(x_728);
lean::dec(x_714);
x_731 = lean::cnstr_get(x_717, 0);
lean::inc(x_731);
lean::dec(x_717);
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
lean::dec(x_2);
lean::dec(x_671);
lean::dec(x_693);
lean::dec(x_642);
lean::dec(x_726);
lean::dec(x_210);
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
obj* x_751; obj* x_754; obj* x_756; obj* x_758; obj* x_759; obj* x_760; obj* x_761; obj* x_762; 
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
x_759 = lean::box(0);
if (lean::is_scalar(x_642)) {
 x_760 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_760 = x_642;
}
lean::cnstr_set(x_760, 0, x_754);
lean::cnstr_set(x_760, 1, x_759);
x_761 = l_List_append___rarg(x_726, x_760);
if (lean::is_scalar(x_758)) {
 x_762 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_762 = x_758;
}
lean::cnstr_set(x_762, 0, x_761);
lean::cnstr_set(x_762, 1, x_756);
x_698 = x_762;
goto lbl_699;
}
}
}
lbl_699:
{
obj* x_763; obj* x_765; obj* x_767; obj* x_768; obj* x_769; obj* x_770; obj* x_771; obj* x_772; obj* x_773; uint8 x_774; obj* x_775; obj* x_776; obj* x_779; obj* x_780; obj* x_781; 
x_763 = lean::cnstr_get(x_698, 0);
x_765 = lean::cnstr_get(x_698, 1);
if (lean::is_exclusive(x_698)) {
 lean::cnstr_set(x_698, 0, lean::box(0));
 lean::cnstr_set(x_698, 1, lean::box(0));
 x_767 = x_698;
} else {
 lean::inc(x_763);
 lean::inc(x_765);
 lean::dec(x_698);
 x_767 = lean::box(0);
}
x_768 = lean::mk_nat_obj(0ul);
x_769 = l_List_lengthAux___main___rarg(x_693, x_768);
x_770 = lean::box(0);
x_771 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_772 = l_Lean_KVMap_setNat(x_770, x_771, x_769);
x_773 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_774 = lean::unbox(x_671);
x_775 = l_Lean_KVMap_setBool(x_772, x_773, x_774);
x_776 = lean::cnstr_get(x_210, 1);
lean::inc(x_776);
lean::dec(x_210);
x_779 = l_List_append___rarg(x_693, x_763);
x_780 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_781 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_780, x_779);
if (lean::obj_tag(x_776) == 0)
{
obj* x_782; obj* x_783; obj* x_784; obj* x_785; obj* x_786; 
x_782 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_783 = l_Lean_Elaborator_toPexpr___main___closed__29;
x_784 = l_Lean_KVMap_setName(x_775, x_782, x_783);
x_785 = lean_expr_mk_mdata(x_784, x_781);
if (lean::is_scalar(x_767)) {
 x_786 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_786 = x_767;
}
lean::cnstr_set(x_786, 0, x_785);
lean::cnstr_set(x_786, 1, x_765);
x_15 = x_786;
goto lbl_16;
}
else
{
obj* x_787; obj* x_789; obj* x_790; obj* x_793; obj* x_794; obj* x_795; obj* x_796; obj* x_798; obj* x_799; obj* x_800; obj* x_801; 
x_787 = lean::cnstr_get(x_776, 0);
if (lean::is_exclusive(x_776)) {
 x_789 = x_776;
} else {
 lean::inc(x_787);
 lean::dec(x_776);
 x_789 = lean::box(0);
}
x_790 = lean::cnstr_get(x_787, 0);
lean::inc(x_790);
lean::dec(x_787);
x_793 = l_Lean_Elaborator_mangleIdent(x_790);
if (lean::is_scalar(x_789)) {
 x_794 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_794 = x_789;
}
lean::cnstr_set(x_794, 0, x_793);
x_795 = lean::box(0);
x_796 = l_Option_getOrElse___main___rarg(x_794, x_795);
lean::dec(x_794);
x_798 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_799 = l_Lean_KVMap_setName(x_775, x_798, x_796);
x_800 = lean_expr_mk_mdata(x_799, x_781);
if (lean::is_scalar(x_767)) {
 x_801 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_801 = x_767;
}
lean::cnstr_set(x_801, 0, x_800);
lean::cnstr_set(x_801, 1, x_765);
x_15 = x_801;
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
obj* x_804; 
lean::inc(x_2);
lean::inc(x_10);
x_804 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_804) == 0)
{
obj* x_809; obj* x_811; obj* x_812; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_809 = lean::cnstr_get(x_804, 0);
if (lean::is_exclusive(x_804)) {
 x_811 = x_804;
} else {
 lean::inc(x_809);
 lean::dec(x_804);
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
obj* x_813; obj* x_816; obj* x_818; obj* x_820; obj* x_821; 
x_813 = lean::cnstr_get(x_804, 0);
lean::inc(x_813);
lean::dec(x_804);
x_816 = lean::cnstr_get(x_813, 0);
x_818 = lean::cnstr_get(x_813, 1);
if (lean::is_exclusive(x_813)) {
 lean::cnstr_set(x_813, 0, lean::box(0));
 lean::cnstr_set(x_813, 1, lean::box(0));
 x_820 = x_813;
} else {
 lean::inc(x_816);
 lean::inc(x_818);
 lean::dec(x_813);
 x_820 = lean::box(0);
}
x_821 = l_List_reverse___rarg(x_816);
if (lean::obj_tag(x_821) == 0)
{
obj* x_825; obj* x_826; obj* x_828; 
lean::dec(x_820);
lean::dec(x_10);
lean::inc(x_0);
x_825 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_825, 0, x_0);
x_826 = l_Lean_Elaborator_toPexpr___main___closed__31;
lean::inc(x_2);
x_828 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_825, x_826, x_1, x_2, x_818);
lean::dec(x_818);
lean::dec(x_825);
if (lean::obj_tag(x_828) == 0)
{
obj* x_834; obj* x_836; obj* x_837; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_834 = lean::cnstr_get(x_828, 0);
if (lean::is_exclusive(x_828)) {
 x_836 = x_828;
} else {
 lean::inc(x_834);
 lean::dec(x_828);
 x_836 = lean::box(0);
}
if (lean::is_scalar(x_836)) {
 x_837 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_837 = x_836;
}
lean::cnstr_set(x_837, 0, x_834);
return x_837;
}
else
{
obj* x_838; 
x_838 = lean::cnstr_get(x_828, 0);
lean::inc(x_838);
lean::dec(x_828);
x_15 = x_838;
goto lbl_16;
}
}
else
{
obj* x_841; obj* x_843; obj* x_846; obj* x_847; obj* x_849; obj* x_850; obj* x_851; obj* x_852; obj* x_853; obj* x_855; obj* x_856; 
x_841 = lean::cnstr_get(x_821, 0);
lean::inc(x_841);
x_843 = lean::cnstr_get(x_821, 1);
lean::inc(x_843);
lean::dec(x_821);
x_846 = lean::mk_nat_obj(0ul);
x_847 = l_List_lengthAux___main___rarg(x_10, x_846);
lean::dec(x_10);
x_849 = lean::box(0);
x_850 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_851 = l_Lean_KVMap_setNat(x_849, x_850, x_847);
x_852 = l_List_reverse___rarg(x_843);
x_853 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(x_841, x_852);
lean::dec(x_841);
x_855 = lean_expr_mk_mdata(x_851, x_853);
if (lean::is_scalar(x_820)) {
 x_856 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_856 = x_820;
}
lean::cnstr_set(x_856, 0, x_855);
lean::cnstr_set(x_856, 1, x_818);
x_15 = x_856;
goto lbl_16;
}
}
}
}
else
{
obj* x_859; obj* x_860; obj* x_864; obj* x_865; obj* x_866; obj* x_867; obj* x_869; obj* x_870; 
lean::dec(x_8);
lean::dec(x_10);
x_859 = l_Lean_Parser_stringLit_HasView;
x_860 = lean::cnstr_get(x_859, 0);
lean::inc(x_860);
lean::dec(x_859);
lean::inc(x_0);
x_864 = lean::apply_1(x_860, x_0);
x_865 = l_Lean_Parser_stringLit_View_value(x_864);
x_866 = l_Lean_Elaborator_toPexpr___main___closed__33;
x_867 = l_Option_getOrElse___main___rarg(x_865, x_866);
lean::dec(x_865);
x_869 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_869, 0, x_867);
x_870 = lean_expr_mk_lit(x_869);
if (x_20 == 0)
{
obj* x_871; 
x_871 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_871) == 0)
{
obj* x_874; obj* x_875; 
lean::dec(x_2);
x_874 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_874, 0, x_870);
lean::cnstr_set(x_874, 1, x_3);
x_875 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_875, 0, x_874);
return x_875;
}
else
{
obj* x_876; obj* x_879; obj* x_882; obj* x_885; obj* x_886; obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_894; obj* x_895; obj* x_896; obj* x_897; obj* x_898; 
x_876 = lean::cnstr_get(x_871, 0);
lean::inc(x_876);
lean::dec(x_871);
x_879 = lean::cnstr_get(x_2, 0);
lean::inc(x_879);
lean::dec(x_2);
x_882 = lean::cnstr_get(x_879, 2);
lean::inc(x_882);
lean::dec(x_879);
x_885 = l_Lean_FileMap_toPosition(x_882, x_876);
x_886 = lean::cnstr_get(x_885, 1);
lean::inc(x_886);
x_888 = lean::box(0);
x_889 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_890 = l_Lean_KVMap_setNat(x_888, x_889, x_886);
x_891 = lean::cnstr_get(x_885, 0);
lean::inc(x_891);
lean::dec(x_885);
x_894 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_895 = l_Lean_KVMap_setNat(x_890, x_894, x_891);
x_896 = lean_expr_mk_mdata(x_895, x_870);
x_897 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_897, 0, x_896);
lean::cnstr_set(x_897, 1, x_3);
x_898 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_898, 0, x_897);
return x_898;
}
}
else
{
obj* x_901; obj* x_902; 
lean::dec(x_0);
lean::dec(x_2);
x_901 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_901, 0, x_870);
lean::cnstr_set(x_901, 1, x_3);
x_902 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_902, 0, x_901);
return x_902;
}
}
}
else
{
obj* x_905; obj* x_906; obj* x_910; obj* x_911; obj* x_912; obj* x_913; 
lean::dec(x_8);
lean::dec(x_10);
x_905 = l_Lean_Parser_number_HasView;
x_906 = lean::cnstr_get(x_905, 0);
lean::inc(x_906);
lean::dec(x_905);
lean::inc(x_0);
x_910 = lean::apply_1(x_906, x_0);
x_911 = l_Lean_Parser_number_View_toNat___main(x_910);
x_912 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_912, 0, x_911);
x_913 = lean_expr_mk_lit(x_912);
if (x_20 == 0)
{
obj* x_914; 
x_914 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_914) == 0)
{
obj* x_917; obj* x_918; 
lean::dec(x_2);
x_917 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_917, 0, x_913);
lean::cnstr_set(x_917, 1, x_3);
x_918 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_918, 0, x_917);
return x_918;
}
else
{
obj* x_919; obj* x_922; obj* x_925; obj* x_928; obj* x_929; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_937; obj* x_938; obj* x_939; obj* x_940; obj* x_941; 
x_919 = lean::cnstr_get(x_914, 0);
lean::inc(x_919);
lean::dec(x_914);
x_922 = lean::cnstr_get(x_2, 0);
lean::inc(x_922);
lean::dec(x_2);
x_925 = lean::cnstr_get(x_922, 2);
lean::inc(x_925);
lean::dec(x_922);
x_928 = l_Lean_FileMap_toPosition(x_925, x_919);
x_929 = lean::cnstr_get(x_928, 1);
lean::inc(x_929);
x_931 = lean::box(0);
x_932 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_933 = l_Lean_KVMap_setNat(x_931, x_932, x_929);
x_934 = lean::cnstr_get(x_928, 0);
lean::inc(x_934);
lean::dec(x_928);
x_937 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_938 = l_Lean_KVMap_setNat(x_933, x_937, x_934);
x_939 = lean_expr_mk_mdata(x_938, x_913);
x_940 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_940, 0, x_939);
lean::cnstr_set(x_940, 1, x_3);
x_941 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_941, 0, x_940);
return x_941;
}
}
else
{
obj* x_944; obj* x_945; 
lean::dec(x_0);
lean::dec(x_2);
x_944 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_944, 0, x_913);
lean::cnstr_set(x_944, 1, x_3);
x_945 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_945, 0, x_944);
return x_945;
}
}
}
else
{
obj* x_948; obj* x_949; obj* x_953; obj* x_954; obj* x_958; 
lean::dec(x_8);
lean::dec(x_10);
x_948 = l_Lean_Parser_Term_borrowed_HasView;
x_949 = lean::cnstr_get(x_948, 0);
lean::inc(x_949);
lean::dec(x_948);
lean::inc(x_0);
x_953 = lean::apply_1(x_949, x_0);
x_954 = lean::cnstr_get(x_953, 1);
lean::inc(x_954);
lean::dec(x_953);
lean::inc(x_2);
x_958 = l_Lean_Elaborator_toPexpr___main(x_954, x_1, x_2, x_3);
if (lean::obj_tag(x_958) == 0)
{
obj* x_961; obj* x_963; obj* x_964; 
lean::dec(x_0);
lean::dec(x_2);
x_961 = lean::cnstr_get(x_958, 0);
if (lean::is_exclusive(x_958)) {
 x_963 = x_958;
} else {
 lean::inc(x_961);
 lean::dec(x_958);
 x_963 = lean::box(0);
}
if (lean::is_scalar(x_963)) {
 x_964 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_964 = x_963;
}
lean::cnstr_set(x_964, 0, x_961);
return x_964;
}
else
{
obj* x_965; obj* x_967; obj* x_968; obj* x_970; obj* x_972; obj* x_973; obj* x_974; 
x_965 = lean::cnstr_get(x_958, 0);
if (lean::is_exclusive(x_958)) {
 lean::cnstr_set(x_958, 0, lean::box(0));
 x_967 = x_958;
} else {
 lean::inc(x_965);
 lean::dec(x_958);
 x_967 = lean::box(0);
}
x_968 = lean::cnstr_get(x_965, 0);
x_970 = lean::cnstr_get(x_965, 1);
if (lean::is_exclusive(x_965)) {
 lean::cnstr_set(x_965, 0, lean::box(0));
 lean::cnstr_set(x_965, 1, lean::box(0));
 x_972 = x_965;
} else {
 lean::inc(x_968);
 lean::inc(x_970);
 lean::dec(x_965);
 x_972 = lean::box(0);
}
x_973 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_974 = l_Lean_Elaborator_Expr_mkAnnotation(x_973, x_968);
if (x_20 == 0)
{
obj* x_975; 
x_975 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_975) == 0)
{
obj* x_978; obj* x_979; 
lean::dec(x_2);
if (lean::is_scalar(x_972)) {
 x_978 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_978 = x_972;
}
lean::cnstr_set(x_978, 0, x_974);
lean::cnstr_set(x_978, 1, x_970);
if (lean::is_scalar(x_967)) {
 x_979 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_979 = x_967;
}
lean::cnstr_set(x_979, 0, x_978);
return x_979;
}
else
{
obj* x_980; obj* x_983; obj* x_986; obj* x_989; obj* x_990; obj* x_992; obj* x_993; obj* x_994; obj* x_995; obj* x_998; obj* x_999; obj* x_1000; obj* x_1001; obj* x_1002; 
x_980 = lean::cnstr_get(x_975, 0);
lean::inc(x_980);
lean::dec(x_975);
x_983 = lean::cnstr_get(x_2, 0);
lean::inc(x_983);
lean::dec(x_2);
x_986 = lean::cnstr_get(x_983, 2);
lean::inc(x_986);
lean::dec(x_983);
x_989 = l_Lean_FileMap_toPosition(x_986, x_980);
x_990 = lean::cnstr_get(x_989, 1);
lean::inc(x_990);
x_992 = lean::box(0);
x_993 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_994 = l_Lean_KVMap_setNat(x_992, x_993, x_990);
x_995 = lean::cnstr_get(x_989, 0);
lean::inc(x_995);
lean::dec(x_989);
x_998 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_999 = l_Lean_KVMap_setNat(x_994, x_998, x_995);
x_1000 = lean_expr_mk_mdata(x_999, x_974);
if (lean::is_scalar(x_972)) {
 x_1001 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1001 = x_972;
}
lean::cnstr_set(x_1001, 0, x_1000);
lean::cnstr_set(x_1001, 1, x_970);
if (lean::is_scalar(x_967)) {
 x_1002 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1002 = x_967;
}
lean::cnstr_set(x_1002, 0, x_1001);
return x_1002;
}
}
else
{
obj* x_1005; obj* x_1006; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_972)) {
 x_1005 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1005 = x_972;
}
lean::cnstr_set(x_1005, 0, x_974);
lean::cnstr_set(x_1005, 1, x_970);
if (lean::is_scalar(x_967)) {
 x_1006 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1006 = x_967;
}
lean::cnstr_set(x_1006, 0, x_1005);
return x_1006;
}
}
}
}
else
{
obj* x_1009; obj* x_1010; obj* x_1014; obj* x_1015; obj* x_1019; 
lean::dec(x_8);
lean::dec(x_10);
x_1009 = l_Lean_Parser_Term_inaccessible_HasView;
x_1010 = lean::cnstr_get(x_1009, 0);
lean::inc(x_1010);
lean::dec(x_1009);
lean::inc(x_0);
x_1014 = lean::apply_1(x_1010, x_0);
x_1015 = lean::cnstr_get(x_1014, 1);
lean::inc(x_1015);
lean::dec(x_1014);
lean::inc(x_2);
x_1019 = l_Lean_Elaborator_toPexpr___main(x_1015, x_1, x_2, x_3);
if (lean::obj_tag(x_1019) == 0)
{
obj* x_1022; obj* x_1024; obj* x_1025; 
lean::dec(x_0);
lean::dec(x_2);
x_1022 = lean::cnstr_get(x_1019, 0);
if (lean::is_exclusive(x_1019)) {
 x_1024 = x_1019;
} else {
 lean::inc(x_1022);
 lean::dec(x_1019);
 x_1024 = lean::box(0);
}
if (lean::is_scalar(x_1024)) {
 x_1025 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1025 = x_1024;
}
lean::cnstr_set(x_1025, 0, x_1022);
return x_1025;
}
else
{
obj* x_1026; obj* x_1028; obj* x_1029; obj* x_1031; obj* x_1033; obj* x_1034; obj* x_1035; 
x_1026 = lean::cnstr_get(x_1019, 0);
if (lean::is_exclusive(x_1019)) {
 lean::cnstr_set(x_1019, 0, lean::box(0));
 x_1028 = x_1019;
} else {
 lean::inc(x_1026);
 lean::dec(x_1019);
 x_1028 = lean::box(0);
}
x_1029 = lean::cnstr_get(x_1026, 0);
x_1031 = lean::cnstr_get(x_1026, 1);
if (lean::is_exclusive(x_1026)) {
 lean::cnstr_set(x_1026, 0, lean::box(0));
 lean::cnstr_set(x_1026, 1, lean::box(0));
 x_1033 = x_1026;
} else {
 lean::inc(x_1029);
 lean::inc(x_1031);
 lean::dec(x_1026);
 x_1033 = lean::box(0);
}
x_1034 = l_Lean_Elaborator_toPexpr___main___closed__35;
x_1035 = l_Lean_Elaborator_Expr_mkAnnotation(x_1034, x_1029);
if (x_20 == 0)
{
obj* x_1036; 
x_1036 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1036) == 0)
{
obj* x_1039; obj* x_1040; 
lean::dec(x_2);
if (lean::is_scalar(x_1033)) {
 x_1039 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1039 = x_1033;
}
lean::cnstr_set(x_1039, 0, x_1035);
lean::cnstr_set(x_1039, 1, x_1031);
if (lean::is_scalar(x_1028)) {
 x_1040 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1040 = x_1028;
}
lean::cnstr_set(x_1040, 0, x_1039);
return x_1040;
}
else
{
obj* x_1041; obj* x_1044; obj* x_1047; obj* x_1050; obj* x_1051; obj* x_1053; obj* x_1054; obj* x_1055; obj* x_1056; obj* x_1059; obj* x_1060; obj* x_1061; obj* x_1062; obj* x_1063; 
x_1041 = lean::cnstr_get(x_1036, 0);
lean::inc(x_1041);
lean::dec(x_1036);
x_1044 = lean::cnstr_get(x_2, 0);
lean::inc(x_1044);
lean::dec(x_2);
x_1047 = lean::cnstr_get(x_1044, 2);
lean::inc(x_1047);
lean::dec(x_1044);
x_1050 = l_Lean_FileMap_toPosition(x_1047, x_1041);
x_1051 = lean::cnstr_get(x_1050, 1);
lean::inc(x_1051);
x_1053 = lean::box(0);
x_1054 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1055 = l_Lean_KVMap_setNat(x_1053, x_1054, x_1051);
x_1056 = lean::cnstr_get(x_1050, 0);
lean::inc(x_1056);
lean::dec(x_1050);
x_1059 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1060 = l_Lean_KVMap_setNat(x_1055, x_1059, x_1056);
x_1061 = lean_expr_mk_mdata(x_1060, x_1035);
if (lean::is_scalar(x_1033)) {
 x_1062 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1062 = x_1033;
}
lean::cnstr_set(x_1062, 0, x_1061);
lean::cnstr_set(x_1062, 1, x_1031);
if (lean::is_scalar(x_1028)) {
 x_1063 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1063 = x_1028;
}
lean::cnstr_set(x_1063, 0, x_1062);
return x_1063;
}
}
else
{
obj* x_1066; obj* x_1067; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1033)) {
 x_1066 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1066 = x_1033;
}
lean::cnstr_set(x_1066, 0, x_1035);
lean::cnstr_set(x_1066, 1, x_1031);
if (lean::is_scalar(x_1028)) {
 x_1067 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1067 = x_1028;
}
lean::cnstr_set(x_1067, 0, x_1066);
return x_1067;
}
}
}
}
else
{
obj* x_1070; obj* x_1071; obj* x_1075; obj* x_1076; obj* x_1078; obj* x_1079; obj* x_1082; obj* x_1085; 
lean::dec(x_8);
lean::dec(x_10);
x_1070 = l_Lean_Parser_Term_explicit_HasView;
x_1071 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1071);
lean::dec(x_1070);
lean::inc(x_0);
x_1075 = lean::apply_1(x_1071, x_0);
x_1076 = lean::cnstr_get(x_1075, 0);
lean::inc(x_1076);
x_1078 = l_Lean_Parser_identUnivs_HasView;
x_1079 = lean::cnstr_get(x_1078, 1);
lean::inc(x_1079);
lean::dec(x_1078);
x_1082 = lean::cnstr_get(x_1075, 1);
lean::inc(x_1082);
lean::dec(x_1075);
x_1085 = lean::apply_1(x_1079, x_1082);
if (lean::obj_tag(x_1076) == 0)
{
obj* x_1088; 
lean::dec(x_1076);
lean::inc(x_2);
x_1088 = l_Lean_Elaborator_toPexpr___main(x_1085, x_1, x_2, x_3);
if (lean::obj_tag(x_1088) == 0)
{
obj* x_1091; obj* x_1093; obj* x_1094; 
lean::dec(x_0);
lean::dec(x_2);
x_1091 = lean::cnstr_get(x_1088, 0);
if (lean::is_exclusive(x_1088)) {
 x_1093 = x_1088;
} else {
 lean::inc(x_1091);
 lean::dec(x_1088);
 x_1093 = lean::box(0);
}
if (lean::is_scalar(x_1093)) {
 x_1094 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1094 = x_1093;
}
lean::cnstr_set(x_1094, 0, x_1091);
return x_1094;
}
else
{
obj* x_1095; obj* x_1097; obj* x_1098; obj* x_1100; obj* x_1102; obj* x_1103; obj* x_1104; 
x_1095 = lean::cnstr_get(x_1088, 0);
if (lean::is_exclusive(x_1088)) {
 lean::cnstr_set(x_1088, 0, lean::box(0));
 x_1097 = x_1088;
} else {
 lean::inc(x_1095);
 lean::dec(x_1088);
 x_1097 = lean::box(0);
}
x_1098 = lean::cnstr_get(x_1095, 0);
x_1100 = lean::cnstr_get(x_1095, 1);
if (lean::is_exclusive(x_1095)) {
 lean::cnstr_set(x_1095, 0, lean::box(0));
 lean::cnstr_set(x_1095, 1, lean::box(0));
 x_1102 = x_1095;
} else {
 lean::inc(x_1098);
 lean::inc(x_1100);
 lean::dec(x_1095);
 x_1102 = lean::box(0);
}
x_1103 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_1104 = l_Lean_Elaborator_Expr_mkAnnotation(x_1103, x_1098);
if (x_20 == 0)
{
obj* x_1105; 
x_1105 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1105) == 0)
{
obj* x_1108; obj* x_1109; 
lean::dec(x_2);
if (lean::is_scalar(x_1102)) {
 x_1108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1108 = x_1102;
}
lean::cnstr_set(x_1108, 0, x_1104);
lean::cnstr_set(x_1108, 1, x_1100);
if (lean::is_scalar(x_1097)) {
 x_1109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1109 = x_1097;
}
lean::cnstr_set(x_1109, 0, x_1108);
return x_1109;
}
else
{
obj* x_1110; obj* x_1113; obj* x_1116; obj* x_1119; obj* x_1120; obj* x_1122; obj* x_1123; obj* x_1124; obj* x_1125; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; obj* x_1132; 
x_1110 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1110);
lean::dec(x_1105);
x_1113 = lean::cnstr_get(x_2, 0);
lean::inc(x_1113);
lean::dec(x_2);
x_1116 = lean::cnstr_get(x_1113, 2);
lean::inc(x_1116);
lean::dec(x_1113);
x_1119 = l_Lean_FileMap_toPosition(x_1116, x_1110);
x_1120 = lean::cnstr_get(x_1119, 1);
lean::inc(x_1120);
x_1122 = lean::box(0);
x_1123 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1124 = l_Lean_KVMap_setNat(x_1122, x_1123, x_1120);
x_1125 = lean::cnstr_get(x_1119, 0);
lean::inc(x_1125);
lean::dec(x_1119);
x_1128 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1129 = l_Lean_KVMap_setNat(x_1124, x_1128, x_1125);
x_1130 = lean_expr_mk_mdata(x_1129, x_1104);
if (lean::is_scalar(x_1102)) {
 x_1131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1131 = x_1102;
}
lean::cnstr_set(x_1131, 0, x_1130);
lean::cnstr_set(x_1131, 1, x_1100);
if (lean::is_scalar(x_1097)) {
 x_1132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1132 = x_1097;
}
lean::cnstr_set(x_1132, 0, x_1131);
return x_1132;
}
}
else
{
obj* x_1135; obj* x_1136; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1102)) {
 x_1135 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1135 = x_1102;
}
lean::cnstr_set(x_1135, 0, x_1104);
lean::cnstr_set(x_1135, 1, x_1100);
if (lean::is_scalar(x_1097)) {
 x_1136 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1136 = x_1097;
}
lean::cnstr_set(x_1136, 0, x_1135);
return x_1136;
}
}
}
else
{
obj* x_1139; 
lean::dec(x_1076);
lean::inc(x_2);
x_1139 = l_Lean_Elaborator_toPexpr___main(x_1085, x_1, x_2, x_3);
if (lean::obj_tag(x_1139) == 0)
{
obj* x_1142; obj* x_1144; obj* x_1145; 
lean::dec(x_0);
lean::dec(x_2);
x_1142 = lean::cnstr_get(x_1139, 0);
if (lean::is_exclusive(x_1139)) {
 x_1144 = x_1139;
} else {
 lean::inc(x_1142);
 lean::dec(x_1139);
 x_1144 = lean::box(0);
}
if (lean::is_scalar(x_1144)) {
 x_1145 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1145 = x_1144;
}
lean::cnstr_set(x_1145, 0, x_1142);
return x_1145;
}
else
{
obj* x_1146; obj* x_1148; obj* x_1149; obj* x_1151; obj* x_1153; obj* x_1154; obj* x_1155; 
x_1146 = lean::cnstr_get(x_1139, 0);
if (lean::is_exclusive(x_1139)) {
 lean::cnstr_set(x_1139, 0, lean::box(0));
 x_1148 = x_1139;
} else {
 lean::inc(x_1146);
 lean::dec(x_1139);
 x_1148 = lean::box(0);
}
x_1149 = lean::cnstr_get(x_1146, 0);
x_1151 = lean::cnstr_get(x_1146, 1);
if (lean::is_exclusive(x_1146)) {
 lean::cnstr_set(x_1146, 0, lean::box(0));
 lean::cnstr_set(x_1146, 1, lean::box(0));
 x_1153 = x_1146;
} else {
 lean::inc(x_1149);
 lean::inc(x_1151);
 lean::dec(x_1146);
 x_1153 = lean::box(0);
}
x_1154 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1155 = l_Lean_Elaborator_Expr_mkAnnotation(x_1154, x_1149);
if (x_20 == 0)
{
obj* x_1156; 
x_1156 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1156) == 0)
{
obj* x_1159; obj* x_1160; 
lean::dec(x_2);
if (lean::is_scalar(x_1153)) {
 x_1159 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1159 = x_1153;
}
lean::cnstr_set(x_1159, 0, x_1155);
lean::cnstr_set(x_1159, 1, x_1151);
if (lean::is_scalar(x_1148)) {
 x_1160 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1160 = x_1148;
}
lean::cnstr_set(x_1160, 0, x_1159);
return x_1160;
}
else
{
obj* x_1161; obj* x_1164; obj* x_1167; obj* x_1170; obj* x_1171; obj* x_1173; obj* x_1174; obj* x_1175; obj* x_1176; obj* x_1179; obj* x_1180; obj* x_1181; obj* x_1182; obj* x_1183; 
x_1161 = lean::cnstr_get(x_1156, 0);
lean::inc(x_1161);
lean::dec(x_1156);
x_1164 = lean::cnstr_get(x_2, 0);
lean::inc(x_1164);
lean::dec(x_2);
x_1167 = lean::cnstr_get(x_1164, 2);
lean::inc(x_1167);
lean::dec(x_1164);
x_1170 = l_Lean_FileMap_toPosition(x_1167, x_1161);
x_1171 = lean::cnstr_get(x_1170, 1);
lean::inc(x_1171);
x_1173 = lean::box(0);
x_1174 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1175 = l_Lean_KVMap_setNat(x_1173, x_1174, x_1171);
x_1176 = lean::cnstr_get(x_1170, 0);
lean::inc(x_1176);
lean::dec(x_1170);
x_1179 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1180 = l_Lean_KVMap_setNat(x_1175, x_1179, x_1176);
x_1181 = lean_expr_mk_mdata(x_1180, x_1155);
if (lean::is_scalar(x_1153)) {
 x_1182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1182 = x_1153;
}
lean::cnstr_set(x_1182, 0, x_1181);
lean::cnstr_set(x_1182, 1, x_1151);
if (lean::is_scalar(x_1148)) {
 x_1183 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1183 = x_1148;
}
lean::cnstr_set(x_1183, 0, x_1182);
return x_1183;
}
}
else
{
obj* x_1186; obj* x_1187; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1153)) {
 x_1186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1186 = x_1153;
}
lean::cnstr_set(x_1186, 0, x_1155);
lean::cnstr_set(x_1186, 1, x_1151);
if (lean::is_scalar(x_1148)) {
 x_1187 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1187 = x_1148;
}
lean::cnstr_set(x_1187, 0, x_1186);
return x_1187;
}
}
}
}
}
else
{
obj* x_1190; obj* x_1191; obj* x_1195; obj* x_1196; 
lean::dec(x_8);
lean::dec(x_10);
x_1190 = l_Lean_Parser_Term_projection_HasView;
x_1191 = lean::cnstr_get(x_1190, 0);
lean::inc(x_1191);
lean::dec(x_1190);
lean::inc(x_0);
x_1195 = lean::apply_1(x_1191, x_0);
x_1196 = lean::cnstr_get(x_1195, 2);
lean::inc(x_1196);
if (lean::obj_tag(x_1196) == 0)
{
obj* x_1198; obj* x_1201; obj* x_1205; 
x_1198 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1198);
lean::dec(x_1195);
x_1201 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1201);
lean::dec(x_1196);
lean::inc(x_2);
x_1205 = l_Lean_Elaborator_toPexpr___main(x_1198, x_1, x_2, x_3);
if (lean::obj_tag(x_1205) == 0)
{
obj* x_1209; obj* x_1211; obj* x_1212; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1201);
x_1209 = lean::cnstr_get(x_1205, 0);
if (lean::is_exclusive(x_1205)) {
 x_1211 = x_1205;
} else {
 lean::inc(x_1209);
 lean::dec(x_1205);
 x_1211 = lean::box(0);
}
if (lean::is_scalar(x_1211)) {
 x_1212 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1212 = x_1211;
}
lean::cnstr_set(x_1212, 0, x_1209);
return x_1212;
}
else
{
obj* x_1213; obj* x_1215; obj* x_1216; obj* x_1218; obj* x_1220; obj* x_1221; obj* x_1224; obj* x_1225; obj* x_1226; obj* x_1227; obj* x_1228; 
x_1213 = lean::cnstr_get(x_1205, 0);
if (lean::is_exclusive(x_1205)) {
 lean::cnstr_set(x_1205, 0, lean::box(0));
 x_1215 = x_1205;
} else {
 lean::inc(x_1213);
 lean::dec(x_1205);
 x_1215 = lean::box(0);
}
x_1216 = lean::cnstr_get(x_1213, 0);
x_1218 = lean::cnstr_get(x_1213, 1);
if (lean::is_exclusive(x_1213)) {
 lean::cnstr_set(x_1213, 0, lean::box(0));
 lean::cnstr_set(x_1213, 1, lean::box(0));
 x_1220 = x_1213;
} else {
 lean::inc(x_1216);
 lean::inc(x_1218);
 lean::dec(x_1213);
 x_1220 = lean::box(0);
}
x_1221 = lean::cnstr_get(x_1201, 2);
lean::inc(x_1221);
lean::dec(x_1201);
x_1224 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1224, 0, x_1221);
x_1225 = lean::box(0);
x_1226 = l_Lean_Elaborator_toPexpr___main___closed__37;
x_1227 = l_Lean_KVMap_insertCore___main(x_1225, x_1226, x_1224);
x_1228 = lean_expr_mk_mdata(x_1227, x_1216);
if (x_20 == 0)
{
obj* x_1229; 
x_1229 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1229) == 0)
{
obj* x_1232; obj* x_1233; 
lean::dec(x_2);
if (lean::is_scalar(x_1220)) {
 x_1232 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1232 = x_1220;
}
lean::cnstr_set(x_1232, 0, x_1228);
lean::cnstr_set(x_1232, 1, x_1218);
if (lean::is_scalar(x_1215)) {
 x_1233 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1233 = x_1215;
}
lean::cnstr_set(x_1233, 0, x_1232);
return x_1233;
}
else
{
obj* x_1234; obj* x_1237; obj* x_1240; obj* x_1243; obj* x_1244; obj* x_1246; obj* x_1247; obj* x_1248; obj* x_1251; obj* x_1252; obj* x_1253; obj* x_1254; obj* x_1255; 
x_1234 = lean::cnstr_get(x_1229, 0);
lean::inc(x_1234);
lean::dec(x_1229);
x_1237 = lean::cnstr_get(x_2, 0);
lean::inc(x_1237);
lean::dec(x_2);
x_1240 = lean::cnstr_get(x_1237, 2);
lean::inc(x_1240);
lean::dec(x_1237);
x_1243 = l_Lean_FileMap_toPosition(x_1240, x_1234);
x_1244 = lean::cnstr_get(x_1243, 1);
lean::inc(x_1244);
x_1246 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1247 = l_Lean_KVMap_setNat(x_1225, x_1246, x_1244);
x_1248 = lean::cnstr_get(x_1243, 0);
lean::inc(x_1248);
lean::dec(x_1243);
x_1251 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1252 = l_Lean_KVMap_setNat(x_1247, x_1251, x_1248);
x_1253 = lean_expr_mk_mdata(x_1252, x_1228);
if (lean::is_scalar(x_1220)) {
 x_1254 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1254 = x_1220;
}
lean::cnstr_set(x_1254, 0, x_1253);
lean::cnstr_set(x_1254, 1, x_1218);
if (lean::is_scalar(x_1215)) {
 x_1255 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1255 = x_1215;
}
lean::cnstr_set(x_1255, 0, x_1254);
return x_1255;
}
}
else
{
obj* x_1258; obj* x_1259; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1220)) {
 x_1258 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1258 = x_1220;
}
lean::cnstr_set(x_1258, 0, x_1228);
lean::cnstr_set(x_1258, 1, x_1218);
if (lean::is_scalar(x_1215)) {
 x_1259 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1259 = x_1215;
}
lean::cnstr_set(x_1259, 0, x_1258);
return x_1259;
}
}
}
else
{
obj* x_1260; obj* x_1263; obj* x_1267; 
x_1260 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1260);
lean::dec(x_1195);
x_1263 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1263);
lean::dec(x_1196);
lean::inc(x_2);
x_1267 = l_Lean_Elaborator_toPexpr___main(x_1260, x_1, x_2, x_3);
if (lean::obj_tag(x_1267) == 0)
{
obj* x_1271; obj* x_1273; obj* x_1274; 
lean::dec(x_1263);
lean::dec(x_0);
lean::dec(x_2);
x_1271 = lean::cnstr_get(x_1267, 0);
if (lean::is_exclusive(x_1267)) {
 x_1273 = x_1267;
} else {
 lean::inc(x_1271);
 lean::dec(x_1267);
 x_1273 = lean::box(0);
}
if (lean::is_scalar(x_1273)) {
 x_1274 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1274 = x_1273;
}
lean::cnstr_set(x_1274, 0, x_1271);
return x_1274;
}
else
{
obj* x_1275; obj* x_1277; obj* x_1278; obj* x_1280; obj* x_1282; obj* x_1283; obj* x_1284; obj* x_1285; obj* x_1286; obj* x_1287; obj* x_1288; 
x_1275 = lean::cnstr_get(x_1267, 0);
if (lean::is_exclusive(x_1267)) {
 lean::cnstr_set(x_1267, 0, lean::box(0));
 x_1277 = x_1267;
} else {
 lean::inc(x_1275);
 lean::dec(x_1267);
 x_1277 = lean::box(0);
}
x_1278 = lean::cnstr_get(x_1275, 0);
x_1280 = lean::cnstr_get(x_1275, 1);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_set(x_1275, 0, lean::box(0));
 lean::cnstr_set(x_1275, 1, lean::box(0));
 x_1282 = x_1275;
} else {
 lean::inc(x_1278);
 lean::inc(x_1280);
 lean::dec(x_1275);
 x_1282 = lean::box(0);
}
x_1283 = l_Lean_Parser_number_View_toNat___main(x_1263);
x_1284 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1284, 0, x_1283);
x_1285 = lean::box(0);
x_1286 = l_Lean_Elaborator_toPexpr___main___closed__37;
x_1287 = l_Lean_KVMap_insertCore___main(x_1285, x_1286, x_1284);
x_1288 = lean_expr_mk_mdata(x_1287, x_1278);
if (x_20 == 0)
{
obj* x_1289; 
x_1289 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1289) == 0)
{
obj* x_1292; obj* x_1293; 
lean::dec(x_2);
if (lean::is_scalar(x_1282)) {
 x_1292 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1292 = x_1282;
}
lean::cnstr_set(x_1292, 0, x_1288);
lean::cnstr_set(x_1292, 1, x_1280);
if (lean::is_scalar(x_1277)) {
 x_1293 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1293 = x_1277;
}
lean::cnstr_set(x_1293, 0, x_1292);
return x_1293;
}
else
{
obj* x_1294; obj* x_1297; obj* x_1300; obj* x_1303; obj* x_1304; obj* x_1306; obj* x_1307; obj* x_1308; obj* x_1311; obj* x_1312; obj* x_1313; obj* x_1314; obj* x_1315; 
x_1294 = lean::cnstr_get(x_1289, 0);
lean::inc(x_1294);
lean::dec(x_1289);
x_1297 = lean::cnstr_get(x_2, 0);
lean::inc(x_1297);
lean::dec(x_2);
x_1300 = lean::cnstr_get(x_1297, 2);
lean::inc(x_1300);
lean::dec(x_1297);
x_1303 = l_Lean_FileMap_toPosition(x_1300, x_1294);
x_1304 = lean::cnstr_get(x_1303, 1);
lean::inc(x_1304);
x_1306 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1307 = l_Lean_KVMap_setNat(x_1285, x_1306, x_1304);
x_1308 = lean::cnstr_get(x_1303, 0);
lean::inc(x_1308);
lean::dec(x_1303);
x_1311 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1312 = l_Lean_KVMap_setNat(x_1307, x_1311, x_1308);
x_1313 = lean_expr_mk_mdata(x_1312, x_1288);
if (lean::is_scalar(x_1282)) {
 x_1314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1314 = x_1282;
}
lean::cnstr_set(x_1314, 0, x_1313);
lean::cnstr_set(x_1314, 1, x_1280);
if (lean::is_scalar(x_1277)) {
 x_1315 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1315 = x_1277;
}
lean::cnstr_set(x_1315, 0, x_1314);
return x_1315;
}
}
else
{
obj* x_1318; obj* x_1319; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1282)) {
 x_1318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1318 = x_1282;
}
lean::cnstr_set(x_1318, 0, x_1288);
lean::cnstr_set(x_1318, 1, x_1280);
if (lean::is_scalar(x_1277)) {
 x_1319 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1319 = x_1277;
}
lean::cnstr_set(x_1319, 0, x_1318);
return x_1319;
}
}
}
}
}
else
{
obj* x_1321; obj* x_1322; obj* x_1326; obj* x_1327; 
lean::dec(x_10);
x_1321 = l_Lean_Parser_Term_let_HasView;
x_1322 = lean::cnstr_get(x_1321, 0);
lean::inc(x_1322);
lean::dec(x_1321);
lean::inc(x_0);
x_1326 = lean::apply_1(x_1322, x_0);
x_1327 = lean::cnstr_get(x_1326, 1);
lean::inc(x_1327);
if (lean::obj_tag(x_1327) == 0)
{
obj* x_1329; obj* x_1332; 
x_1329 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1329);
lean::dec(x_1327);
x_1332 = lean::cnstr_get(x_1329, 1);
lean::inc(x_1332);
if (lean::obj_tag(x_1332) == 0)
{
obj* x_1334; 
x_1334 = lean::cnstr_get(x_1329, 2);
lean::inc(x_1334);
if (lean::obj_tag(x_1334) == 0)
{
obj* x_1339; obj* x_1340; obj* x_1342; 
lean::dec(x_1329);
lean::dec(x_1326);
lean::inc(x_0);
x_1339 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1339, 0, x_0);
x_1340 = l_Lean_Elaborator_toPexpr___main___closed__38;
lean::inc(x_2);
x_1342 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1339, x_1340, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1339);
if (lean::obj_tag(x_1342) == 0)
{
obj* x_1348; obj* x_1350; obj* x_1351; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1348 = lean::cnstr_get(x_1342, 0);
if (lean::is_exclusive(x_1342)) {
 x_1350 = x_1342;
} else {
 lean::inc(x_1348);
 lean::dec(x_1342);
 x_1350 = lean::box(0);
}
if (lean::is_scalar(x_1350)) {
 x_1351 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1351 = x_1350;
}
lean::cnstr_set(x_1351, 0, x_1348);
return x_1351;
}
else
{
obj* x_1352; 
x_1352 = lean::cnstr_get(x_1342, 0);
lean::inc(x_1352);
lean::dec(x_1342);
x_15 = x_1352;
goto lbl_16;
}
}
else
{
obj* x_1355; obj* x_1358; obj* x_1361; obj* x_1365; 
x_1355 = lean::cnstr_get(x_1329, 0);
lean::inc(x_1355);
lean::dec(x_1329);
x_1358 = lean::cnstr_get(x_1334, 0);
lean::inc(x_1358);
lean::dec(x_1334);
x_1361 = lean::cnstr_get(x_1358, 1);
lean::inc(x_1361);
lean::dec(x_1358);
lean::inc(x_2);
x_1365 = l_Lean_Elaborator_toPexpr___main(x_1361, x_1, x_2, x_3);
if (lean::obj_tag(x_1365) == 0)
{
obj* x_1371; obj* x_1373; obj* x_1374; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1355);
lean::dec(x_1326);
x_1371 = lean::cnstr_get(x_1365, 0);
if (lean::is_exclusive(x_1365)) {
 x_1373 = x_1365;
} else {
 lean::inc(x_1371);
 lean::dec(x_1365);
 x_1373 = lean::box(0);
}
if (lean::is_scalar(x_1373)) {
 x_1374 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1374 = x_1373;
}
lean::cnstr_set(x_1374, 0, x_1371);
return x_1374;
}
else
{
obj* x_1375; obj* x_1378; obj* x_1380; obj* x_1383; obj* x_1386; 
x_1375 = lean::cnstr_get(x_1365, 0);
lean::inc(x_1375);
lean::dec(x_1365);
x_1378 = lean::cnstr_get(x_1375, 0);
lean::inc(x_1378);
x_1380 = lean::cnstr_get(x_1375, 1);
lean::inc(x_1380);
lean::dec(x_1375);
x_1383 = lean::cnstr_get(x_1326, 3);
lean::inc(x_1383);
lean::inc(x_2);
x_1386 = l_Lean_Elaborator_toPexpr___main(x_1383, x_1, x_2, x_1380);
if (lean::obj_tag(x_1386) == 0)
{
obj* x_1393; obj* x_1395; obj* x_1396; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1355);
lean::dec(x_1378);
lean::dec(x_1326);
x_1393 = lean::cnstr_get(x_1386, 0);
if (lean::is_exclusive(x_1386)) {
 x_1395 = x_1386;
} else {
 lean::inc(x_1393);
 lean::dec(x_1386);
 x_1395 = lean::box(0);
}
if (lean::is_scalar(x_1395)) {
 x_1396 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1396 = x_1395;
}
lean::cnstr_set(x_1396, 0, x_1393);
return x_1396;
}
else
{
obj* x_1397; obj* x_1400; obj* x_1402; obj* x_1405; obj* x_1409; 
x_1397 = lean::cnstr_get(x_1386, 0);
lean::inc(x_1397);
lean::dec(x_1386);
x_1400 = lean::cnstr_get(x_1397, 0);
lean::inc(x_1400);
x_1402 = lean::cnstr_get(x_1397, 1);
lean::inc(x_1402);
lean::dec(x_1397);
x_1405 = lean::cnstr_get(x_1326, 5);
lean::inc(x_1405);
lean::dec(x_1326);
lean::inc(x_2);
x_1409 = l_Lean_Elaborator_toPexpr___main(x_1405, x_1, x_2, x_1402);
if (lean::obj_tag(x_1409) == 0)
{
obj* x_1416; obj* x_1418; obj* x_1419; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1355);
lean::dec(x_1400);
lean::dec(x_1378);
x_1416 = lean::cnstr_get(x_1409, 0);
if (lean::is_exclusive(x_1409)) {
 x_1418 = x_1409;
} else {
 lean::inc(x_1416);
 lean::dec(x_1409);
 x_1418 = lean::box(0);
}
if (lean::is_scalar(x_1418)) {
 x_1419 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1419 = x_1418;
}
lean::cnstr_set(x_1419, 0, x_1416);
return x_1419;
}
else
{
obj* x_1420; obj* x_1423; obj* x_1425; obj* x_1427; obj* x_1428; obj* x_1429; obj* x_1430; 
x_1420 = lean::cnstr_get(x_1409, 0);
lean::inc(x_1420);
lean::dec(x_1409);
x_1423 = lean::cnstr_get(x_1420, 0);
x_1425 = lean::cnstr_get(x_1420, 1);
if (lean::is_exclusive(x_1420)) {
 x_1427 = x_1420;
} else {
 lean::inc(x_1423);
 lean::inc(x_1425);
 lean::dec(x_1420);
 x_1427 = lean::box(0);
}
x_1428 = l_Lean_Elaborator_mangleIdent(x_1355);
x_1429 = lean_expr_mk_let(x_1428, x_1378, x_1400, x_1423);
if (lean::is_scalar(x_1427)) {
 x_1430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1430 = x_1427;
}
lean::cnstr_set(x_1430, 0, x_1429);
lean::cnstr_set(x_1430, 1, x_1425);
x_15 = x_1430;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1435; obj* x_1436; obj* x_1438; 
lean::dec(x_1332);
lean::dec(x_1329);
lean::dec(x_1326);
lean::inc(x_0);
x_1435 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1435, 0, x_0);
x_1436 = l_Lean_Elaborator_toPexpr___main___closed__38;
lean::inc(x_2);
x_1438 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1435, x_1436, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1435);
if (lean::obj_tag(x_1438) == 0)
{
obj* x_1444; obj* x_1446; obj* x_1447; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1444 = lean::cnstr_get(x_1438, 0);
if (lean::is_exclusive(x_1438)) {
 x_1446 = x_1438;
} else {
 lean::inc(x_1444);
 lean::dec(x_1438);
 x_1446 = lean::box(0);
}
if (lean::is_scalar(x_1446)) {
 x_1447 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1447 = x_1446;
}
lean::cnstr_set(x_1447, 0, x_1444);
return x_1447;
}
else
{
obj* x_1448; 
x_1448 = lean::cnstr_get(x_1438, 0);
lean::inc(x_1448);
lean::dec(x_1438);
x_15 = x_1448;
goto lbl_16;
}
}
}
else
{
obj* x_1454; obj* x_1455; obj* x_1457; 
lean::dec(x_1326);
lean::dec(x_1327);
lean::inc(x_0);
x_1454 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1454, 0, x_0);
x_1455 = l_Lean_Elaborator_toPexpr___main___closed__38;
lean::inc(x_2);
x_1457 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1454, x_1455, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1454);
if (lean::obj_tag(x_1457) == 0)
{
obj* x_1463; obj* x_1465; obj* x_1466; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1463 = lean::cnstr_get(x_1457, 0);
if (lean::is_exclusive(x_1457)) {
 x_1465 = x_1457;
} else {
 lean::inc(x_1463);
 lean::dec(x_1457);
 x_1465 = lean::box(0);
}
if (lean::is_scalar(x_1465)) {
 x_1466 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1466 = x_1465;
}
lean::cnstr_set(x_1466, 0, x_1463);
return x_1466;
}
else
{
obj* x_1467; 
x_1467 = lean::cnstr_get(x_1457, 0);
lean::inc(x_1467);
lean::dec(x_1457);
x_15 = x_1467;
goto lbl_16;
}
}
}
}
else
{
obj* x_1472; obj* x_1473; obj* x_1477; obj* x_1478; obj* x_1481; 
lean::dec(x_8);
lean::dec(x_10);
x_1472 = l_Lean_Parser_Term_show_HasView;
x_1473 = lean::cnstr_get(x_1472, 0);
lean::inc(x_1473);
lean::dec(x_1472);
lean::inc(x_0);
x_1477 = lean::apply_1(x_1473, x_0);
x_1478 = lean::cnstr_get(x_1477, 1);
lean::inc(x_1478);
lean::inc(x_2);
x_1481 = l_Lean_Elaborator_toPexpr___main(x_1478, x_1, x_2, x_3);
if (lean::obj_tag(x_1481) == 0)
{
obj* x_1485; obj* x_1487; obj* x_1488; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1477);
x_1485 = lean::cnstr_get(x_1481, 0);
if (lean::is_exclusive(x_1481)) {
 x_1487 = x_1481;
} else {
 lean::inc(x_1485);
 lean::dec(x_1481);
 x_1487 = lean::box(0);
}
if (lean::is_scalar(x_1487)) {
 x_1488 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1488 = x_1487;
}
lean::cnstr_set(x_1488, 0, x_1485);
return x_1488;
}
else
{
obj* x_1489; obj* x_1492; obj* x_1494; obj* x_1497; obj* x_1500; obj* x_1504; 
x_1489 = lean::cnstr_get(x_1481, 0);
lean::inc(x_1489);
lean::dec(x_1481);
x_1492 = lean::cnstr_get(x_1489, 0);
lean::inc(x_1492);
x_1494 = lean::cnstr_get(x_1489, 1);
lean::inc(x_1494);
lean::dec(x_1489);
x_1497 = lean::cnstr_get(x_1477, 3);
lean::inc(x_1497);
lean::dec(x_1477);
x_1500 = lean::cnstr_get(x_1497, 1);
lean::inc(x_1500);
lean::dec(x_1497);
lean::inc(x_2);
x_1504 = l_Lean_Elaborator_toPexpr___main(x_1500, x_1, x_2, x_1494);
if (lean::obj_tag(x_1504) == 0)
{
obj* x_1508; obj* x_1510; obj* x_1511; 
lean::dec(x_1492);
lean::dec(x_0);
lean::dec(x_2);
x_1508 = lean::cnstr_get(x_1504, 0);
if (lean::is_exclusive(x_1504)) {
 x_1510 = x_1504;
} else {
 lean::inc(x_1508);
 lean::dec(x_1504);
 x_1510 = lean::box(0);
}
if (lean::is_scalar(x_1510)) {
 x_1511 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1511 = x_1510;
}
lean::cnstr_set(x_1511, 0, x_1508);
return x_1511;
}
else
{
obj* x_1512; obj* x_1514; obj* x_1515; obj* x_1517; obj* x_1519; obj* x_1520; uint8 x_1521; obj* x_1522; obj* x_1523; obj* x_1524; obj* x_1525; obj* x_1526; 
x_1512 = lean::cnstr_get(x_1504, 0);
if (lean::is_exclusive(x_1504)) {
 lean::cnstr_set(x_1504, 0, lean::box(0));
 x_1514 = x_1504;
} else {
 lean::inc(x_1512);
 lean::dec(x_1504);
 x_1514 = lean::box(0);
}
x_1515 = lean::cnstr_get(x_1512, 0);
x_1517 = lean::cnstr_get(x_1512, 1);
if (lean::is_exclusive(x_1512)) {
 lean::cnstr_set(x_1512, 0, lean::box(0));
 lean::cnstr_set(x_1512, 1, lean::box(0));
 x_1519 = x_1512;
} else {
 lean::inc(x_1515);
 lean::inc(x_1517);
 lean::dec(x_1512);
 x_1519 = lean::box(0);
}
x_1520 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1521 = 0;
x_1522 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1523 = lean_expr_mk_lambda(x_1520, x_1521, x_1492, x_1522);
x_1524 = lean_expr_mk_app(x_1523, x_1515);
x_1525 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1526 = l_Lean_Elaborator_Expr_mkAnnotation(x_1525, x_1524);
if (x_20 == 0)
{
obj* x_1527; 
x_1527 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1527) == 0)
{
obj* x_1530; obj* x_1531; 
lean::dec(x_2);
if (lean::is_scalar(x_1519)) {
 x_1530 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1530 = x_1519;
}
lean::cnstr_set(x_1530, 0, x_1526);
lean::cnstr_set(x_1530, 1, x_1517);
if (lean::is_scalar(x_1514)) {
 x_1531 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1531 = x_1514;
}
lean::cnstr_set(x_1531, 0, x_1530);
return x_1531;
}
else
{
obj* x_1532; obj* x_1535; obj* x_1538; obj* x_1541; obj* x_1542; obj* x_1544; obj* x_1545; obj* x_1546; obj* x_1547; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1554; 
x_1532 = lean::cnstr_get(x_1527, 0);
lean::inc(x_1532);
lean::dec(x_1527);
x_1535 = lean::cnstr_get(x_2, 0);
lean::inc(x_1535);
lean::dec(x_2);
x_1538 = lean::cnstr_get(x_1535, 2);
lean::inc(x_1538);
lean::dec(x_1535);
x_1541 = l_Lean_FileMap_toPosition(x_1538, x_1532);
x_1542 = lean::cnstr_get(x_1541, 1);
lean::inc(x_1542);
x_1544 = lean::box(0);
x_1545 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1546 = l_Lean_KVMap_setNat(x_1544, x_1545, x_1542);
x_1547 = lean::cnstr_get(x_1541, 0);
lean::inc(x_1547);
lean::dec(x_1541);
x_1550 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1551 = l_Lean_KVMap_setNat(x_1546, x_1550, x_1547);
x_1552 = lean_expr_mk_mdata(x_1551, x_1526);
if (lean::is_scalar(x_1519)) {
 x_1553 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1553 = x_1519;
}
lean::cnstr_set(x_1553, 0, x_1552);
lean::cnstr_set(x_1553, 1, x_1517);
if (lean::is_scalar(x_1514)) {
 x_1554 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1554 = x_1514;
}
lean::cnstr_set(x_1554, 0, x_1553);
return x_1554;
}
}
else
{
obj* x_1557; obj* x_1558; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1519)) {
 x_1557 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1557 = x_1519;
}
lean::cnstr_set(x_1557, 0, x_1526);
lean::cnstr_set(x_1557, 1, x_1517);
if (lean::is_scalar(x_1514)) {
 x_1558 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1558 = x_1514;
}
lean::cnstr_set(x_1558, 0, x_1557);
return x_1558;
}
}
}
}
}
else
{
obj* x_1560; obj* x_1561; obj* x_1565; obj* x_1566; 
lean::dec(x_10);
x_1560 = l_Lean_Parser_Term_have_HasView;
x_1561 = lean::cnstr_get(x_1560, 0);
lean::inc(x_1561);
lean::dec(x_1560);
lean::inc(x_0);
x_1565 = lean::apply_1(x_1561, x_0);
x_1566 = lean::cnstr_get(x_1565, 1);
lean::inc(x_1566);
if (lean::obj_tag(x_1566) == 0)
{
obj* x_1568; obj* x_1570; obj* x_1573; 
x_1568 = lean::cnstr_get(x_1565, 2);
lean::inc(x_1568);
x_1570 = lean::cnstr_get(x_1565, 5);
lean::inc(x_1570);
lean::inc(x_2);
x_1573 = l_Lean_Elaborator_toPexpr___main(x_1568, x_1, x_2, x_3);
if (lean::obj_tag(x_1573) == 0)
{
obj* x_1579; obj* x_1581; obj* x_1582; 
lean::dec(x_1570);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1565);
x_1579 = lean::cnstr_get(x_1573, 0);
if (lean::is_exclusive(x_1573)) {
 x_1581 = x_1573;
} else {
 lean::inc(x_1579);
 lean::dec(x_1573);
 x_1581 = lean::box(0);
}
if (lean::is_scalar(x_1581)) {
 x_1582 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1582 = x_1581;
}
lean::cnstr_set(x_1582, 0, x_1579);
return x_1582;
}
else
{
obj* x_1583; obj* x_1586; obj* x_1588; obj* x_1592; 
x_1583 = lean::cnstr_get(x_1573, 0);
lean::inc(x_1583);
lean::dec(x_1573);
x_1586 = lean::cnstr_get(x_1583, 0);
lean::inc(x_1586);
x_1588 = lean::cnstr_get(x_1583, 1);
lean::inc(x_1588);
lean::dec(x_1583);
lean::inc(x_2);
x_1592 = l_Lean_Elaborator_toPexpr___main(x_1570, x_1, x_2, x_1588);
if (lean::obj_tag(x_1592) == 0)
{
obj* x_1598; obj* x_1600; obj* x_1601; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1565);
lean::dec(x_1586);
x_1598 = lean::cnstr_get(x_1592, 0);
if (lean::is_exclusive(x_1592)) {
 x_1600 = x_1592;
} else {
 lean::inc(x_1598);
 lean::dec(x_1592);
 x_1600 = lean::box(0);
}
if (lean::is_scalar(x_1600)) {
 x_1601 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1601 = x_1600;
}
lean::cnstr_set(x_1601, 0, x_1598);
return x_1601;
}
else
{
obj* x_1602; obj* x_1605; obj* x_1607; obj* x_1610; uint8 x_1611; obj* x_1612; obj* x_1613; 
x_1602 = lean::cnstr_get(x_1592, 0);
lean::inc(x_1602);
lean::dec(x_1592);
x_1605 = lean::cnstr_get(x_1602, 0);
lean::inc(x_1605);
x_1607 = lean::cnstr_get(x_1602, 1);
lean::inc(x_1607);
lean::dec(x_1602);
x_1610 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_1611 = 0;
x_1612 = lean_expr_mk_lambda(x_1610, x_1611, x_1586, x_1605);
x_1613 = lean::cnstr_get(x_1565, 3);
lean::inc(x_1613);
lean::dec(x_1565);
if (lean::obj_tag(x_1613) == 0)
{
obj* x_1616; obj* x_1619; obj* x_1623; 
x_1616 = lean::cnstr_get(x_1613, 0);
lean::inc(x_1616);
lean::dec(x_1613);
x_1619 = lean::cnstr_get(x_1616, 1);
lean::inc(x_1619);
lean::dec(x_1616);
lean::inc(x_2);
x_1623 = l_Lean_Elaborator_toPexpr___main(x_1619, x_1, x_2, x_1607);
if (lean::obj_tag(x_1623) == 0)
{
obj* x_1628; obj* x_1630; obj* x_1631; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1612);
x_1628 = lean::cnstr_get(x_1623, 0);
if (lean::is_exclusive(x_1623)) {
 x_1630 = x_1623;
} else {
 lean::inc(x_1628);
 lean::dec(x_1623);
 x_1630 = lean::box(0);
}
if (lean::is_scalar(x_1630)) {
 x_1631 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1631 = x_1630;
}
lean::cnstr_set(x_1631, 0, x_1628);
return x_1631;
}
else
{
obj* x_1632; obj* x_1635; obj* x_1637; obj* x_1639; obj* x_1640; obj* x_1641; obj* x_1642; obj* x_1643; 
x_1632 = lean::cnstr_get(x_1623, 0);
lean::inc(x_1632);
lean::dec(x_1623);
x_1635 = lean::cnstr_get(x_1632, 0);
x_1637 = lean::cnstr_get(x_1632, 1);
if (lean::is_exclusive(x_1632)) {
 x_1639 = x_1632;
} else {
 lean::inc(x_1635);
 lean::inc(x_1637);
 lean::dec(x_1632);
 x_1639 = lean::box(0);
}
x_1640 = l_Lean_Elaborator_toPexpr___main___closed__43;
x_1641 = l_Lean_Elaborator_Expr_mkAnnotation(x_1640, x_1612);
x_1642 = lean_expr_mk_app(x_1641, x_1635);
if (lean::is_scalar(x_1639)) {
 x_1643 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1643 = x_1639;
}
lean::cnstr_set(x_1643, 0, x_1642);
lean::cnstr_set(x_1643, 1, x_1637);
x_15 = x_1643;
goto lbl_16;
}
}
else
{
obj* x_1644; obj* x_1647; obj* x_1650; obj* x_1654; 
x_1644 = lean::cnstr_get(x_1613, 0);
lean::inc(x_1644);
lean::dec(x_1613);
x_1647 = lean::cnstr_get(x_1644, 1);
lean::inc(x_1647);
lean::dec(x_1644);
x_1650 = lean::cnstr_get(x_1647, 1);
lean::inc(x_1650);
lean::dec(x_1647);
lean::inc(x_2);
x_1654 = l_Lean_Elaborator_toPexpr___main(x_1650, x_1, x_2, x_1607);
if (lean::obj_tag(x_1654) == 0)
{
obj* x_1659; obj* x_1661; obj* x_1662; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1612);
x_1659 = lean::cnstr_get(x_1654, 0);
if (lean::is_exclusive(x_1654)) {
 x_1661 = x_1654;
} else {
 lean::inc(x_1659);
 lean::dec(x_1654);
 x_1661 = lean::box(0);
}
if (lean::is_scalar(x_1661)) {
 x_1662 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1662 = x_1661;
}
lean::cnstr_set(x_1662, 0, x_1659);
return x_1662;
}
else
{
obj* x_1663; obj* x_1666; obj* x_1668; obj* x_1670; obj* x_1671; obj* x_1672; obj* x_1673; obj* x_1674; 
x_1663 = lean::cnstr_get(x_1654, 0);
lean::inc(x_1663);
lean::dec(x_1654);
x_1666 = lean::cnstr_get(x_1663, 0);
x_1668 = lean::cnstr_get(x_1663, 1);
if (lean::is_exclusive(x_1663)) {
 x_1670 = x_1663;
} else {
 lean::inc(x_1666);
 lean::inc(x_1668);
 lean::dec(x_1663);
 x_1670 = lean::box(0);
}
x_1671 = l_Lean_Elaborator_toPexpr___main___closed__43;
x_1672 = l_Lean_Elaborator_Expr_mkAnnotation(x_1671, x_1612);
x_1673 = lean_expr_mk_app(x_1672, x_1666);
if (lean::is_scalar(x_1670)) {
 x_1674 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1674 = x_1670;
}
lean::cnstr_set(x_1674, 0, x_1673);
lean::cnstr_set(x_1674, 1, x_1668);
x_15 = x_1674;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1675; obj* x_1677; obj* x_1679; obj* x_1681; obj* x_1683; 
x_1675 = lean::cnstr_get(x_1565, 2);
lean::inc(x_1675);
x_1677 = lean::cnstr_get(x_1565, 5);
lean::inc(x_1677);
x_1679 = lean::cnstr_get(x_1566, 0);
if (lean::is_exclusive(x_1566)) {
 lean::cnstr_set(x_1566, 0, lean::box(0));
 x_1681 = x_1566;
} else {
 lean::inc(x_1679);
 lean::dec(x_1566);
 x_1681 = lean::box(0);
}
lean::inc(x_2);
x_1683 = l_Lean_Elaborator_toPexpr___main(x_1675, x_1, x_2, x_3);
if (lean::obj_tag(x_1683) == 0)
{
obj* x_1691; obj* x_1693; obj* x_1694; 
lean::dec(x_1681);
lean::dec(x_1677);
lean::dec(x_1679);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1565);
x_1691 = lean::cnstr_get(x_1683, 0);
if (lean::is_exclusive(x_1683)) {
 x_1693 = x_1683;
} else {
 lean::inc(x_1691);
 lean::dec(x_1683);
 x_1693 = lean::box(0);
}
if (lean::is_scalar(x_1693)) {
 x_1694 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1694 = x_1693;
}
lean::cnstr_set(x_1694, 0, x_1691);
return x_1694;
}
else
{
obj* x_1695; obj* x_1698; obj* x_1700; obj* x_1704; 
x_1695 = lean::cnstr_get(x_1683, 0);
lean::inc(x_1695);
lean::dec(x_1683);
x_1698 = lean::cnstr_get(x_1695, 0);
lean::inc(x_1698);
x_1700 = lean::cnstr_get(x_1695, 1);
lean::inc(x_1700);
lean::dec(x_1695);
lean::inc(x_2);
x_1704 = l_Lean_Elaborator_toPexpr___main(x_1677, x_1, x_2, x_1700);
if (lean::obj_tag(x_1704) == 0)
{
obj* x_1712; obj* x_1714; obj* x_1715; 
lean::dec(x_1681);
lean::dec(x_1679);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1565);
lean::dec(x_1698);
x_1712 = lean::cnstr_get(x_1704, 0);
if (lean::is_exclusive(x_1704)) {
 x_1714 = x_1704;
} else {
 lean::inc(x_1712);
 lean::dec(x_1704);
 x_1714 = lean::box(0);
}
if (lean::is_scalar(x_1714)) {
 x_1715 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1715 = x_1714;
}
lean::cnstr_set(x_1715, 0, x_1712);
return x_1715;
}
else
{
obj* x_1716; obj* x_1719; obj* x_1721; obj* x_1724; obj* x_1727; obj* x_1728; obj* x_1729; obj* x_1730; uint8 x_1732; obj* x_1733; obj* x_1734; 
x_1716 = lean::cnstr_get(x_1704, 0);
lean::inc(x_1716);
lean::dec(x_1704);
x_1719 = lean::cnstr_get(x_1716, 0);
lean::inc(x_1719);
x_1721 = lean::cnstr_get(x_1716, 1);
lean::inc(x_1721);
lean::dec(x_1716);
x_1724 = lean::cnstr_get(x_1679, 0);
lean::inc(x_1724);
lean::dec(x_1679);
x_1727 = l_Lean_Elaborator_mangleIdent(x_1724);
if (lean::is_scalar(x_1681)) {
 x_1728 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1728 = x_1681;
}
lean::cnstr_set(x_1728, 0, x_1727);
x_1729 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1730 = l_Option_getOrElse___main___rarg(x_1728, x_1729);
lean::dec(x_1728);
x_1732 = 0;
x_1733 = lean_expr_mk_lambda(x_1730, x_1732, x_1698, x_1719);
x_1734 = lean::cnstr_get(x_1565, 3);
lean::inc(x_1734);
lean::dec(x_1565);
if (lean::obj_tag(x_1734) == 0)
{
obj* x_1737; obj* x_1740; obj* x_1744; 
x_1737 = lean::cnstr_get(x_1734, 0);
lean::inc(x_1737);
lean::dec(x_1734);
x_1740 = lean::cnstr_get(x_1737, 1);
lean::inc(x_1740);
lean::dec(x_1737);
lean::inc(x_2);
x_1744 = l_Lean_Elaborator_toPexpr___main(x_1740, x_1, x_2, x_1721);
if (lean::obj_tag(x_1744) == 0)
{
obj* x_1749; obj* x_1751; obj* x_1752; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1733);
x_1749 = lean::cnstr_get(x_1744, 0);
if (lean::is_exclusive(x_1744)) {
 x_1751 = x_1744;
} else {
 lean::inc(x_1749);
 lean::dec(x_1744);
 x_1751 = lean::box(0);
}
if (lean::is_scalar(x_1751)) {
 x_1752 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1752 = x_1751;
}
lean::cnstr_set(x_1752, 0, x_1749);
return x_1752;
}
else
{
obj* x_1753; obj* x_1756; obj* x_1758; obj* x_1760; obj* x_1761; obj* x_1762; obj* x_1763; obj* x_1764; 
x_1753 = lean::cnstr_get(x_1744, 0);
lean::inc(x_1753);
lean::dec(x_1744);
x_1756 = lean::cnstr_get(x_1753, 0);
x_1758 = lean::cnstr_get(x_1753, 1);
if (lean::is_exclusive(x_1753)) {
 x_1760 = x_1753;
} else {
 lean::inc(x_1756);
 lean::inc(x_1758);
 lean::dec(x_1753);
 x_1760 = lean::box(0);
}
x_1761 = l_Lean_Elaborator_toPexpr___main___closed__43;
x_1762 = l_Lean_Elaborator_Expr_mkAnnotation(x_1761, x_1733);
x_1763 = lean_expr_mk_app(x_1762, x_1756);
if (lean::is_scalar(x_1760)) {
 x_1764 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1764 = x_1760;
}
lean::cnstr_set(x_1764, 0, x_1763);
lean::cnstr_set(x_1764, 1, x_1758);
x_15 = x_1764;
goto lbl_16;
}
}
else
{
obj* x_1765; obj* x_1768; obj* x_1771; obj* x_1775; 
x_1765 = lean::cnstr_get(x_1734, 0);
lean::inc(x_1765);
lean::dec(x_1734);
x_1768 = lean::cnstr_get(x_1765, 1);
lean::inc(x_1768);
lean::dec(x_1765);
x_1771 = lean::cnstr_get(x_1768, 1);
lean::inc(x_1771);
lean::dec(x_1768);
lean::inc(x_2);
x_1775 = l_Lean_Elaborator_toPexpr___main(x_1771, x_1, x_2, x_1721);
if (lean::obj_tag(x_1775) == 0)
{
obj* x_1780; obj* x_1782; obj* x_1783; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1733);
x_1780 = lean::cnstr_get(x_1775, 0);
if (lean::is_exclusive(x_1775)) {
 x_1782 = x_1775;
} else {
 lean::inc(x_1780);
 lean::dec(x_1775);
 x_1782 = lean::box(0);
}
if (lean::is_scalar(x_1782)) {
 x_1783 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1783 = x_1782;
}
lean::cnstr_set(x_1783, 0, x_1780);
return x_1783;
}
else
{
obj* x_1784; obj* x_1787; obj* x_1789; obj* x_1791; obj* x_1792; obj* x_1793; obj* x_1794; obj* x_1795; 
x_1784 = lean::cnstr_get(x_1775, 0);
lean::inc(x_1784);
lean::dec(x_1775);
x_1787 = lean::cnstr_get(x_1784, 0);
x_1789 = lean::cnstr_get(x_1784, 1);
if (lean::is_exclusive(x_1784)) {
 x_1791 = x_1784;
} else {
 lean::inc(x_1787);
 lean::inc(x_1789);
 lean::dec(x_1784);
 x_1791 = lean::box(0);
}
x_1792 = l_Lean_Elaborator_toPexpr___main___closed__43;
x_1793 = l_Lean_Elaborator_Expr_mkAnnotation(x_1792, x_1733);
x_1794 = lean_expr_mk_app(x_1793, x_1787);
if (lean::is_scalar(x_1791)) {
 x_1795 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1795 = x_1791;
}
lean::cnstr_set(x_1795, 0, x_1794);
lean::cnstr_set(x_1795, 1, x_1789);
x_15 = x_1795;
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
obj* x_1798; 
x_1798 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1798) == 0)
{
obj* x_1801; obj* x_1802; obj* x_1803; 
lean::dec(x_2);
x_1801 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_1802 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1802, 0, x_1801);
lean::cnstr_set(x_1802, 1, x_3);
x_1803 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1803, 0, x_1802);
return x_1803;
}
else
{
obj* x_1804; obj* x_1807; obj* x_1810; obj* x_1813; obj* x_1814; obj* x_1816; obj* x_1817; obj* x_1818; obj* x_1819; obj* x_1822; obj* x_1823; obj* x_1824; obj* x_1825; obj* x_1826; obj* x_1827; 
x_1804 = lean::cnstr_get(x_1798, 0);
lean::inc(x_1804);
lean::dec(x_1798);
x_1807 = lean::cnstr_get(x_2, 0);
lean::inc(x_1807);
lean::dec(x_2);
x_1810 = lean::cnstr_get(x_1807, 2);
lean::inc(x_1810);
lean::dec(x_1807);
x_1813 = l_Lean_FileMap_toPosition(x_1810, x_1804);
x_1814 = lean::cnstr_get(x_1813, 1);
lean::inc(x_1814);
x_1816 = lean::box(0);
x_1817 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1818 = l_Lean_KVMap_setNat(x_1816, x_1817, x_1814);
x_1819 = lean::cnstr_get(x_1813, 0);
lean::inc(x_1819);
lean::dec(x_1813);
x_1822 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1823 = l_Lean_KVMap_setNat(x_1818, x_1822, x_1819);
x_1824 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_1825 = lean_expr_mk_mdata(x_1823, x_1824);
x_1826 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1826, 0, x_1825);
lean::cnstr_set(x_1826, 1, x_3);
x_1827 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1827, 0, x_1826);
return x_1827;
}
}
else
{
obj* x_1830; obj* x_1831; obj* x_1832; 
lean::dec(x_0);
lean::dec(x_2);
x_1830 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_1831 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1831, 0, x_1830);
lean::cnstr_set(x_1831, 1, x_3);
x_1832 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1832, 0, x_1831);
return x_1832;
}
}
}
else
{
obj* x_1835; obj* x_1836; obj* x_1840; obj* x_1841; obj* x_1844; obj* x_1845; obj* x_1846; obj* x_1848; 
lean::dec(x_8);
lean::dec(x_10);
x_1835 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_1836 = lean::cnstr_get(x_1835, 0);
lean::inc(x_1836);
lean::dec(x_1835);
lean::inc(x_0);
x_1840 = lean::apply_1(x_1836, x_0);
x_1841 = lean::cnstr_get(x_1840, 1);
lean::inc(x_1841);
lean::dec(x_1840);
x_1844 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__19(x_1841);
x_1845 = l_Lean_Expander_getOptType___main___closed__1;
x_1846 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_1845, x_1844);
lean::inc(x_2);
x_1848 = l_Lean_Elaborator_toPexpr___main(x_1846, x_1, x_2, x_3);
if (lean::obj_tag(x_1848) == 0)
{
obj* x_1851; obj* x_1853; obj* x_1854; 
lean::dec(x_0);
lean::dec(x_2);
x_1851 = lean::cnstr_get(x_1848, 0);
if (lean::is_exclusive(x_1848)) {
 x_1853 = x_1848;
} else {
 lean::inc(x_1851);
 lean::dec(x_1848);
 x_1853 = lean::box(0);
}
if (lean::is_scalar(x_1853)) {
 x_1854 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1854 = x_1853;
}
lean::cnstr_set(x_1854, 0, x_1851);
return x_1854;
}
else
{
obj* x_1855; obj* x_1857; obj* x_1858; obj* x_1860; obj* x_1862; obj* x_1863; obj* x_1864; 
x_1855 = lean::cnstr_get(x_1848, 0);
if (lean::is_exclusive(x_1848)) {
 lean::cnstr_set(x_1848, 0, lean::box(0));
 x_1857 = x_1848;
} else {
 lean::inc(x_1855);
 lean::dec(x_1848);
 x_1857 = lean::box(0);
}
x_1858 = lean::cnstr_get(x_1855, 0);
x_1860 = lean::cnstr_get(x_1855, 1);
if (lean::is_exclusive(x_1855)) {
 lean::cnstr_set(x_1855, 0, lean::box(0));
 lean::cnstr_set(x_1855, 1, lean::box(0));
 x_1862 = x_1855;
} else {
 lean::inc(x_1858);
 lean::inc(x_1860);
 lean::dec(x_1855);
 x_1862 = lean::box(0);
}
x_1863 = l_Lean_Elaborator_toPexpr___main___closed__45;
x_1864 = l_Lean_Elaborator_Expr_mkAnnotation(x_1863, x_1858);
if (x_20 == 0)
{
obj* x_1865; 
x_1865 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1865) == 0)
{
obj* x_1868; obj* x_1869; 
lean::dec(x_2);
if (lean::is_scalar(x_1862)) {
 x_1868 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1868 = x_1862;
}
lean::cnstr_set(x_1868, 0, x_1864);
lean::cnstr_set(x_1868, 1, x_1860);
if (lean::is_scalar(x_1857)) {
 x_1869 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1869 = x_1857;
}
lean::cnstr_set(x_1869, 0, x_1868);
return x_1869;
}
else
{
obj* x_1870; obj* x_1873; obj* x_1876; obj* x_1879; obj* x_1880; obj* x_1882; obj* x_1883; obj* x_1884; obj* x_1885; obj* x_1888; obj* x_1889; obj* x_1890; obj* x_1891; obj* x_1892; 
x_1870 = lean::cnstr_get(x_1865, 0);
lean::inc(x_1870);
lean::dec(x_1865);
x_1873 = lean::cnstr_get(x_2, 0);
lean::inc(x_1873);
lean::dec(x_2);
x_1876 = lean::cnstr_get(x_1873, 2);
lean::inc(x_1876);
lean::dec(x_1873);
x_1879 = l_Lean_FileMap_toPosition(x_1876, x_1870);
x_1880 = lean::cnstr_get(x_1879, 1);
lean::inc(x_1880);
x_1882 = lean::box(0);
x_1883 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1884 = l_Lean_KVMap_setNat(x_1882, x_1883, x_1880);
x_1885 = lean::cnstr_get(x_1879, 0);
lean::inc(x_1885);
lean::dec(x_1879);
x_1888 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1889 = l_Lean_KVMap_setNat(x_1884, x_1888, x_1885);
x_1890 = lean_expr_mk_mdata(x_1889, x_1864);
if (lean::is_scalar(x_1862)) {
 x_1891 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1891 = x_1862;
}
lean::cnstr_set(x_1891, 0, x_1890);
lean::cnstr_set(x_1891, 1, x_1860);
if (lean::is_scalar(x_1857)) {
 x_1892 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1892 = x_1857;
}
lean::cnstr_set(x_1892, 0, x_1891);
return x_1892;
}
}
else
{
obj* x_1895; obj* x_1896; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1862)) {
 x_1895 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1895 = x_1862;
}
lean::cnstr_set(x_1895, 0, x_1864);
lean::cnstr_set(x_1895, 1, x_1860);
if (lean::is_scalar(x_1857)) {
 x_1896 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1896 = x_1857;
}
lean::cnstr_set(x_1896, 0, x_1895);
return x_1896;
}
}
}
}
else
{
obj* x_1899; obj* x_1900; obj* x_1904; obj* x_1905; obj* x_1906; obj* x_1909; obj* x_1911; 
lean::dec(x_8);
lean::dec(x_10);
x_1899 = l_Lean_Parser_Term_sortApp_HasView;
x_1900 = lean::cnstr_get(x_1899, 0);
lean::inc(x_1900);
lean::dec(x_1899);
lean::inc(x_0);
x_1904 = lean::apply_1(x_1900, x_0);
x_1905 = l_Lean_Parser_Term_sort_HasView;
x_1906 = lean::cnstr_get(x_1905, 0);
lean::inc(x_1906);
lean::dec(x_1905);
x_1909 = lean::cnstr_get(x_1904, 0);
lean::inc(x_1909);
x_1911 = lean::apply_1(x_1906, x_1909);
if (lean::obj_tag(x_1911) == 0)
{
obj* x_1913; obj* x_1917; 
lean::dec(x_1911);
x_1913 = lean::cnstr_get(x_1904, 1);
lean::inc(x_1913);
lean::dec(x_1904);
lean::inc(x_2);
x_1917 = l_Lean_Elaborator_toLevel___main(x_1913, x_1, x_2, x_3);
if (lean::obj_tag(x_1917) == 0)
{
obj* x_1920; obj* x_1922; obj* x_1923; 
lean::dec(x_0);
lean::dec(x_2);
x_1920 = lean::cnstr_get(x_1917, 0);
if (lean::is_exclusive(x_1917)) {
 x_1922 = x_1917;
} else {
 lean::inc(x_1920);
 lean::dec(x_1917);
 x_1922 = lean::box(0);
}
if (lean::is_scalar(x_1922)) {
 x_1923 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1923 = x_1922;
}
lean::cnstr_set(x_1923, 0, x_1920);
return x_1923;
}
else
{
obj* x_1924; obj* x_1926; obj* x_1927; obj* x_1929; obj* x_1931; obj* x_1932; 
x_1924 = lean::cnstr_get(x_1917, 0);
if (lean::is_exclusive(x_1917)) {
 lean::cnstr_set(x_1917, 0, lean::box(0));
 x_1926 = x_1917;
} else {
 lean::inc(x_1924);
 lean::dec(x_1917);
 x_1926 = lean::box(0);
}
x_1927 = lean::cnstr_get(x_1924, 0);
x_1929 = lean::cnstr_get(x_1924, 1);
if (lean::is_exclusive(x_1924)) {
 lean::cnstr_set(x_1924, 0, lean::box(0));
 lean::cnstr_set(x_1924, 1, lean::box(0));
 x_1931 = x_1924;
} else {
 lean::inc(x_1927);
 lean::inc(x_1929);
 lean::dec(x_1924);
 x_1931 = lean::box(0);
}
x_1932 = lean_expr_mk_sort(x_1927);
if (x_20 == 0)
{
obj* x_1933; 
x_1933 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1933) == 0)
{
obj* x_1936; obj* x_1937; 
lean::dec(x_2);
if (lean::is_scalar(x_1931)) {
 x_1936 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1936 = x_1931;
}
lean::cnstr_set(x_1936, 0, x_1932);
lean::cnstr_set(x_1936, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1937 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1937 = x_1926;
}
lean::cnstr_set(x_1937, 0, x_1936);
return x_1937;
}
else
{
obj* x_1938; obj* x_1941; obj* x_1944; obj* x_1947; obj* x_1948; obj* x_1950; obj* x_1951; obj* x_1952; obj* x_1953; obj* x_1956; obj* x_1957; obj* x_1958; obj* x_1959; obj* x_1960; 
x_1938 = lean::cnstr_get(x_1933, 0);
lean::inc(x_1938);
lean::dec(x_1933);
x_1941 = lean::cnstr_get(x_2, 0);
lean::inc(x_1941);
lean::dec(x_2);
x_1944 = lean::cnstr_get(x_1941, 2);
lean::inc(x_1944);
lean::dec(x_1941);
x_1947 = l_Lean_FileMap_toPosition(x_1944, x_1938);
x_1948 = lean::cnstr_get(x_1947, 1);
lean::inc(x_1948);
x_1950 = lean::box(0);
x_1951 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1952 = l_Lean_KVMap_setNat(x_1950, x_1951, x_1948);
x_1953 = lean::cnstr_get(x_1947, 0);
lean::inc(x_1953);
lean::dec(x_1947);
x_1956 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1957 = l_Lean_KVMap_setNat(x_1952, x_1956, x_1953);
x_1958 = lean_expr_mk_mdata(x_1957, x_1932);
if (lean::is_scalar(x_1931)) {
 x_1959 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1959 = x_1931;
}
lean::cnstr_set(x_1959, 0, x_1958);
lean::cnstr_set(x_1959, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1960 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1960 = x_1926;
}
lean::cnstr_set(x_1960, 0, x_1959);
return x_1960;
}
}
else
{
obj* x_1963; obj* x_1964; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1931)) {
 x_1963 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1963 = x_1931;
}
lean::cnstr_set(x_1963, 0, x_1932);
lean::cnstr_set(x_1963, 1, x_1929);
if (lean::is_scalar(x_1926)) {
 x_1964 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1964 = x_1926;
}
lean::cnstr_set(x_1964, 0, x_1963);
return x_1964;
}
}
}
else
{
obj* x_1966; obj* x_1970; 
lean::dec(x_1911);
x_1966 = lean::cnstr_get(x_1904, 1);
lean::inc(x_1966);
lean::dec(x_1904);
lean::inc(x_2);
x_1970 = l_Lean_Elaborator_toLevel___main(x_1966, x_1, x_2, x_3);
if (lean::obj_tag(x_1970) == 0)
{
obj* x_1973; obj* x_1975; obj* x_1976; 
lean::dec(x_0);
lean::dec(x_2);
x_1973 = lean::cnstr_get(x_1970, 0);
if (lean::is_exclusive(x_1970)) {
 x_1975 = x_1970;
} else {
 lean::inc(x_1973);
 lean::dec(x_1970);
 x_1975 = lean::box(0);
}
if (lean::is_scalar(x_1975)) {
 x_1976 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1976 = x_1975;
}
lean::cnstr_set(x_1976, 0, x_1973);
return x_1976;
}
else
{
obj* x_1977; obj* x_1979; obj* x_1980; obj* x_1982; obj* x_1984; obj* x_1985; obj* x_1986; 
x_1977 = lean::cnstr_get(x_1970, 0);
if (lean::is_exclusive(x_1970)) {
 lean::cnstr_set(x_1970, 0, lean::box(0));
 x_1979 = x_1970;
} else {
 lean::inc(x_1977);
 lean::dec(x_1970);
 x_1979 = lean::box(0);
}
x_1980 = lean::cnstr_get(x_1977, 0);
x_1982 = lean::cnstr_get(x_1977, 1);
if (lean::is_exclusive(x_1977)) {
 lean::cnstr_set(x_1977, 0, lean::box(0));
 lean::cnstr_set(x_1977, 1, lean::box(0));
 x_1984 = x_1977;
} else {
 lean::inc(x_1980);
 lean::inc(x_1982);
 lean::dec(x_1977);
 x_1984 = lean::box(0);
}
x_1985 = level_mk_succ(x_1980);
x_1986 = lean_expr_mk_sort(x_1985);
if (x_20 == 0)
{
obj* x_1987; 
x_1987 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1987) == 0)
{
obj* x_1990; obj* x_1991; 
lean::dec(x_2);
if (lean::is_scalar(x_1984)) {
 x_1990 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1990 = x_1984;
}
lean::cnstr_set(x_1990, 0, x_1986);
lean::cnstr_set(x_1990, 1, x_1982);
if (lean::is_scalar(x_1979)) {
 x_1991 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1991 = x_1979;
}
lean::cnstr_set(x_1991, 0, x_1990);
return x_1991;
}
else
{
obj* x_1992; obj* x_1995; obj* x_1998; obj* x_2001; obj* x_2002; obj* x_2004; obj* x_2005; obj* x_2006; obj* x_2007; obj* x_2010; obj* x_2011; obj* x_2012; obj* x_2013; obj* x_2014; 
x_1992 = lean::cnstr_get(x_1987, 0);
lean::inc(x_1992);
lean::dec(x_1987);
x_1995 = lean::cnstr_get(x_2, 0);
lean::inc(x_1995);
lean::dec(x_2);
x_1998 = lean::cnstr_get(x_1995, 2);
lean::inc(x_1998);
lean::dec(x_1995);
x_2001 = l_Lean_FileMap_toPosition(x_1998, x_1992);
x_2002 = lean::cnstr_get(x_2001, 1);
lean::inc(x_2002);
x_2004 = lean::box(0);
x_2005 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2006 = l_Lean_KVMap_setNat(x_2004, x_2005, x_2002);
x_2007 = lean::cnstr_get(x_2001, 0);
lean::inc(x_2007);
lean::dec(x_2001);
x_2010 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2011 = l_Lean_KVMap_setNat(x_2006, x_2010, x_2007);
x_2012 = lean_expr_mk_mdata(x_2011, x_1986);
if (lean::is_scalar(x_1984)) {
 x_2013 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2013 = x_1984;
}
lean::cnstr_set(x_2013, 0, x_2012);
lean::cnstr_set(x_2013, 1, x_1982);
if (lean::is_scalar(x_1979)) {
 x_2014 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2014 = x_1979;
}
lean::cnstr_set(x_2014, 0, x_2013);
return x_2014;
}
}
else
{
obj* x_2017; obj* x_2018; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1984)) {
 x_2017 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2017 = x_1984;
}
lean::cnstr_set(x_2017, 0, x_1986);
lean::cnstr_set(x_2017, 1, x_1982);
if (lean::is_scalar(x_1979)) {
 x_2018 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2018 = x_1979;
}
lean::cnstr_set(x_2018, 0, x_2017);
return x_2018;
}
}
}
}
}
else
{
obj* x_2021; obj* x_2022; obj* x_2026; 
lean::dec(x_8);
lean::dec(x_10);
x_2021 = l_Lean_Parser_Term_sort_HasView;
x_2022 = lean::cnstr_get(x_2021, 0);
lean::inc(x_2022);
lean::dec(x_2021);
lean::inc(x_0);
x_2026 = lean::apply_1(x_2022, x_0);
if (lean::obj_tag(x_2026) == 0)
{
lean::dec(x_2026);
if (x_20 == 0)
{
obj* x_2028; 
x_2028 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2028) == 0)
{
obj* x_2031; obj* x_2032; obj* x_2033; 
lean::dec(x_2);
x_2031 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2032 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2032, 0, x_2031);
lean::cnstr_set(x_2032, 1, x_3);
x_2033 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2033, 0, x_2032);
return x_2033;
}
else
{
obj* x_2034; obj* x_2037; obj* x_2040; obj* x_2043; obj* x_2044; obj* x_2046; obj* x_2047; obj* x_2048; obj* x_2049; obj* x_2052; obj* x_2053; obj* x_2054; obj* x_2055; obj* x_2056; obj* x_2057; 
x_2034 = lean::cnstr_get(x_2028, 0);
lean::inc(x_2034);
lean::dec(x_2028);
x_2037 = lean::cnstr_get(x_2, 0);
lean::inc(x_2037);
lean::dec(x_2);
x_2040 = lean::cnstr_get(x_2037, 2);
lean::inc(x_2040);
lean::dec(x_2037);
x_2043 = l_Lean_FileMap_toPosition(x_2040, x_2034);
x_2044 = lean::cnstr_get(x_2043, 1);
lean::inc(x_2044);
x_2046 = lean::box(0);
x_2047 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2048 = l_Lean_KVMap_setNat(x_2046, x_2047, x_2044);
x_2049 = lean::cnstr_get(x_2043, 0);
lean::inc(x_2049);
lean::dec(x_2043);
x_2052 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2053 = l_Lean_KVMap_setNat(x_2048, x_2052, x_2049);
x_2054 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2055 = lean_expr_mk_mdata(x_2053, x_2054);
x_2056 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2056, 0, x_2055);
lean::cnstr_set(x_2056, 1, x_3);
x_2057 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2057, 0, x_2056);
return x_2057;
}
}
else
{
obj* x_2060; obj* x_2061; obj* x_2062; 
lean::dec(x_0);
lean::dec(x_2);
x_2060 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2061 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2061, 0, x_2060);
lean::cnstr_set(x_2061, 1, x_3);
x_2062 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2062, 0, x_2061);
return x_2062;
}
}
else
{
lean::dec(x_2026);
if (x_20 == 0)
{
obj* x_2064; 
x_2064 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2064) == 0)
{
obj* x_2067; obj* x_2068; obj* x_2069; 
lean::dec(x_2);
x_2067 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2068 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2068, 0, x_2067);
lean::cnstr_set(x_2068, 1, x_3);
x_2069 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2069, 0, x_2068);
return x_2069;
}
else
{
obj* x_2070; obj* x_2073; obj* x_2076; obj* x_2079; obj* x_2080; obj* x_2082; obj* x_2083; obj* x_2084; obj* x_2085; obj* x_2088; obj* x_2089; obj* x_2090; obj* x_2091; obj* x_2092; obj* x_2093; 
x_2070 = lean::cnstr_get(x_2064, 0);
lean::inc(x_2070);
lean::dec(x_2064);
x_2073 = lean::cnstr_get(x_2, 0);
lean::inc(x_2073);
lean::dec(x_2);
x_2076 = lean::cnstr_get(x_2073, 2);
lean::inc(x_2076);
lean::dec(x_2073);
x_2079 = l_Lean_FileMap_toPosition(x_2076, x_2070);
x_2080 = lean::cnstr_get(x_2079, 1);
lean::inc(x_2080);
x_2082 = lean::box(0);
x_2083 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2084 = l_Lean_KVMap_setNat(x_2082, x_2083, x_2080);
x_2085 = lean::cnstr_get(x_2079, 0);
lean::inc(x_2085);
lean::dec(x_2079);
x_2088 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2089 = l_Lean_KVMap_setNat(x_2084, x_2088, x_2085);
x_2090 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2091 = lean_expr_mk_mdata(x_2089, x_2090);
x_2092 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2092, 0, x_2091);
lean::cnstr_set(x_2092, 1, x_3);
x_2093 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2093, 0, x_2092);
return x_2093;
}
}
else
{
obj* x_2096; obj* x_2097; obj* x_2098; 
lean::dec(x_0);
lean::dec(x_2);
x_2096 = l_Lean_Elaborator_toPexpr___main___closed__46;
x_2097 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2097, 0, x_2096);
lean::cnstr_set(x_2097, 1, x_3);
x_2098 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2098, 0, x_2097);
return x_2098;
}
}
}
}
else
{
obj* x_2100; obj* x_2101; obj* x_2105; obj* x_2106; 
lean::dec(x_10);
x_2100 = l_Lean_Parser_Term_pi_HasView;
x_2101 = lean::cnstr_get(x_2100, 0);
lean::inc(x_2101);
lean::dec(x_2100);
lean::inc(x_0);
x_2105 = lean::apply_1(x_2101, x_0);
x_2106 = lean::cnstr_get(x_2105, 1);
lean::inc(x_2106);
if (lean::obj_tag(x_2106) == 0)
{
obj* x_2111; obj* x_2112; obj* x_2114; 
lean::dec(x_2106);
lean::dec(x_2105);
lean::inc(x_0);
x_2111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2111, 0, x_0);
x_2112 = l_Lean_Elaborator_toPexpr___main___closed__47;
lean::inc(x_2);
x_2114 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2111, x_2112, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2111);
if (lean::obj_tag(x_2114) == 0)
{
obj* x_2120; obj* x_2122; obj* x_2123; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2120 = lean::cnstr_get(x_2114, 0);
if (lean::is_exclusive(x_2114)) {
 x_2122 = x_2114;
} else {
 lean::inc(x_2120);
 lean::dec(x_2114);
 x_2122 = lean::box(0);
}
if (lean::is_scalar(x_2122)) {
 x_2123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2123 = x_2122;
}
lean::cnstr_set(x_2123, 0, x_2120);
return x_2123;
}
else
{
obj* x_2124; 
x_2124 = lean::cnstr_get(x_2114, 0);
lean::inc(x_2124);
lean::dec(x_2114);
x_15 = x_2124;
goto lbl_16;
}
}
else
{
obj* x_2127; obj* x_2130; obj* x_2131; obj* x_2133; obj* x_2136; obj* x_2138; obj* x_2142; 
x_2127 = lean::cnstr_get(x_2106, 0);
lean::inc(x_2127);
lean::dec(x_2106);
x_2130 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2127);
x_2131 = lean::cnstr_get(x_2130, 1);
lean::inc(x_2131);
x_2133 = lean::cnstr_get(x_2130, 0);
lean::inc(x_2133);
lean::dec(x_2130);
x_2136 = lean::cnstr_get(x_2131, 0);
lean::inc(x_2136);
x_2138 = lean::cnstr_get(x_2131, 1);
lean::inc(x_2138);
lean::dec(x_2131);
lean::inc(x_2);
x_2142 = l_Lean_Elaborator_toPexpr___main(x_2138, x_1, x_2, x_3);
if (lean::obj_tag(x_2142) == 0)
{
obj* x_2149; obj* x_2151; obj* x_2152; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2133);
lean::dec(x_2105);
lean::dec(x_2136);
x_2149 = lean::cnstr_get(x_2142, 0);
if (lean::is_exclusive(x_2142)) {
 x_2151 = x_2142;
} else {
 lean::inc(x_2149);
 lean::dec(x_2142);
 x_2151 = lean::box(0);
}
if (lean::is_scalar(x_2151)) {
 x_2152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2152 = x_2151;
}
lean::cnstr_set(x_2152, 0, x_2149);
return x_2152;
}
else
{
obj* x_2153; obj* x_2156; obj* x_2158; obj* x_2161; obj* x_2165; 
x_2153 = lean::cnstr_get(x_2142, 0);
lean::inc(x_2153);
lean::dec(x_2142);
x_2156 = lean::cnstr_get(x_2153, 0);
lean::inc(x_2156);
x_2158 = lean::cnstr_get(x_2153, 1);
lean::inc(x_2158);
lean::dec(x_2153);
x_2161 = lean::cnstr_get(x_2105, 3);
lean::inc(x_2161);
lean::dec(x_2105);
lean::inc(x_2);
x_2165 = l_Lean_Elaborator_toPexpr___main(x_2161, x_1, x_2, x_2158);
if (lean::obj_tag(x_2165) == 0)
{
obj* x_2172; obj* x_2174; obj* x_2175; 
lean::dec(x_2156);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2133);
lean::dec(x_2136);
x_2172 = lean::cnstr_get(x_2165, 0);
if (lean::is_exclusive(x_2165)) {
 x_2174 = x_2165;
} else {
 lean::inc(x_2172);
 lean::dec(x_2165);
 x_2174 = lean::box(0);
}
if (lean::is_scalar(x_2174)) {
 x_2175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2175 = x_2174;
}
lean::cnstr_set(x_2175, 0, x_2172);
return x_2175;
}
else
{
obj* x_2176; obj* x_2179; obj* x_2181; obj* x_2183; obj* x_2184; uint8 x_2185; obj* x_2186; obj* x_2187; 
x_2176 = lean::cnstr_get(x_2165, 0);
lean::inc(x_2176);
lean::dec(x_2165);
x_2179 = lean::cnstr_get(x_2176, 0);
x_2181 = lean::cnstr_get(x_2176, 1);
if (lean::is_exclusive(x_2176)) {
 x_2183 = x_2176;
} else {
 lean::inc(x_2179);
 lean::inc(x_2181);
 lean::dec(x_2176);
 x_2183 = lean::box(0);
}
x_2184 = l_Lean_Elaborator_mangleIdent(x_2136);
x_2185 = lean::unbox(x_2133);
x_2186 = lean_expr_mk_pi(x_2184, x_2185, x_2156, x_2179);
if (lean::is_scalar(x_2183)) {
 x_2187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2187 = x_2183;
}
lean::cnstr_set(x_2187, 0, x_2186);
lean::cnstr_set(x_2187, 1, x_2181);
x_15 = x_2187;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2189; obj* x_2190; obj* x_2194; obj* x_2195; 
lean::dec(x_10);
x_2189 = l_Lean_Parser_Term_lambda_HasView;
x_2190 = lean::cnstr_get(x_2189, 0);
lean::inc(x_2190);
lean::dec(x_2189);
lean::inc(x_0);
x_2194 = lean::apply_1(x_2190, x_0);
x_2195 = lean::cnstr_get(x_2194, 1);
lean::inc(x_2195);
if (lean::obj_tag(x_2195) == 0)
{
obj* x_2200; obj* x_2201; obj* x_2203; 
lean::dec(x_2194);
lean::dec(x_2195);
lean::inc(x_0);
x_2200 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2200, 0, x_0);
x_2201 = l_Lean_Elaborator_toPexpr___main___closed__48;
lean::inc(x_2);
x_2203 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2200, x_2201, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2200);
if (lean::obj_tag(x_2203) == 0)
{
obj* x_2209; obj* x_2211; obj* x_2212; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2209 = lean::cnstr_get(x_2203, 0);
if (lean::is_exclusive(x_2203)) {
 x_2211 = x_2203;
} else {
 lean::inc(x_2209);
 lean::dec(x_2203);
 x_2211 = lean::box(0);
}
if (lean::is_scalar(x_2211)) {
 x_2212 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2212 = x_2211;
}
lean::cnstr_set(x_2212, 0, x_2209);
return x_2212;
}
else
{
obj* x_2213; 
x_2213 = lean::cnstr_get(x_2203, 0);
lean::inc(x_2213);
lean::dec(x_2203);
x_15 = x_2213;
goto lbl_16;
}
}
else
{
obj* x_2216; obj* x_2219; obj* x_2220; obj* x_2222; obj* x_2225; obj* x_2227; obj* x_2231; 
x_2216 = lean::cnstr_get(x_2195, 0);
lean::inc(x_2216);
lean::dec(x_2195);
x_2219 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2216);
x_2220 = lean::cnstr_get(x_2219, 1);
lean::inc(x_2220);
x_2222 = lean::cnstr_get(x_2219, 0);
lean::inc(x_2222);
lean::dec(x_2219);
x_2225 = lean::cnstr_get(x_2220, 0);
lean::inc(x_2225);
x_2227 = lean::cnstr_get(x_2220, 1);
lean::inc(x_2227);
lean::dec(x_2220);
lean::inc(x_2);
x_2231 = l_Lean_Elaborator_toPexpr___main(x_2227, x_1, x_2, x_3);
if (lean::obj_tag(x_2231) == 0)
{
obj* x_2238; obj* x_2240; obj* x_2241; 
lean::dec(x_2194);
lean::dec(x_2222);
lean::dec(x_2225);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2238 = lean::cnstr_get(x_2231, 0);
if (lean::is_exclusive(x_2231)) {
 x_2240 = x_2231;
} else {
 lean::inc(x_2238);
 lean::dec(x_2231);
 x_2240 = lean::box(0);
}
if (lean::is_scalar(x_2240)) {
 x_2241 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2241 = x_2240;
}
lean::cnstr_set(x_2241, 0, x_2238);
return x_2241;
}
else
{
obj* x_2242; obj* x_2245; obj* x_2247; obj* x_2250; obj* x_2254; 
x_2242 = lean::cnstr_get(x_2231, 0);
lean::inc(x_2242);
lean::dec(x_2231);
x_2245 = lean::cnstr_get(x_2242, 0);
lean::inc(x_2245);
x_2247 = lean::cnstr_get(x_2242, 1);
lean::inc(x_2247);
lean::dec(x_2242);
x_2250 = lean::cnstr_get(x_2194, 3);
lean::inc(x_2250);
lean::dec(x_2194);
lean::inc(x_2);
x_2254 = l_Lean_Elaborator_toPexpr___main(x_2250, x_1, x_2, x_2247);
if (lean::obj_tag(x_2254) == 0)
{
obj* x_2261; obj* x_2263; obj* x_2264; 
lean::dec(x_2222);
lean::dec(x_2225);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2245);
x_2261 = lean::cnstr_get(x_2254, 0);
if (lean::is_exclusive(x_2254)) {
 x_2263 = x_2254;
} else {
 lean::inc(x_2261);
 lean::dec(x_2254);
 x_2263 = lean::box(0);
}
if (lean::is_scalar(x_2263)) {
 x_2264 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2264 = x_2263;
}
lean::cnstr_set(x_2264, 0, x_2261);
return x_2264;
}
else
{
obj* x_2265; obj* x_2268; obj* x_2270; obj* x_2272; obj* x_2273; uint8 x_2274; obj* x_2275; obj* x_2276; 
x_2265 = lean::cnstr_get(x_2254, 0);
lean::inc(x_2265);
lean::dec(x_2254);
x_2268 = lean::cnstr_get(x_2265, 0);
x_2270 = lean::cnstr_get(x_2265, 1);
if (lean::is_exclusive(x_2265)) {
 x_2272 = x_2265;
} else {
 lean::inc(x_2268);
 lean::inc(x_2270);
 lean::dec(x_2265);
 x_2272 = lean::box(0);
}
x_2273 = l_Lean_Elaborator_mangleIdent(x_2225);
x_2274 = lean::unbox(x_2222);
x_2275 = lean_expr_mk_lambda(x_2273, x_2274, x_2245, x_2268);
if (lean::is_scalar(x_2272)) {
 x_2276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2276 = x_2272;
}
lean::cnstr_set(x_2276, 0, x_2275);
lean::cnstr_set(x_2276, 1, x_2270);
x_15 = x_2276;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2279; obj* x_2280; obj* x_2284; obj* x_2285; obj* x_2288; 
lean::dec(x_8);
lean::dec(x_10);
x_2279 = l_Lean_Parser_Term_app_HasView;
x_2280 = lean::cnstr_get(x_2279, 0);
lean::inc(x_2280);
lean::dec(x_2279);
lean::inc(x_0);
x_2284 = lean::apply_1(x_2280, x_0);
x_2285 = lean::cnstr_get(x_2284, 0);
lean::inc(x_2285);
lean::inc(x_2);
x_2288 = l_Lean_Elaborator_toPexpr___main(x_2285, x_1, x_2, x_3);
if (lean::obj_tag(x_2288) == 0)
{
obj* x_2292; obj* x_2294; obj* x_2295; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2284);
x_2292 = lean::cnstr_get(x_2288, 0);
if (lean::is_exclusive(x_2288)) {
 x_2294 = x_2288;
} else {
 lean::inc(x_2292);
 lean::dec(x_2288);
 x_2294 = lean::box(0);
}
if (lean::is_scalar(x_2294)) {
 x_2295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2295 = x_2294;
}
lean::cnstr_set(x_2295, 0, x_2292);
return x_2295;
}
else
{
obj* x_2296; obj* x_2299; obj* x_2301; obj* x_2304; obj* x_2308; 
x_2296 = lean::cnstr_get(x_2288, 0);
lean::inc(x_2296);
lean::dec(x_2288);
x_2299 = lean::cnstr_get(x_2296, 0);
lean::inc(x_2299);
x_2301 = lean::cnstr_get(x_2296, 1);
lean::inc(x_2301);
lean::dec(x_2296);
x_2304 = lean::cnstr_get(x_2284, 1);
lean::inc(x_2304);
lean::dec(x_2284);
lean::inc(x_2);
x_2308 = l_Lean_Elaborator_toPexpr___main(x_2304, x_1, x_2, x_2301);
if (lean::obj_tag(x_2308) == 0)
{
obj* x_2312; obj* x_2314; obj* x_2315; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2299);
x_2312 = lean::cnstr_get(x_2308, 0);
if (lean::is_exclusive(x_2308)) {
 x_2314 = x_2308;
} else {
 lean::inc(x_2312);
 lean::dec(x_2308);
 x_2314 = lean::box(0);
}
if (lean::is_scalar(x_2314)) {
 x_2315 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2315 = x_2314;
}
lean::cnstr_set(x_2315, 0, x_2312);
return x_2315;
}
else
{
obj* x_2316; obj* x_2318; obj* x_2319; obj* x_2321; obj* x_2323; obj* x_2324; 
x_2316 = lean::cnstr_get(x_2308, 0);
if (lean::is_exclusive(x_2308)) {
 lean::cnstr_set(x_2308, 0, lean::box(0));
 x_2318 = x_2308;
} else {
 lean::inc(x_2316);
 lean::dec(x_2308);
 x_2318 = lean::box(0);
}
x_2319 = lean::cnstr_get(x_2316, 0);
x_2321 = lean::cnstr_get(x_2316, 1);
if (lean::is_exclusive(x_2316)) {
 lean::cnstr_set(x_2316, 0, lean::box(0));
 lean::cnstr_set(x_2316, 1, lean::box(0));
 x_2323 = x_2316;
} else {
 lean::inc(x_2319);
 lean::inc(x_2321);
 lean::dec(x_2316);
 x_2323 = lean::box(0);
}
x_2324 = lean_expr_mk_app(x_2299, x_2319);
if (x_20 == 0)
{
obj* x_2325; 
x_2325 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2325) == 0)
{
obj* x_2328; obj* x_2329; 
lean::dec(x_2);
if (lean::is_scalar(x_2323)) {
 x_2328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2328 = x_2323;
}
lean::cnstr_set(x_2328, 0, x_2324);
lean::cnstr_set(x_2328, 1, x_2321);
if (lean::is_scalar(x_2318)) {
 x_2329 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2329 = x_2318;
}
lean::cnstr_set(x_2329, 0, x_2328);
return x_2329;
}
else
{
obj* x_2330; obj* x_2333; obj* x_2336; obj* x_2339; obj* x_2340; obj* x_2342; obj* x_2343; obj* x_2344; obj* x_2345; obj* x_2348; obj* x_2349; obj* x_2350; obj* x_2351; obj* x_2352; 
x_2330 = lean::cnstr_get(x_2325, 0);
lean::inc(x_2330);
lean::dec(x_2325);
x_2333 = lean::cnstr_get(x_2, 0);
lean::inc(x_2333);
lean::dec(x_2);
x_2336 = lean::cnstr_get(x_2333, 2);
lean::inc(x_2336);
lean::dec(x_2333);
x_2339 = l_Lean_FileMap_toPosition(x_2336, x_2330);
x_2340 = lean::cnstr_get(x_2339, 1);
lean::inc(x_2340);
x_2342 = lean::box(0);
x_2343 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2344 = l_Lean_KVMap_setNat(x_2342, x_2343, x_2340);
x_2345 = lean::cnstr_get(x_2339, 0);
lean::inc(x_2345);
lean::dec(x_2339);
x_2348 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2349 = l_Lean_KVMap_setNat(x_2344, x_2348, x_2345);
x_2350 = lean_expr_mk_mdata(x_2349, x_2324);
if (lean::is_scalar(x_2323)) {
 x_2351 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2351 = x_2323;
}
lean::cnstr_set(x_2351, 0, x_2350);
lean::cnstr_set(x_2351, 1, x_2321);
if (lean::is_scalar(x_2318)) {
 x_2352 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2352 = x_2318;
}
lean::cnstr_set(x_2352, 0, x_2351);
return x_2352;
}
}
else
{
obj* x_2355; obj* x_2356; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2323)) {
 x_2355 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2355 = x_2323;
}
lean::cnstr_set(x_2355, 0, x_2324);
lean::cnstr_set(x_2355, 1, x_2321);
if (lean::is_scalar(x_2318)) {
 x_2356 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2356 = x_2318;
}
lean::cnstr_set(x_2356, 0, x_2355);
return x_2356;
}
}
}
}
}
else
{
obj* x_2358; obj* x_2359; obj* x_2363; obj* x_2364; 
lean::dec(x_10);
x_2358 = l_Lean_Parser_identUnivs_HasView;
x_2359 = lean::cnstr_get(x_2358, 0);
lean::inc(x_2359);
lean::dec(x_2358);
lean::inc(x_0);
x_2363 = lean::apply_1(x_2359, x_0);
x_2364 = lean::cnstr_get(x_2363, 1);
lean::inc(x_2364);
if (lean::obj_tag(x_2364) == 0)
{
obj* x_2366; obj* x_2370; obj* x_2371; obj* x_2372; obj* x_2373; obj* x_2376; obj* x_2377; obj* x_2378; obj* x_2379; obj* x_2380; obj* x_2381; uint8 x_2382; 
x_2366 = lean::cnstr_get(x_2363, 0);
lean::inc(x_2366);
lean::dec(x_2363);
lean::inc(x_2366);
x_2370 = l_Lean_Elaborator_mangleIdent(x_2366);
x_2371 = lean::box(0);
x_2372 = lean_expr_mk_const(x_2370, x_2371);
x_2373 = lean::cnstr_get(x_2366, 3);
lean::inc(x_2373);
lean::dec(x_2366);
x_2376 = lean::mk_nat_obj(0ul);
x_2377 = l_List_enumFrom___main___rarg(x_2376, x_2373);
x_2378 = l_Lean_Elaborator_toPexpr___main___closed__49;
x_2379 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__20(x_2378, x_2377);
x_2380 = lean_expr_mk_mdata(x_2379, x_2372);
x_2381 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2382 = lean_name_dec_eq(x_8, x_2381);
lean::dec(x_8);
if (x_2382 == 0)
{
obj* x_2384; 
x_2384 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2384) == 0)
{
obj* x_2387; obj* x_2388; 
lean::dec(x_2);
x_2387 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2387, 0, x_2380);
lean::cnstr_set(x_2387, 1, x_3);
x_2388 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2388, 0, x_2387);
return x_2388;
}
else
{
obj* x_2389; obj* x_2392; obj* x_2395; obj* x_2398; obj* x_2399; obj* x_2401; obj* x_2402; obj* x_2403; obj* x_2406; obj* x_2407; obj* x_2408; obj* x_2409; obj* x_2410; 
x_2389 = lean::cnstr_get(x_2384, 0);
lean::inc(x_2389);
lean::dec(x_2384);
x_2392 = lean::cnstr_get(x_2, 0);
lean::inc(x_2392);
lean::dec(x_2);
x_2395 = lean::cnstr_get(x_2392, 2);
lean::inc(x_2395);
lean::dec(x_2392);
x_2398 = l_Lean_FileMap_toPosition(x_2395, x_2389);
x_2399 = lean::cnstr_get(x_2398, 1);
lean::inc(x_2399);
x_2401 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2402 = l_Lean_KVMap_setNat(x_2371, x_2401, x_2399);
x_2403 = lean::cnstr_get(x_2398, 0);
lean::inc(x_2403);
lean::dec(x_2398);
x_2406 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2407 = l_Lean_KVMap_setNat(x_2402, x_2406, x_2403);
x_2408 = lean_expr_mk_mdata(x_2407, x_2380);
x_2409 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2409, 0, x_2408);
lean::cnstr_set(x_2409, 1, x_3);
x_2410 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2410, 0, x_2409);
return x_2410;
}
}
else
{
obj* x_2413; obj* x_2414; 
lean::dec(x_0);
lean::dec(x_2);
x_2413 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2413, 0, x_2380);
lean::cnstr_set(x_2413, 1, x_3);
x_2414 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2414, 0, x_2413);
return x_2414;
}
}
else
{
obj* x_2415; obj* x_2418; obj* x_2421; obj* x_2425; 
x_2415 = lean::cnstr_get(x_2363, 0);
lean::inc(x_2415);
lean::dec(x_2363);
x_2418 = lean::cnstr_get(x_2364, 0);
lean::inc(x_2418);
lean::dec(x_2364);
x_2421 = lean::cnstr_get(x_2418, 1);
lean::inc(x_2421);
lean::dec(x_2418);
lean::inc(x_2);
x_2425 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(x_2421, x_1, x_2, x_3);
if (lean::obj_tag(x_2425) == 0)
{
obj* x_2430; obj* x_2432; obj* x_2433; 
lean::dec(x_2415);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2430 = lean::cnstr_get(x_2425, 0);
if (lean::is_exclusive(x_2425)) {
 x_2432 = x_2425;
} else {
 lean::inc(x_2430);
 lean::dec(x_2425);
 x_2432 = lean::box(0);
}
if (lean::is_scalar(x_2432)) {
 x_2433 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2433 = x_2432;
}
lean::cnstr_set(x_2433, 0, x_2430);
return x_2433;
}
else
{
obj* x_2434; obj* x_2436; obj* x_2437; obj* x_2439; obj* x_2441; obj* x_2443; obj* x_2444; obj* x_2445; obj* x_2448; obj* x_2449; obj* x_2450; obj* x_2451; obj* x_2452; obj* x_2453; uint8 x_2454; 
x_2434 = lean::cnstr_get(x_2425, 0);
if (lean::is_exclusive(x_2425)) {
 lean::cnstr_set(x_2425, 0, lean::box(0));
 x_2436 = x_2425;
} else {
 lean::inc(x_2434);
 lean::dec(x_2425);
 x_2436 = lean::box(0);
}
x_2437 = lean::cnstr_get(x_2434, 0);
x_2439 = lean::cnstr_get(x_2434, 1);
if (lean::is_exclusive(x_2434)) {
 lean::cnstr_set(x_2434, 0, lean::box(0));
 lean::cnstr_set(x_2434, 1, lean::box(0));
 x_2441 = x_2434;
} else {
 lean::inc(x_2437);
 lean::inc(x_2439);
 lean::dec(x_2434);
 x_2441 = lean::box(0);
}
lean::inc(x_2415);
x_2443 = l_Lean_Elaborator_mangleIdent(x_2415);
x_2444 = lean_expr_mk_const(x_2443, x_2437);
x_2445 = lean::cnstr_get(x_2415, 3);
lean::inc(x_2445);
lean::dec(x_2415);
x_2448 = lean::mk_nat_obj(0ul);
x_2449 = l_List_enumFrom___main___rarg(x_2448, x_2445);
x_2450 = l_Lean_Elaborator_toPexpr___main___closed__50;
x_2451 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__22(x_2450, x_2449);
x_2452 = lean_expr_mk_mdata(x_2451, x_2444);
x_2453 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2454 = lean_name_dec_eq(x_8, x_2453);
lean::dec(x_8);
if (x_2454 == 0)
{
obj* x_2456; obj* x_2457; 
x_2456 = lean::box(0);
x_2457 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2457) == 0)
{
obj* x_2460; obj* x_2461; 
lean::dec(x_2);
if (lean::is_scalar(x_2441)) {
 x_2460 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2460 = x_2441;
}
lean::cnstr_set(x_2460, 0, x_2452);
lean::cnstr_set(x_2460, 1, x_2439);
if (lean::is_scalar(x_2436)) {
 x_2461 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2461 = x_2436;
}
lean::cnstr_set(x_2461, 0, x_2460);
return x_2461;
}
else
{
obj* x_2462; obj* x_2465; obj* x_2468; obj* x_2471; obj* x_2472; obj* x_2474; obj* x_2475; obj* x_2476; obj* x_2479; obj* x_2480; obj* x_2481; obj* x_2482; obj* x_2483; 
x_2462 = lean::cnstr_get(x_2457, 0);
lean::inc(x_2462);
lean::dec(x_2457);
x_2465 = lean::cnstr_get(x_2, 0);
lean::inc(x_2465);
lean::dec(x_2);
x_2468 = lean::cnstr_get(x_2465, 2);
lean::inc(x_2468);
lean::dec(x_2465);
x_2471 = l_Lean_FileMap_toPosition(x_2468, x_2462);
x_2472 = lean::cnstr_get(x_2471, 1);
lean::inc(x_2472);
x_2474 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2475 = l_Lean_KVMap_setNat(x_2456, x_2474, x_2472);
x_2476 = lean::cnstr_get(x_2471, 0);
lean::inc(x_2476);
lean::dec(x_2471);
x_2479 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2480 = l_Lean_KVMap_setNat(x_2475, x_2479, x_2476);
x_2481 = lean_expr_mk_mdata(x_2480, x_2452);
if (lean::is_scalar(x_2441)) {
 x_2482 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2482 = x_2441;
}
lean::cnstr_set(x_2482, 0, x_2481);
lean::cnstr_set(x_2482, 1, x_2439);
if (lean::is_scalar(x_2436)) {
 x_2483 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2483 = x_2436;
}
lean::cnstr_set(x_2483, 0, x_2482);
return x_2483;
}
}
else
{
obj* x_2486; obj* x_2487; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2441)) {
 x_2486 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2486 = x_2441;
}
lean::cnstr_set(x_2486, 0, x_2452);
lean::cnstr_set(x_2486, 1, x_2439);
if (lean::is_scalar(x_2436)) {
 x_2487 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2487 = x_2436;
}
lean::cnstr_set(x_2487, 0, x_2486);
return x_2487;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2491; obj* x_2493; obj* x_2494; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2491 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2493 = x_13;
} else {
 lean::inc(x_2491);
 lean::dec(x_13);
 x_2493 = lean::box(0);
}
if (lean::is_scalar(x_2493)) {
 x_2494 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2494 = x_2493;
}
lean::cnstr_set(x_2494, 0, x_2491);
return x_2494;
}
else
{
obj* x_2495; obj* x_2497; obj* x_2498; obj* x_2500; obj* x_2502; obj* x_2503; uint8 x_2504; 
x_2495 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2497 = x_13;
} else {
 lean::inc(x_2495);
 lean::dec(x_13);
 x_2497 = lean::box(0);
}
x_2498 = lean::cnstr_get(x_2495, 0);
x_2500 = lean::cnstr_get(x_2495, 1);
if (lean::is_exclusive(x_2495)) {
 lean::cnstr_set(x_2495, 0, lean::box(0));
 lean::cnstr_set(x_2495, 1, lean::box(0));
 x_2502 = x_2495;
} else {
 lean::inc(x_2498);
 lean::inc(x_2500);
 lean::dec(x_2495);
 x_2502 = lean::box(0);
}
x_2503 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2504 = lean_name_dec_eq(x_8, x_2503);
lean::dec(x_8);
if (x_2504 == 0)
{
obj* x_2506; 
x_2506 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2506) == 0)
{
obj* x_2509; obj* x_2510; 
lean::dec(x_2);
if (lean::is_scalar(x_2502)) {
 x_2509 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2509 = x_2502;
}
lean::cnstr_set(x_2509, 0, x_2498);
lean::cnstr_set(x_2509, 1, x_2500);
if (lean::is_scalar(x_2497)) {
 x_2510 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2510 = x_2497;
}
lean::cnstr_set(x_2510, 0, x_2509);
return x_2510;
}
else
{
obj* x_2511; obj* x_2514; obj* x_2517; obj* x_2520; obj* x_2521; obj* x_2523; obj* x_2524; obj* x_2525; obj* x_2526; obj* x_2529; obj* x_2530; obj* x_2531; obj* x_2532; obj* x_2533; 
x_2511 = lean::cnstr_get(x_2506, 0);
lean::inc(x_2511);
lean::dec(x_2506);
x_2514 = lean::cnstr_get(x_2, 0);
lean::inc(x_2514);
lean::dec(x_2);
x_2517 = lean::cnstr_get(x_2514, 2);
lean::inc(x_2517);
lean::dec(x_2514);
x_2520 = l_Lean_FileMap_toPosition(x_2517, x_2511);
x_2521 = lean::cnstr_get(x_2520, 1);
lean::inc(x_2521);
x_2523 = lean::box(0);
x_2524 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2525 = l_Lean_KVMap_setNat(x_2523, x_2524, x_2521);
x_2526 = lean::cnstr_get(x_2520, 0);
lean::inc(x_2526);
lean::dec(x_2520);
x_2529 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2530 = l_Lean_KVMap_setNat(x_2525, x_2529, x_2526);
x_2531 = lean_expr_mk_mdata(x_2530, x_2498);
if (lean::is_scalar(x_2502)) {
 x_2532 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2532 = x_2502;
}
lean::cnstr_set(x_2532, 0, x_2531);
lean::cnstr_set(x_2532, 1, x_2500);
if (lean::is_scalar(x_2497)) {
 x_2533 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2533 = x_2497;
}
lean::cnstr_set(x_2533, 0, x_2532);
return x_2533;
}
}
else
{
obj* x_2536; obj* x_2537; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2502)) {
 x_2536 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2536 = x_2502;
}
lean::cnstr_set(x_2536, 0, x_2498);
lean::cnstr_set(x_2536, 1, x_2500);
if (lean::is_scalar(x_2497)) {
 x_2537 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2537 = x_2497;
}
lean::cnstr_set(x_2537, 0, x_2536);
return x_2537;
}
}
}
lbl_16:
{
obj* x_2538; obj* x_2540; obj* x_2542; obj* x_2543; uint8 x_2544; 
x_2538 = lean::cnstr_get(x_15, 0);
x_2540 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2542 = x_15;
} else {
 lean::inc(x_2538);
 lean::inc(x_2540);
 lean::dec(x_15);
 x_2542 = lean::box(0);
}
x_2543 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2544 = lean_name_dec_eq(x_8, x_2543);
lean::dec(x_8);
if (x_2544 == 0)
{
obj* x_2546; 
x_2546 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2546) == 0)
{
obj* x_2549; obj* x_2550; 
lean::dec(x_2);
if (lean::is_scalar(x_2542)) {
 x_2549 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2549 = x_2542;
}
lean::cnstr_set(x_2549, 0, x_2538);
lean::cnstr_set(x_2549, 1, x_2540);
x_2550 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2550, 0, x_2549);
return x_2550;
}
else
{
obj* x_2551; obj* x_2554; obj* x_2557; obj* x_2560; obj* x_2561; obj* x_2563; obj* x_2564; obj* x_2565; obj* x_2566; obj* x_2569; obj* x_2570; obj* x_2571; obj* x_2572; obj* x_2573; 
x_2551 = lean::cnstr_get(x_2546, 0);
lean::inc(x_2551);
lean::dec(x_2546);
x_2554 = lean::cnstr_get(x_2, 0);
lean::inc(x_2554);
lean::dec(x_2);
x_2557 = lean::cnstr_get(x_2554, 2);
lean::inc(x_2557);
lean::dec(x_2554);
x_2560 = l_Lean_FileMap_toPosition(x_2557, x_2551);
x_2561 = lean::cnstr_get(x_2560, 1);
lean::inc(x_2561);
x_2563 = lean::box(0);
x_2564 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2565 = l_Lean_KVMap_setNat(x_2563, x_2564, x_2561);
x_2566 = lean::cnstr_get(x_2560, 0);
lean::inc(x_2566);
lean::dec(x_2560);
x_2569 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2570 = l_Lean_KVMap_setNat(x_2565, x_2569, x_2566);
x_2571 = lean_expr_mk_mdata(x_2570, x_2538);
if (lean::is_scalar(x_2542)) {
 x_2572 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2572 = x_2542;
}
lean::cnstr_set(x_2572, 0, x_2571);
lean::cnstr_set(x_2572, 1, x_2540);
x_2573 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2573, 0, x_2572);
return x_2573;
}
}
else
{
obj* x_2576; obj* x_2577; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2542)) {
 x_2576 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2576 = x_2542;
}
lean::cnstr_set(x_2576, 0, x_2538);
lean::cnstr_set(x_2576, 1, x_2540);
x_2577 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2577, 0, x_2576);
return x_2577;
}
}
}
default:
{
obj* x_2578; 
x_2578 = lean::box(0);
x_4 = x_2578;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2581; obj* x_2582; obj* x_2583; obj* x_2584; obj* x_2585; obj* x_2586; obj* x_2588; 
lean::dec(x_4);
lean::inc(x_0);
x_2581 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2581, 0, x_0);
x_2582 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_2583 = l_Lean_Options_empty;
x_2584 = l_Lean_Format_pretty(x_2582, x_2583);
x_2585 = l_Lean_Elaborator_toPexpr___main___closed__1;
x_2586 = lean::string_append(x_2585, x_2584);
lean::dec(x_2584);
x_2588 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2581, x_2586, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2581);
return x_2588;
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
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__6(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
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
obj* l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elaborator_toPexpr___main___lambda__1___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Elaborator_toPexpr___main___lambda__1(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Elaborator_toPexpr___main___lambda__2___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_Elaborator_toPexpr___main___lambda__2(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
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
obj* x_5; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_9 = l_Lean_Elaborator_currentScope(x_2, x_3, x_4);
switch (lean::obj_tag(x_1)) {
case 10:
{
obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_5, 2);
lean::inc(x_17);
x_19 = l_Lean_Parser_Syntax_getPos(x_0);
x_20 = lean::mk_nat_obj(0ul);
x_21 = l_Option_getOrElse___main___rarg(x_19, x_20);
lean::dec(x_19);
x_23 = l_Lean_FileMap_toPosition(x_17, x_21);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_26 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_27 = l_Lean_KVMap_setNat(x_12, x_26, x_24);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_32 = l_Lean_KVMap_setNat(x_27, x_31, x_28);
x_33 = lean_expr_mk_mdata(x_32, x_14);
x_10 = x_33;
goto lbl_11;
}
default:
{
x_10 = x_1;
goto lbl_11;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_10);
x_38 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_40 = x_9;
} else {
 lean::inc(x_38);
 lean::dec(x_9);
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
obj* x_42; obj* x_45; obj* x_47; obj* x_51; 
x_42 = lean::cnstr_get(x_9, 0);
lean::inc(x_42);
lean::dec(x_9);
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
lean::inc(x_3);
x_51 = l_Lean_Elaborator_getNamespace(x_2, x_3, x_47);
if (lean::obj_tag(x_51) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_45);
x_57 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_59 = x_51;
} else {
 lean::inc(x_57);
 lean::dec(x_51);
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
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_69; obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_94; obj* x_97; obj* x_98; obj* x_101; 
x_61 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_63 = x_51;
} else {
 lean::inc(x_61);
 lean::dec(x_51);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_5, 0);
lean::inc(x_69);
lean::dec(x_5);
x_72 = lean::cnstr_get(x_4, 8);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_4, 9);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_45, 3);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_76, 0);
lean::inc(x_78);
lean::dec(x_76);
x_81 = l_List_reverse___rarg(x_78);
x_82 = lean::cnstr_get(x_45, 4);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_87 = l_List_reverse___rarg(x_84);
x_88 = lean::cnstr_get(x_45, 5);
lean::inc(x_88);
x_90 = l_RBTree_toList___rarg(x_88);
x_91 = lean::cnstr_get(x_45, 8);
lean::inc(x_91);
lean::dec(x_45);
x_94 = lean::cnstr_get(x_4, 10);
lean::inc(x_94);
lean::dec(x_4);
x_97 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_97, 0, x_72);
lean::cnstr_set(x_97, 1, x_74);
lean::cnstr_set(x_97, 2, x_81);
lean::cnstr_set(x_97, 3, x_87);
lean::cnstr_set(x_97, 4, x_90);
lean::cnstr_set(x_97, 5, x_91);
lean::cnstr_set(x_97, 6, x_94);
lean::cnstr_set(x_97, 7, x_64);
x_98 = lean_elaborator_elaborate_command(x_69, x_10, x_97);
lean::dec(x_97);
lean::dec(x_69);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_106 = x_98;
} else {
 lean::inc(x_104);
 lean::dec(x_98);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_66, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_66, 1);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_66, 2);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_66, 3);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_66, 4);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_66, 5);
lean::inc(x_117);
x_119 = l_List_append___rarg(x_104, x_117);
x_120 = lean::cnstr_get(x_66, 6);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_66, 7);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_66, 8);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_66, 9);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_66, 10);
lean::inc(x_128);
lean::dec(x_66);
x_131 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_131, 0, x_107);
lean::cnstr_set(x_131, 1, x_109);
lean::cnstr_set(x_131, 2, x_111);
lean::cnstr_set(x_131, 3, x_113);
lean::cnstr_set(x_131, 4, x_115);
lean::cnstr_set(x_131, 5, x_119);
lean::cnstr_set(x_131, 6, x_120);
lean::cnstr_set(x_131, 7, x_122);
lean::cnstr_set(x_131, 8, x_124);
lean::cnstr_set(x_131, 9, x_126);
lean::cnstr_set(x_131, 10, x_128);
x_132 = lean::box(0);
if (lean::is_scalar(x_106)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_106;
}
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_131);
if (lean::is_scalar(x_63)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_63;
}
lean::cnstr_set(x_134, 0, x_133);
return x_134;
}
else
{
obj* x_136; obj* x_139; obj* x_143; obj* x_144; 
lean::dec(x_63);
x_136 = lean::cnstr_get(x_98, 1);
lean::inc(x_136);
lean::dec(x_98);
x_139 = lean::cnstr_get(x_101, 0);
lean::inc(x_139);
lean::dec(x_101);
lean::inc(x_139);
x_143 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_oldElabCommand___lambda__1), 2, 1);
lean::closure_set(x_143, 0, x_139);
x_144 = l_Lean_Elaborator_modifyCurrentScope(x_143, x_2, x_3, x_66);
if (lean::obj_tag(x_144) == 0)
{
obj* x_147; obj* x_149; obj* x_150; 
lean::dec(x_139);
lean::dec(x_136);
x_147 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_149 = x_144;
} else {
 lean::inc(x_147);
 lean::dec(x_144);
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
obj* x_151; obj* x_153; obj* x_154; obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_169; obj* x_171; obj* x_174; obj* x_176; obj* x_178; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_151 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_153 = x_144;
} else {
 lean::inc(x_151);
 lean::dec(x_144);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_151, 1);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 x_156 = x_151;
} else {
 lean::inc(x_154);
 lean::dec(x_151);
 x_156 = lean::box(0);
}
x_157 = lean::cnstr_get(x_154, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_154, 1);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_154, 2);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_154, 3);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_154, 4);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_154, 5);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_154, 6);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_154, 7);
lean::inc(x_171);
lean::dec(x_154);
x_174 = lean::cnstr_get(x_139, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_139, 1);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_139, 6);
lean::inc(x_178);
lean::dec(x_139);
x_181 = l_List_append___rarg(x_136, x_167);
x_182 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_182, 0, x_157);
lean::cnstr_set(x_182, 1, x_159);
lean::cnstr_set(x_182, 2, x_161);
lean::cnstr_set(x_182, 3, x_163);
lean::cnstr_set(x_182, 4, x_165);
lean::cnstr_set(x_182, 5, x_181);
lean::cnstr_set(x_182, 6, x_169);
lean::cnstr_set(x_182, 7, x_171);
lean::cnstr_set(x_182, 8, x_174);
lean::cnstr_set(x_182, 9, x_176);
lean::cnstr_set(x_182, 10, x_178);
x_183 = lean::box(0);
if (lean::is_scalar(x_156)) {
 x_184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_184 = x_156;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_182);
if (lean::is_scalar(x_153)) {
 x_185 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_185 = x_153;
}
lean::cnstr_set(x_185, 0, x_184);
return x_185;
}
}
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
obj* x_4; obj* x_5; obj* x_7; obj* x_9; uint8 x_11; obj* x_13; uint8 x_15; obj* x_17; obj* x_20; 
x_4 = lean::box(0);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
x_11 = l_Option_isSome___main___rarg(x_9);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_0, 4);
lean::inc(x_13);
x_15 = l_Option_isSome___main___rarg(x_13);
lean::dec(x_13);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_4;
goto lbl_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_7, 0);
lean::inc(x_22);
lean::dec(x_7);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; 
lean::dec(x_22);
x_26 = l_Lean_Elaborator_declModifiersToPexpr___closed__3;
x_20 = x_26;
goto lbl_21;
}
else
{
obj* x_28; 
lean::dec(x_22);
x_28 = l_Lean_Elaborator_declModifiersToPexpr___closed__4;
x_20 = x_28;
goto lbl_21;
}
}
}
else
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_5, 0);
lean::inc(x_29);
lean::dec(x_5);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_32) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_4;
goto lbl_21;
}
else
{
obj* x_35; 
x_35 = lean::cnstr_get(x_7, 0);
lean::inc(x_35);
lean::dec(x_7);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; 
lean::dec(x_35);
x_39 = l_Lean_Elaborator_declModifiersToPexpr___closed__3;
x_20 = x_39;
goto lbl_21;
}
else
{
obj* x_41; 
lean::dec(x_35);
x_41 = l_Lean_Elaborator_declModifiersToPexpr___closed__4;
x_20 = x_41;
goto lbl_21;
}
}
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_32, 0);
lean::inc(x_42);
lean::dec(x_32);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_Lean_Elaborator_declModifiersToPexpr___closed__5;
x_49 = l_Lean_KVMap_setString(x_4, x_48, x_45);
if (lean::obj_tag(x_7) == 0)
{
x_20 = x_49;
goto lbl_21;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_7, 0);
lean::inc(x_50);
lean::dec(x_7);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; uint8 x_55; obj* x_56; 
lean::dec(x_50);
x_54 = l_Lean_Elaborator_declModifiersToPexpr___closed__6;
x_55 = 1;
x_56 = l_Lean_KVMap_setBool(x_49, x_54, x_55);
x_20 = x_56;
goto lbl_21;
}
else
{
obj* x_58; uint8 x_59; obj* x_60; 
lean::dec(x_50);
x_58 = l_Lean_Elaborator_declModifiersToPexpr___closed__7;
x_59 = 1;
x_60 = l_Lean_KVMap_setBool(x_49, x_58, x_59);
x_20 = x_60;
goto lbl_21;
}
}
}
}
lbl_21:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = l_Lean_Elaborator_declModifiersToPexpr___closed__1;
x_62 = l_Lean_KVMap_setBool(x_20, x_61, x_11);
x_63 = l_Lean_Elaborator_declModifiersToPexpr___closed__2;
x_64 = l_Lean_KVMap_setBool(x_62, x_63, x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_65; 
x_65 = l_Lean_Elaborator_attrsToPexpr(x_4, x_1, x_2, x_3);
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
x_79 = lean_expr_mk_mdata(x_64, x_74);
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
else
{
obj* x_82; obj* x_85; obj* x_88; 
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
lean::dec(x_17);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_Lean_Elaborator_attrsToPexpr(x_85, x_1, x_2, x_3);
if (lean::obj_tag(x_88) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_64);
x_90 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_92 = x_88;
} else {
 lean::inc(x_90);
 lean::dec(x_88);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
x_102 = lean_expr_mk_mdata(x_64, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
if (lean::is_scalar(x_96)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_96;
}
lean::cnstr_set(x_104, 0, x_103);
return x_104;
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
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_30 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_10, x_1, x_2, x_27);
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
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_18 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_15, x_2, x_3, x_4);
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
x_60 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2(x_0, x_12, x_2, x_3, x_56);
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
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__3(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__3(x_4);
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_23 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_14, x_2, x_3);
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
x_26 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_8, x_2, x_3);
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
x_45 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_35, x_2, x_3);
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
x_51 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_35, x_2, x_3);
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
x_54 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_29, x_2, x_3);
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
x_60 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_29, x_2, x_3);
x_61 = l_RBNode_balance1___main___rarg(x_59, x_60);
return x_61;
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__7(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
x_17 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6(x_3, x_10, x_1, x_16);
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
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__9(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__9(x_4);
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
obj* l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__10(obj* x_0, obj* x_1) {
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
x_9 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__11(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__11(x_4);
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
x_13 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__9(x_10);
x_14 = l_List_foldl___main___at_Lean_Elaborator_elabDefLike___spec__10(x_8, x_13);
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
x_100 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__3(x_97);
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
x_165 = l_List_map___main___at_Lean_Elaborator_elabDefLike___spec__11(x_162);
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
x_220 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2(x_175, x_216, x_4, x_5, x_168);
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
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mmap___main___at_Lean_Elaborator_elabDefLike___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
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
obj* l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_Elaborator_elabDefLike___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_Elaborator_elabDefLike___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_insert___main___at_Lean_Elaborator_elabDefLike___spec__5(x_0, x_1, x_2, x_3);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_4);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_4);
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
obj* l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__6(obj* x_0, obj* x_1) {
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
x_9 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__7(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__7(x_4);
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8(x_10, x_1, x_2, x_30);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__9(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__9(x_4);
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_121 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10(x_0, x_1, x_14, x_3, x_4, x_117);
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
x_146 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__9(x_144);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__11(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__11(x_4);
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
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__12(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__12(x_4);
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
obj* l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__13(obj* x_0, obj* x_1) {
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
x_9 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(x_0, x_2, x_8);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__14(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__14(x_4);
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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__2(obj* x_0, obj* x_1) {
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
x_13 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__5(x_10);
x_14 = l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__6(x_8, x_13);
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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
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
x_92 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__4(x_89);
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
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__2), 2, 1);
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
x_162 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__7(x_159);
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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__4(obj* x_0, obj* x_1) {
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
x_13 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__12(x_10);
x_14 = l_List_foldl___main___at_Lean_Elaborator_Declaration_elaborate___spec__13(x_8, x_13);
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_inferModToPexpr(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("mk");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
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
x_59 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__11(x_56);
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
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__4), 2, 1);
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
x_129 = l_List_map___main___at_Lean_Elaborator_Declaration_elaborate___spec__14(x_126);
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
x_175 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8(x_168, x_11, x_12, x_156);
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
x_203 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10(x_2, x_199, x_3, x_11, x_12, x_196);
if (lean::obj_tag(x_4) == 0)
{
obj* x_206; 
x_206 = l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2;
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
x_240 = l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1;
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
obj* _init_l_Lean_Elaborator_Declaration_elaborate___closed__2() {
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
obj* x_47; obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_47 = lean::cnstr_get(x_12, 0);
lean::inc(x_47);
lean::dec(x_12);
x_50 = lean::cnstr_get(x_11, 0);
lean::inc(x_50);
lean::dec(x_11);
x_53 = lean::box(0);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_57 = l_Option_getOrElse___main___rarg(x_54, x_56);
lean::dec(x_54);
x_59 = lean::cnstr_get(x_47, 2);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
lean::dec(x_59);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_63);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::cnstr_get(x_47, 3);
lean::inc(x_68);
lean::dec(x_47);
x_71 = l_Lean_Elaborator_Declaration_elaborate___closed__2;
x_72 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_53);
lean::cnstr_set(x_72, 2, x_57);
lean::cnstr_set(x_72, 3, x_67);
lean::cnstr_set(x_72, 4, x_68);
x_73 = lean::mk_nat_obj(4ul);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_74, 0, x_0);
lean::closure_set(x_74, 1, x_50);
lean::closure_set(x_74, 2, x_72);
lean::closure_set(x_74, 3, x_73);
x_75 = l_Lean_Elaborator_locally(x_74, x_1, x_2, x_3);
return x_75;
}
case 2:
{
obj* x_76; obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_76 = lean::cnstr_get(x_12, 0);
lean::inc(x_76);
lean::dec(x_12);
x_79 = lean::cnstr_get(x_11, 0);
lean::inc(x_79);
lean::dec(x_11);
x_82 = lean::box(0);
x_83 = lean::cnstr_get(x_76, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_83, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_83, 1);
lean::inc(x_87);
lean::dec(x_83);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_85);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::cnstr_get(x_76, 2);
lean::inc(x_92);
lean::dec(x_76);
x_95 = l_Lean_Elaborator_Declaration_elaborate___closed__2;
x_96 = l_Lean_Elaborator_Declaration_elaborate___closed__1;
x_97 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_82);
lean::cnstr_set(x_97, 2, x_96);
lean::cnstr_set(x_97, 3, x_91);
lean::cnstr_set(x_97, 4, x_92);
x_98 = lean::mk_nat_obj(3ul);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_elabDefLike___boxed), 7, 4);
lean::closure_set(x_99, 0, x_0);
lean::closure_set(x_99, 1, x_79);
lean::closure_set(x_99, 2, x_97);
lean::closure_set(x_99, 3, x_98);
x_100 = l_Lean_Elaborator_locally(x_99, x_1, x_2, x_3);
return x_100;
}
case 3:
{
obj* x_101; obj* x_104; obj* x_106; 
x_101 = lean::cnstr_get(x_12, 0);
lean::inc(x_101);
lean::dec(x_12);
x_104 = lean::cnstr_get(x_101, 2);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_104, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_112; 
lean::dec(x_11);
lean::dec(x_104);
lean::dec(x_106);
lean::dec(x_101);
x_112 = lean::box(0);
x_4 = x_112;
goto lbl_5;
}
else
{
obj* x_113; 
x_113 = lean::cnstr_get(x_106, 0);
lean::inc(x_113);
lean::dec(x_106);
if (lean::obj_tag(x_113) == 0)
{
obj* x_116; obj* x_119; obj* x_122; obj* x_123; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_116 = lean::cnstr_get(x_101, 1);
lean::inc(x_116);
lean::dec(x_101);
x_119 = lean::cnstr_get(x_104, 1);
lean::inc(x_119);
lean::dec(x_104);
x_122 = lean::box(0);
x_123 = lean::cnstr_get(x_11, 0);
lean::inc(x_123);
lean::dec(x_11);
x_126 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_126, 0, x_123);
x_127 = l_Lean_Elaborator_Declaration_elaborate___closed__3;
x_128 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__1___boxed), 9, 5);
lean::closure_set(x_128, 0, x_119);
lean::closure_set(x_128, 1, x_116);
lean::closure_set(x_128, 2, x_122);
lean::closure_set(x_128, 3, x_127);
lean::closure_set(x_128, 4, x_0);
x_129 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_129, 0, x_126);
lean::closure_set(x_129, 1, x_128);
x_130 = l_Lean_Elaborator_locally(x_129, x_1, x_2, x_3);
return x_130;
}
else
{
obj* x_135; 
lean::dec(x_11);
lean::dec(x_113);
lean::dec(x_104);
lean::dec(x_101);
x_135 = lean::box(0);
x_4 = x_135;
goto lbl_5;
}
}
}
case 4:
{
obj* x_136; obj* x_139; 
x_136 = lean::cnstr_get(x_12, 0);
lean::inc(x_136);
lean::dec(x_12);
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_141; obj* x_143; 
x_141 = lean::cnstr_get(x_136, 4);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_141, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_149; 
lean::dec(x_143);
lean::dec(x_141);
lean::dec(x_11);
lean::dec(x_136);
x_149 = lean::box(0);
x_4 = x_149;
goto lbl_5;
}
else
{
obj* x_150; obj* x_152; obj* x_154; obj* x_157; obj* x_160; obj* x_163; obj* x_164; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_150 = lean::cnstr_get(x_136, 2);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_136, 3);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_136, 6);
lean::inc(x_154);
lean::dec(x_136);
x_157 = lean::cnstr_get(x_141, 1);
lean::inc(x_157);
lean::dec(x_141);
x_160 = lean::cnstr_get(x_143, 0);
lean::inc(x_160);
lean::dec(x_143);
x_163 = lean::box(0);
x_164 = lean::cnstr_get(x_11, 0);
lean::inc(x_164);
lean::dec(x_11);
lean::inc(x_164);
x_168 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_168, 0, x_164);
x_169 = l_Lean_Elaborator_Declaration_elaborate___closed__4;
x_170 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed), 13, 9);
lean::closure_set(x_170, 0, x_163);
lean::closure_set(x_170, 1, x_160);
lean::closure_set(x_170, 2, x_0);
lean::closure_set(x_170, 3, x_154);
lean::closure_set(x_170, 4, x_152);
lean::closure_set(x_170, 5, x_169);
lean::closure_set(x_170, 6, x_150);
lean::closure_set(x_170, 7, x_157);
lean::closure_set(x_170, 8, x_164);
x_171 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_171, 0, x_168);
lean::closure_set(x_171, 1, x_170);
x_172 = l_Lean_Elaborator_locally(x_171, x_1, x_2, x_3);
return x_172;
}
}
else
{
obj* x_176; 
lean::dec(x_11);
lean::dec(x_139);
lean::dec(x_136);
x_176 = lean::box(0);
x_4 = x_176;
goto lbl_5;
}
}
default:
{
obj* x_177; obj* x_180; 
x_177 = lean::cnstr_get(x_12, 0);
lean::inc(x_177);
lean::dec(x_12);
x_180 = lean::cnstr_get(x_177, 0);
lean::inc(x_180);
if (lean::obj_tag(x_180) == 0)
{
obj* x_183; obj* x_185; 
lean::dec(x_180);
x_183 = lean::cnstr_get(x_177, 3);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_183, 0);
lean::inc(x_185);
if (lean::obj_tag(x_185) == 0)
{
obj* x_191; 
lean::dec(x_183);
lean::dec(x_177);
lean::dec(x_185);
lean::dec(x_11);
x_191 = lean::box(0);
x_4 = x_191;
goto lbl_5;
}
else
{
obj* x_192; obj* x_194; obj* x_196; obj* x_198; obj* x_200; obj* x_203; obj* x_206; obj* x_209; obj* x_210; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
x_192 = lean::cnstr_get(x_177, 1);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_177, 2);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_177, 4);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_177, 6);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_177, 7);
lean::inc(x_200);
lean::dec(x_177);
x_203 = lean::cnstr_get(x_183, 1);
lean::inc(x_203);
lean::dec(x_183);
x_206 = lean::cnstr_get(x_185, 0);
lean::inc(x_206);
lean::dec(x_185);
x_209 = lean::box(0);
x_210 = lean::cnstr_get(x_11, 0);
lean::inc(x_210);
lean::dec(x_11);
x_213 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_declModifiersToPexpr___boxed), 4, 1);
lean::closure_set(x_213, 0, x_210);
x_214 = l_Lean_Elaborator_Declaration_elaborate___closed__5;
x_215 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__5___boxed), 14, 10);
lean::closure_set(x_215, 0, x_206);
lean::closure_set(x_215, 1, x_194);
lean::closure_set(x_215, 2, x_0);
lean::closure_set(x_215, 3, x_200);
lean::closure_set(x_215, 4, x_198);
lean::closure_set(x_215, 5, x_209);
lean::closure_set(x_215, 6, x_214);
lean::closure_set(x_215, 7, x_196);
lean::closure_set(x_215, 8, x_192);
lean::closure_set(x_215, 9, x_203);
x_216 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Elaborator_Declaration_elaborate___spec__1___rarg), 5, 2);
lean::closure_set(x_216, 0, x_213);
lean::closure_set(x_216, 1, x_215);
x_217 = l_Lean_Elaborator_locally(x_216, x_1, x_2, x_3);
return x_217;
}
}
else
{
obj* x_221; 
lean::dec(x_180);
lean::dec(x_177);
lean::dec(x_11);
x_221 = lean::box(0);
x_4 = x_221;
goto lbl_5;
}
}
}
lbl_5:
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_4);
x_223 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_223, 0, x_0);
x_224 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__2___closed__1;
x_225 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg___boxed), 5, 2);
lean::closure_set(x_225, 0, x_223);
lean::closure_set(x_225, 1, x_224);
x_226 = l_Lean_Elaborator_locally(x_225, x_1, x_2, x_3);
return x_226;
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
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mmap___main___at_Lean_Elaborator_Declaration_elaborate___spec__10(x_0, x_1, x_2, x_3, x_4, x_5);
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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
obj* x_13; 
x_13 = l_Lean_Elaborator_Declaration_elaborate___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_10);
return x_13;
}
}
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
x_14 = l_Lean_Elaborator_Declaration_elaborate___lambda__5(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
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
x_39 = l_Lean_Parser_Trie_insert___rarg(x_27, x_33, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_25);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::cnstr_get(x_0, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_0, 2);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 3);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_0, 4);
lean::inc(x_47);
lean::dec(x_0);
x_50 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_50, 0, x_40);
lean::cnstr_set(x_50, 1, x_41);
lean::cnstr_set(x_50, 2, x_43);
lean::cnstr_set(x_50, 3, x_45);
lean::cnstr_set(x_50, 4, x_47);
x_0 = x_50;
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
obj* l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__6(obj* x_0) {
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
x_8 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__6(x_4);
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
x_134 = l_List_map___main___at_Lean_Elaborator_CommandParserConfig_registerNotationParser___spec__6(x_52);
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
x_1 = l_Lean_Parser_Syntax_reprintLst___main___closed__1;
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
obj* x_2; obj* x_4; uint8 x_6; obj* x_7; uint8 x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_6 = l_Option_isSome___main___rarg(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = l_Option_isSome___main___rarg(x_7);
lean::dec(x_7);
if (x_6 == 0)
{
if (x_9 == 0)
{
obj* x_11; 
x_11 = lean::box(0);
x_4 = x_11;
goto lbl_5;
}
else
{
obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
}
else
{
if (x_9 == 0)
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_19 = lean::box(0);
return x_19;
}
else
{
obj* x_20; 
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
obj* l_Lean_Elaborator_notation_elaborateAux___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_Lean_Elaborator_matchSpec(x_2, x_5);
return x_8;
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
obj* x_5; obj* x_6; obj* x_8; 
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_notation_elaborateAux___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = l_List_filterMap___main___rarg(x_5, x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 2);
lean::inc(x_14);
x_16 = l_Lean_Elaborator_postprocessNotationSpec(x_14);
x_17 = lean::cnstr_get(x_0, 3);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 4);
lean::inc(x_19);
lean::dec(x_0);
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_16);
lean::cnstr_set(x_22, 3, x_17);
lean::cnstr_set(x_22, 4, x_19);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_3);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_8, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_2);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
lean::dec(x_8);
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 3);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 4);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_Lean_Elaborator_postprocessNotationSpec(x_28);
x_41 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_41, 0, x_31);
lean::cnstr_set(x_41, 1, x_33);
lean::cnstr_set(x_41, 2, x_40);
lean::cnstr_set(x_41, 3, x_35);
lean::cnstr_set(x_41, 4, x_37);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_3);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
else
{
obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_8);
lean::dec(x_25);
x_46 = l_Lean_Parser_command_notation_HasView;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_0);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = l_Lean_Elaborator_notation_elaborateAux___closed__1;
x_53 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_51, x_52, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_58 = x_53;
} else {
 lean::inc(x_56);
 lean::dec(x_53);
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
obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_81; obj* x_82; 
x_60 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 x_62 = x_53;
} else {
 lean::inc(x_60);
 lean::dec(x_53);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_60, 0);
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_67 = x_60;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_63, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_63, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_63, 2);
lean::inc(x_72);
x_74 = l_Lean_Elaborator_postprocessNotationSpec(x_72);
x_75 = lean::cnstr_get(x_63, 3);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_63, 4);
lean::inc(x_77);
lean::dec(x_63);
x_80 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_80, 0, x_68);
lean::cnstr_set(x_80, 1, x_70);
lean::cnstr_set(x_80, 2, x_74);
lean::cnstr_set(x_80, 3, x_75);
lean::cnstr_set(x_80, 4, x_77);
if (lean::is_scalar(x_67)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_67;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_65);
if (lean::is_scalar(x_62)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_62;
}
lean::cnstr_set(x_82, 0, x_81);
return x_82;
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
x_12 = l_Lean_Elaborator_OrderedRBMap_insert___at_Lean_Elaborator_elabDefLike___spec__4(x_8, x_0, x_11);
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
x_33 = l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_toLevel___main___spec__5(x_30, x_29);
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
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_13; 
x_4 = l_Lean_Parser_command_attribute_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
lean::inc(x_0);
x_9 = lean::apply_1(x_5, x_0);
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
lean::inc(x_2);
x_13 = l_Lean_Elaborator_attrsToPexpr(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_19 = x_13;
} else {
 lean::inc(x_17);
 lean::dec(x_13);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_29; obj* x_32; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = lean::cnstr_get(x_9, 5);
lean::inc(x_29);
lean::inc(x_2);
x_32 = l_List_mmap___main___at_Lean_Elaborator_attribute_elaborate___spec__1(x_29, x_1, x_2, x_26);
if (lean::obj_tag(x_32) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_24);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_37 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_39 = x_32;
} else {
 lean::inc(x_37);
 lean::dec(x_32);
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
obj* x_41; obj* x_44; obj* x_46; obj* x_49; uint8 x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_41 = lean::cnstr_get(x_32, 0);
lean::inc(x_41);
lean::dec(x_32);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::cnstr_get(x_9, 0);
lean::inc(x_49);
lean::dec(x_9);
x_52 = l_Option_isSome___main___rarg(x_49);
lean::dec(x_49);
x_54 = l_Lean_Elaborator_attribute_elaborate___closed__1;
x_55 = l_Lean_Elaborator_attribute_elaborate___closed__2;
x_56 = l_Lean_KVMap_setBool(x_54, x_55, x_52);
x_57 = l_Lean_Elaborator_mkEqns___closed__1;
x_58 = l_Lean_Expr_mkCapp(x_57, x_44);
x_59 = lean_expr_mk_app(x_24, x_58);
x_60 = lean_expr_mk_mdata(x_56, x_59);
x_61 = l_Lean_Elaborator_oldElabCommand(x_0, x_60, x_1, x_2, x_46);
lean::dec(x_0);
return x_61;
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
obj* l_List_mmap_x_27___main___at_Lean_Elaborator_noKind_elaborate___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_19 = l_List_mmap_x_27___main___at_Lean_Elaborator_noKind_elaborate___spec__1(x_16, x_1, x_2, x_3);
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
obj* x_19; obj* x_22; obj* x_23; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_35; uint8 x_37; 
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
x_31 = l_Lean_Elaborator_end_elaborate___closed__2;
x_32 = l_Option_getOrElse___main___rarg(x_28, x_31);
lean::dec(x_28);
x_34 = l_Lean_Elaborator_mangleIdent(x_32);
x_35 = lean::cnstr_get(x_19, 1);
lean::inc(x_35);
x_37 = lean_name_dec_eq(x_34, x_35);
lean::dec(x_34);
if (x_37 == 0)
{
obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_55; 
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_0);
x_40 = lean::cnstr_get(x_19, 0);
lean::inc(x_40);
lean::dec(x_19);
x_43 = l_Lean_Elaborator_end_elaborate___closed__3;
x_44 = lean::string_append(x_43, x_40);
lean::dec(x_40);
x_46 = l_Lean_Elaborator_end_elaborate___closed__4;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_Lean_Name_toString___closed__1;
x_49 = l_Lean_Name_toStringWithSep___main(x_48, x_35);
x_50 = lean::string_append(x_47, x_49);
lean::dec(x_49);
x_52 = l_Char_HasRepr___closed__1;
x_53 = lean::string_append(x_50, x_52);
lean::inc(x_2);
x_55 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_39, x_53, x_1, x_2, x_3);
lean::dec(x_39);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
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
obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_55);
x_65 = lean::cnstr_get(x_3, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_3, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_3, 2);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_3, 3);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_3, 5);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_3, 6);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_3, 7);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_3, 8);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_3, 9);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_3, 10);
lean::inc(x_83);
lean::dec(x_3);
x_86 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_86, 0, x_65);
lean::cnstr_set(x_86, 1, x_67);
lean::cnstr_set(x_86, 2, x_69);
lean::cnstr_set(x_86, 3, x_71);
lean::cnstr_set(x_86, 4, x_11);
lean::cnstr_set(x_86, 5, x_73);
lean::cnstr_set(x_86, 6, x_75);
lean::cnstr_set(x_86, 7, x_77);
lean::cnstr_set(x_86, 8, x_79);
lean::cnstr_set(x_86, 9, x_81);
lean::cnstr_set(x_86, 10, x_83);
x_87 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_86);
return x_87;
}
}
else
{
obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_112; obj* x_113; 
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_35);
x_91 = lean::cnstr_get(x_3, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_3, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_3, 2);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_3, 3);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_3, 5);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_3, 6);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_3, 7);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_3, 8);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_3, 9);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_3, 10);
lean::inc(x_109);
lean::dec(x_3);
x_112 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_112, 0, x_91);
lean::cnstr_set(x_112, 1, x_93);
lean::cnstr_set(x_112, 2, x_95);
lean::cnstr_set(x_112, 3, x_97);
lean::cnstr_set(x_112, 4, x_11);
lean::cnstr_set(x_112, 5, x_99);
lean::cnstr_set(x_112, 6, x_101);
lean::cnstr_set(x_112, 7, x_103);
lean::cnstr_set(x_112, 8, x_105);
lean::cnstr_set(x_112, 9, x_107);
lean::cnstr_set(x_112, 10, x_109);
x_113 = l_Lean_Elaborator_updateParserConfig(x_1, x_2, x_112);
return x_113;
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
obj* l_Lean_Elaborator_section_elaborate(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_currentScope(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
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
x_18 = l_Lean_Parser_command_section_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_0);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = l_Lean_Elaborator_end_elaborate___closed__2;
x_27 = l_Option_getOrElse___main___rarg(x_23, x_26);
lean::dec(x_23);
x_29 = l_Lean_Elaborator_mangleIdent(x_27);
x_30 = lean::cnstr_get(x_15, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_15, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_15, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 3);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_13, 2);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_13, 3);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_13, 4);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_13, 5);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_13, 6);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_13, 7);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_13, 8);
lean::inc(x_50);
lean::dec(x_13);
x_53 = l_Lean_Elaborator_section_elaborate___closed__1;
x_54 = lean::alloc_cnstr(0, 9, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_29);
lean::cnstr_set(x_54, 2, x_38);
lean::cnstr_set(x_54, 3, x_40);
lean::cnstr_set(x_54, 4, x_42);
lean::cnstr_set(x_54, 5, x_44);
lean::cnstr_set(x_54, 6, x_46);
lean::cnstr_set(x_54, 7, x_48);
lean::cnstr_set(x_54, 8, x_50);
x_55 = lean::cnstr_get(x_15, 4);
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::cnstr_get(x_15, 5);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_15, 6);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_15, 7);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_15, 8);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_15, 9);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_15, 10);
lean::inc(x_68);
lean::dec(x_15);
x_71 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_71, 0, x_30);
lean::cnstr_set(x_71, 1, x_32);
lean::cnstr_set(x_71, 2, x_34);
lean::cnstr_set(x_71, 3, x_36);
lean::cnstr_set(x_71, 4, x_57);
lean::cnstr_set(x_71, 5, x_58);
lean::cnstr_set(x_71, 6, x_60);
lean::cnstr_set(x_71, 7, x_62);
lean::cnstr_set(x_71, 8, x_64);
lean::cnstr_set(x_71, 9, x_66);
lean::cnstr_set(x_71, 10, x_68);
x_72 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_17;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
if (lean::is_scalar(x_12)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_12;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
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
uint8 l_Lean_Elaborator_resolveContext___main___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_0, 8);
x_4 = l_Lean_Name_append___main(x_2, x_1);
x_5 = lean_environment_contains(x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
uint8 l_Lean_Elaborator_resolveContext___main___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_Lean_Elaborator_isOpenNamespace___main(x_0, x_2);
return x_3;
}
}
obj* l_Lean_Elaborator_resolveContext___main___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_Lean_Elaborator_matchOpenSpec(x_0, x_2);
return x_5;
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
obj* x_25; obj* x_26; obj* x_28; 
lean::inc(x_0);
lean::inc(x_3);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_resolveContext___main___lambda__1___boxed), 3, 2);
lean::closure_set(x_25, 0, x_3);
lean::closure_set(x_25, 1, x_0);
x_26 = lean::cnstr_get(x_15, 6);
lean::inc(x_26);
x_28 = l_List_filter___main___rarg(x_25, x_26);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_32; obj* x_33; uint8 x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_29 = l_Lean_Elaborator_resolveContext___main___closed__1;
x_30 = lean::box(0);
lean::inc(x_0);
x_32 = l_Lean_Name_replacePrefix___main(x_0, x_29, x_30);
x_33 = lean::cnstr_get(x_3, 8);
lean::inc(x_33);
x_35 = lean_environment_contains(x_33, x_32);
lean::inc(x_0);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_matchOpenSpec), 2, 1);
lean::closure_set(x_37, 0, x_0);
x_38 = lean::cnstr_get(x_15, 7);
lean::inc(x_38);
x_40 = l_List_filterMap___main___rarg(x_37, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_environment_contains___boxed), 2, 1);
lean::closure_set(x_41, 0, x_33);
lean::inc(x_41);
x_43 = l_List_filter___main___rarg(x_41, x_40);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_resolveContext___main___lambda__2___boxed), 2, 1);
lean::closure_set(x_44, 0, x_15);
x_45 = lean::cnstr_get(x_3, 3);
lean::inc(x_45);
lean::dec(x_3);
x_48 = l_List_filter___main___rarg(x_44, x_45);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_resolveContext___main___lambda__3), 2, 1);
lean::closure_set(x_49, 0, x_0);
x_50 = l_List_filterMap___main___rarg(x_49, x_48);
x_51 = l_List_filter___main___rarg(x_41, x_50);
if (x_35 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_32);
x_53 = l_List_append___rarg(x_28, x_43);
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
lean::cnstr_set(x_57, 0, x_32);
lean::cnstr_set(x_57, 1, x_28);
x_58 = l_List_append___rarg(x_57, x_43);
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
obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_3);
lean::dec(x_15);
x_64 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 1);
 x_66 = x_28;
} else {
 lean::inc(x_64);
 lean::dec(x_28);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Name_append___main(x_64, x_0);
lean::dec(x_64);
x_69 = lean::box(0);
if (lean::is_scalar(x_66)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_66;
}
lean::cnstr_set(x_70, 0, x_67);
lean::cnstr_set(x_70, 1, x_69);
if (lean::is_scalar(x_19)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_19;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_72 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_72 = x_14;
}
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
}
else
{
obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
lean::dec(x_19);
x_77 = lean::cnstr_get(x_22, 0);
lean::inc(x_77);
lean::dec(x_22);
x_80 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 x_82 = x_77;
} else {
 lean::inc(x_80);
 lean::dec(x_77);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::box(0);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set(x_87, 1, x_86);
if (lean::is_scalar(x_82)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_82;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_17);
if (lean::is_scalar(x_14)) {
 x_89 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_89 = x_14;
}
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
}
}
obj* l_Lean_Elaborator_resolveContext___main___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Elaborator_resolveContext___main___lambda__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elaborator_resolveContext___main___lambda__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Elaborator_resolveContext___main___lambda__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
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
x_13 = l_Lean_Expander_error___rarg___lambda__1___closed__1;
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
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_0, 0);
x_21 = l_Lean_Parser_Syntax_getPos(x_20);
x_22 = lean::mk_nat_obj(0ul);
x_23 = l_Option_getOrElse___main___rarg(x_21, x_22);
lean::dec(x_21);
x_25 = l_Lean_FileMap_toPosition(x_9, x_23);
x_26 = 2;
x_27 = l_String_splitAux___main___closed__1;
x_28 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_28, 0, x_7);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_12);
lean::cnstr_set(x_28, 3, x_27);
lean::cnstr_set(x_28, 4, x_1);
lean::cnstr_set_scalar(x_28, sizeof(void*)*5, x_26);
x_29 = x_28;
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
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
x_14 = l_Lean_Expander_error___rarg___lambda__1___closed__1;
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
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_0, 0);
x_22 = l_Lean_Parser_Syntax_getPos(x_21);
x_23 = lean::mk_nat_obj(0ul);
x_24 = l_Option_getOrElse___main___rarg(x_22, x_23);
lean::dec(x_22);
x_26 = l_Lean_FileMap_toPosition(x_10, x_24);
x_27 = 2;
x_28 = l_String_splitAux___main___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_1);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
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
x_0 = lean::mk_string("Elaborator.run: recursion depth exceeded");
return x_0;
}
}
obj* l_Lean_Elaborator_processCommand___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = l_Lean_Elaborator_processCommand___lambda__1___closed__1;
x_6 = l_Lean_Expander_error___at_Lean_Elaborator_processCommand___spec__1___rarg(x_4, x_5, x_2, x_3);
lean::dec(x_4);
return x_6;
}
}
obj* _init_l_Lean_Elaborator_processCommand___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("not a command: ");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_processCommand___lambda__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown command: ");
return x_0;
}
}
obj* l_Lean_Elaborator_processCommand___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = l_Lean_Elaborator_processCommand___lambda__2___closed__1;
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
x_29 = l_Lean_Elaborator_processCommand___lambda__2___closed__2;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_processCommand___lambda__2), 4, 0);
return x_0;
}
}
obj* l_Lean_Elaborator_processCommand(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
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
lean::inc(x_2);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_processCommand___lambda__1___boxed), 4, 1);
lean::closure_set(x_37, 0, x_2);
x_38 = l_Lean_Elaborator_processCommand___closed__1;
x_39 = lean::fixpoint(x_38, x_2);
lean::dec(x_37);
x_41 = lean::apply_2(x_39, x_0, x_35);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_24);
x_46 = lean::alloc_cnstr(0, 11, 0);
lean::cnstr_set(x_46, 0, x_3);
lean::cnstr_set(x_46, 1, x_5);
lean::cnstr_set(x_46, 2, x_7);
lean::cnstr_set(x_46, 3, x_9);
lean::cnstr_set(x_46, 4, x_11);
lean::cnstr_set(x_46, 5, x_45);
lean::cnstr_set(x_46, 6, x_13);
lean::cnstr_set(x_46, 7, x_15);
lean::cnstr_set(x_46, 8, x_17);
lean::cnstr_set(x_46, 9, x_19);
lean::cnstr_set(x_46, 10, x_21);
return x_46;
}
else
{
obj* x_57; obj* x_60; 
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
x_57 = lean::cnstr_get(x_41, 0);
lean::inc(x_57);
lean::dec(x_41);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
return x_60;
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
obj* l_Lean_Elaborator_processCommand___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elaborator_processCommand___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
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
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__1);
 l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2 = _init_l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2();
lean::mark_persistent(l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__5___closed__2);
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
 l_Lean_Elaborator_toPexpr___main___closed__47 = _init_l_Lean_Elaborator_toPexpr___main___closed__47();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__47);
 l_Lean_Elaborator_toPexpr___main___closed__48 = _init_l_Lean_Elaborator_toPexpr___main___closed__48();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__48);
 l_Lean_Elaborator_toPexpr___main___closed__49 = _init_l_Lean_Elaborator_toPexpr___main___closed__49();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__49);
 l_Lean_Elaborator_toPexpr___main___closed__50 = _init_l_Lean_Elaborator_toPexpr___main___closed__50();
lean::mark_persistent(l_Lean_Elaborator_toPexpr___main___closed__50);
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
 l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1 = _init_l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__1);
 l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2 = _init_l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2();
lean::mark_persistent(l_Lean_Elaborator_Declaration_elaborate___lambda__5___closed__2);
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
 l_Lean_Elaborator_processCommand___lambda__2___closed__1 = _init_l_Lean_Elaborator_processCommand___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__2___closed__1);
 l_Lean_Elaborator_processCommand___lambda__2___closed__2 = _init_l_Lean_Elaborator_processCommand___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Elaborator_processCommand___lambda__2___closed__2);
 l_Lean_Elaborator_processCommand___closed__1 = _init_l_Lean_Elaborator_processCommand___closed__1();
lean::mark_persistent(l_Lean_Elaborator_processCommand___closed__1);
return w;
}
