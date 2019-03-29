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
obj* l_Lean_Elaborator_Declaration_elaborate___lambda__4(obj*, obj*);
obj* l_Lean_Elaborator_elaboratorInh(obj*, obj*, obj*, obj*);
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
obj* l_Lean_Elaborator_elaboratorInh___closed__1;
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
obj* l_Lean_Elaborator_OrderedRBMap_find___at_Lean_Elaborator_variables_elaborate___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Elaborator_toPexpr___main___closed__17;
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
extern obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
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
obj* x_0; 
x_0 = lean::mk_string("unexpected item in structure instance notation");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__30() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed choice");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__31() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("choice");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__32() {
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
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrowed");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("innaccessible");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__35() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@@");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__36() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("fieldNotation");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__37() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed let");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__38() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__39() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean_expr_mk_bvar(x_0);
return x_1;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("show");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("have");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Elaborator_dummy;
x_2 = lean_expr_mk_mvar(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("anonymousConstructor");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__44() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = level_mk_succ(x_0);
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__45() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed pi");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__46() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ill-formed lambda");
return x_0;
}
}
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__47() {
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
obj* _init_l_Lean_Elaborator_toPexpr___main___closed__48() {
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
x_327 = lean::box(0);
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
obj* x_331; obj* x_334; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
x_331 = lean::cnstr_get(x_320, 0);
lean::inc(x_331);
lean::dec(x_320);
x_334 = lean::cnstr_get(x_331, 0);
lean::inc(x_334);
lean::dec(x_331);
x_337 = l_Lean_Elaborator_mangleIdent(x_334);
x_338 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_339 = l_Lean_KVMap_setName(x_319, x_338, x_337);
x_340 = lean_expr_mk_mdata(x_339, x_325);
if (lean::is_scalar(x_311)) {
 x_341 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_341 = x_311;
}
lean::cnstr_set(x_341, 0, x_340);
lean::cnstr_set(x_341, 1, x_309);
x_15 = x_341;
goto lbl_16;
}
}
}
}
else
{
obj* x_342; obj* x_344; 
x_342 = lean::cnstr_get(x_222, 0);
lean::inc(x_342);
x_344 = lean::cnstr_get(x_342, 0);
lean::inc(x_344);
lean::dec(x_342);
if (lean::obj_tag(x_344) == 0)
{
obj* x_347; obj* x_348; obj* x_351; obj* x_352; obj* x_355; obj* x_356; obj* x_357; obj* x_359; 
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 lean::cnstr_release(x_222, 1);
 x_347 = x_222;
} else {
 lean::dec(x_222);
 x_347 = lean::box(0);
}
x_348 = lean::cnstr_get(x_221, 0);
lean::inc(x_348);
lean::dec(x_221);
x_351 = l_Lean_Parser_Term_structInstItem_HasView;
x_352 = lean::cnstr_get(x_351, 1);
lean::inc(x_352);
lean::dec(x_351);
x_355 = lean::apply_1(x_352, x_344);
x_356 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_356, 0, x_355);
x_357 = l_Lean_Elaborator_toPexpr___main___closed__29;
lean::inc(x_2);
x_359 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_356, x_357, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_356);
if (lean::obj_tag(x_359) == 0)
{
obj* x_369; obj* x_371; obj* x_372; 
lean::dec(x_347);
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_215);
lean::dec(x_210);
x_369 = lean::cnstr_get(x_359, 0);
if (lean::is_exclusive(x_359)) {
 x_371 = x_359;
} else {
 lean::inc(x_369);
 lean::dec(x_359);
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
obj* x_373; obj* x_376; obj* x_378; obj* x_383; 
x_373 = lean::cnstr_get(x_359, 0);
lean::inc(x_373);
lean::dec(x_359);
x_376 = lean::cnstr_get(x_373, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_373, 1);
lean::inc(x_378);
lean::dec(x_373);
lean::inc(x_2);
lean::inc(x_0);
x_383 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__8(x_0, x_215, x_1, x_2, x_378);
if (lean::obj_tag(x_383) == 0)
{
obj* x_391; obj* x_393; obj* x_394; 
lean::dec(x_347);
lean::dec(x_348);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_391 = lean::cnstr_get(x_383, 0);
if (lean::is_exclusive(x_383)) {
 x_393 = x_383;
} else {
 lean::inc(x_391);
 lean::dec(x_383);
 x_393 = lean::box(0);
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_391);
return x_394;
}
else
{
obj* x_395; obj* x_398; obj* x_400; obj* x_403; obj* x_407; 
x_395 = lean::cnstr_get(x_383, 0);
lean::inc(x_395);
lean::dec(x_383);
x_398 = lean::cnstr_get(x_395, 0);
lean::inc(x_398);
x_400 = lean::cnstr_get(x_395, 1);
lean::inc(x_400);
lean::dec(x_395);
lean::inc(x_2);
lean::inc(x_0);
x_407 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__10(x_0, x_348, x_1, x_2, x_400);
if (lean::obj_tag(x_407) == 0)
{
obj* x_415; obj* x_417; obj* x_418; 
lean::dec(x_347);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_398);
lean::dec(x_210);
x_415 = lean::cnstr_get(x_407, 0);
if (lean::is_exclusive(x_407)) {
 x_417 = x_407;
} else {
 lean::inc(x_415);
 lean::dec(x_407);
 x_417 = lean::box(0);
}
if (lean::is_scalar(x_417)) {
 x_418 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_418 = x_417;
}
lean::cnstr_set(x_418, 0, x_415);
return x_418;
}
else
{
obj* x_419; obj* x_422; 
x_419 = lean::cnstr_get(x_407, 0);
lean::inc(x_419);
lean::dec(x_407);
x_422 = lean::cnstr_get(x_210, 2);
lean::inc(x_422);
if (lean::obj_tag(x_422) == 0)
{
obj* x_425; obj* x_427; obj* x_429; obj* x_430; 
lean::dec(x_347);
x_425 = lean::cnstr_get(x_419, 0);
x_427 = lean::cnstr_get(x_419, 1);
if (lean::is_exclusive(x_419)) {
 x_429 = x_419;
} else {
 lean::inc(x_425);
 lean::inc(x_427);
 lean::dec(x_419);
 x_429 = lean::box(0);
}
if (lean::is_scalar(x_429)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_429;
}
lean::cnstr_set(x_430, 0, x_425);
lean::cnstr_set(x_430, 1, x_427);
x_403 = x_430;
goto lbl_404;
}
else
{
obj* x_431; obj* x_433; obj* x_436; obj* x_439; obj* x_443; 
x_431 = lean::cnstr_get(x_419, 0);
lean::inc(x_431);
x_433 = lean::cnstr_get(x_419, 1);
lean::inc(x_433);
lean::dec(x_419);
x_436 = lean::cnstr_get(x_422, 0);
lean::inc(x_436);
lean::dec(x_422);
x_439 = lean::cnstr_get(x_436, 0);
lean::inc(x_439);
lean::dec(x_436);
lean::inc(x_2);
x_443 = l_Lean_Elaborator_toPexpr___main(x_439, x_1, x_2, x_433);
if (lean::obj_tag(x_443) == 0)
{
obj* x_452; obj* x_454; obj* x_455; 
lean::dec(x_347);
lean::dec(x_8);
lean::dec(x_376);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_431);
lean::dec(x_398);
lean::dec(x_210);
x_452 = lean::cnstr_get(x_443, 0);
if (lean::is_exclusive(x_443)) {
 x_454 = x_443;
} else {
 lean::inc(x_452);
 lean::dec(x_443);
 x_454 = lean::box(0);
}
if (lean::is_scalar(x_454)) {
 x_455 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_455 = x_454;
}
lean::cnstr_set(x_455, 0, x_452);
return x_455;
}
else
{
obj* x_456; obj* x_459; obj* x_461; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; 
x_456 = lean::cnstr_get(x_443, 0);
lean::inc(x_456);
lean::dec(x_443);
x_459 = lean::cnstr_get(x_456, 0);
x_461 = lean::cnstr_get(x_456, 1);
if (lean::is_exclusive(x_456)) {
 x_463 = x_456;
} else {
 lean::inc(x_459);
 lean::inc(x_461);
 lean::dec(x_456);
 x_463 = lean::box(0);
}
x_464 = lean::box(0);
if (lean::is_scalar(x_347)) {
 x_465 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_465 = x_347;
}
lean::cnstr_set(x_465, 0, x_459);
lean::cnstr_set(x_465, 1, x_464);
x_466 = l_List_append___rarg(x_431, x_465);
if (lean::is_scalar(x_463)) {
 x_467 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_467 = x_463;
}
lean::cnstr_set(x_467, 0, x_466);
lean::cnstr_set(x_467, 1, x_461);
x_403 = x_467;
goto lbl_404;
}
}
}
lbl_404:
{
obj* x_468; obj* x_470; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; uint8 x_479; obj* x_480; obj* x_481; obj* x_484; obj* x_485; obj* x_486; 
x_468 = lean::cnstr_get(x_403, 0);
x_470 = lean::cnstr_get(x_403, 1);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_set(x_403, 0, lean::box(0));
 lean::cnstr_set(x_403, 1, lean::box(0));
 x_472 = x_403;
} else {
 lean::inc(x_468);
 lean::inc(x_470);
 lean::dec(x_403);
 x_472 = lean::box(0);
}
x_473 = lean::mk_nat_obj(0ul);
x_474 = l_List_lengthAux___main___rarg(x_398, x_473);
x_475 = lean::box(0);
x_476 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_477 = l_Lean_KVMap_setNat(x_475, x_476, x_474);
x_478 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_479 = lean::unbox(x_376);
x_480 = l_Lean_KVMap_setBool(x_477, x_478, x_479);
x_481 = lean::cnstr_get(x_210, 1);
lean::inc(x_481);
lean::dec(x_210);
x_484 = l_List_append___rarg(x_398, x_468);
x_485 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_486 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__9(x_485, x_484);
if (lean::obj_tag(x_481) == 0)
{
obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; 
x_487 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_488 = lean::box(0);
x_489 = l_Lean_KVMap_setName(x_480, x_487, x_488);
x_490 = lean_expr_mk_mdata(x_489, x_486);
if (lean::is_scalar(x_472)) {
 x_491 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_491 = x_472;
}
lean::cnstr_set(x_491, 0, x_490);
lean::cnstr_set(x_491, 1, x_470);
x_15 = x_491;
goto lbl_16;
}
else
{
obj* x_492; obj* x_495; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; 
x_492 = lean::cnstr_get(x_481, 0);
lean::inc(x_492);
lean::dec(x_481);
x_495 = lean::cnstr_get(x_492, 0);
lean::inc(x_495);
lean::dec(x_492);
x_498 = l_Lean_Elaborator_mangleIdent(x_495);
x_499 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_500 = l_Lean_KVMap_setName(x_480, x_499, x_498);
x_501 = lean_expr_mk_mdata(x_500, x_486);
if (lean::is_scalar(x_472)) {
 x_502 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_502 = x_472;
}
lean::cnstr_set(x_502, 0, x_501);
lean::cnstr_set(x_502, 1, x_470);
x_15 = x_502;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_503; obj* x_505; 
x_503 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 lean::cnstr_set(x_222, 1, lean::box(0));
 x_505 = x_222;
} else {
 lean::inc(x_503);
 lean::dec(x_222);
 x_505 = lean::box(0);
}
if (lean::obj_tag(x_503) == 0)
{
obj* x_507; obj* x_512; 
lean::dec(x_344);
x_507 = lean::cnstr_get(x_221, 0);
lean::inc(x_507);
lean::dec(x_221);
lean::inc(x_2);
lean::inc(x_0);
x_512 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__11(x_0, x_215, x_1, x_2, x_3);
if (lean::obj_tag(x_512) == 0)
{
obj* x_519; obj* x_521; obj* x_522; 
lean::dec(x_507);
lean::dec(x_505);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_519 = lean::cnstr_get(x_512, 0);
if (lean::is_exclusive(x_512)) {
 x_521 = x_512;
} else {
 lean::inc(x_519);
 lean::dec(x_512);
 x_521 = lean::box(0);
}
if (lean::is_scalar(x_521)) {
 x_522 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_522 = x_521;
}
lean::cnstr_set(x_522, 0, x_519);
return x_522;
}
else
{
obj* x_523; obj* x_526; obj* x_528; obj* x_531; obj* x_535; 
x_523 = lean::cnstr_get(x_512, 0);
lean::inc(x_523);
lean::dec(x_512);
x_526 = lean::cnstr_get(x_523, 0);
lean::inc(x_526);
x_528 = lean::cnstr_get(x_523, 1);
lean::inc(x_528);
lean::dec(x_523);
lean::inc(x_2);
lean::inc(x_0);
x_535 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__13(x_0, x_507, x_1, x_2, x_528);
if (lean::obj_tag(x_535) == 0)
{
obj* x_542; obj* x_544; obj* x_545; 
lean::dec(x_505);
lean::dec(x_526);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_210);
x_542 = lean::cnstr_get(x_535, 0);
if (lean::is_exclusive(x_535)) {
 x_544 = x_535;
} else {
 lean::inc(x_542);
 lean::dec(x_535);
 x_544 = lean::box(0);
}
if (lean::is_scalar(x_544)) {
 x_545 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_545 = x_544;
}
lean::cnstr_set(x_545, 0, x_542);
return x_545;
}
else
{
obj* x_546; obj* x_549; 
x_546 = lean::cnstr_get(x_535, 0);
lean::inc(x_546);
lean::dec(x_535);
x_549 = lean::cnstr_get(x_210, 2);
lean::inc(x_549);
if (lean::obj_tag(x_549) == 0)
{
obj* x_552; obj* x_554; obj* x_556; obj* x_557; 
lean::dec(x_505);
x_552 = lean::cnstr_get(x_546, 0);
x_554 = lean::cnstr_get(x_546, 1);
if (lean::is_exclusive(x_546)) {
 x_556 = x_546;
} else {
 lean::inc(x_552);
 lean::inc(x_554);
 lean::dec(x_546);
 x_556 = lean::box(0);
}
if (lean::is_scalar(x_556)) {
 x_557 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_557 = x_556;
}
lean::cnstr_set(x_557, 0, x_552);
lean::cnstr_set(x_557, 1, x_554);
x_531 = x_557;
goto lbl_532;
}
else
{
obj* x_558; obj* x_560; obj* x_563; obj* x_566; obj* x_570; 
x_558 = lean::cnstr_get(x_546, 0);
lean::inc(x_558);
x_560 = lean::cnstr_get(x_546, 1);
lean::inc(x_560);
lean::dec(x_546);
x_563 = lean::cnstr_get(x_549, 0);
lean::inc(x_563);
lean::dec(x_549);
x_566 = lean::cnstr_get(x_563, 0);
lean::inc(x_566);
lean::dec(x_563);
lean::inc(x_2);
x_570 = l_Lean_Elaborator_toPexpr___main(x_566, x_1, x_2, x_560);
if (lean::obj_tag(x_570) == 0)
{
obj* x_578; obj* x_580; obj* x_581; 
lean::dec(x_505);
lean::dec(x_526);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_558);
lean::dec(x_210);
x_578 = lean::cnstr_get(x_570, 0);
if (lean::is_exclusive(x_570)) {
 x_580 = x_570;
} else {
 lean::inc(x_578);
 lean::dec(x_570);
 x_580 = lean::box(0);
}
if (lean::is_scalar(x_580)) {
 x_581 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_581 = x_580;
}
lean::cnstr_set(x_581, 0, x_578);
return x_581;
}
else
{
obj* x_582; obj* x_585; obj* x_587; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; 
x_582 = lean::cnstr_get(x_570, 0);
lean::inc(x_582);
lean::dec(x_570);
x_585 = lean::cnstr_get(x_582, 0);
x_587 = lean::cnstr_get(x_582, 1);
if (lean::is_exclusive(x_582)) {
 x_589 = x_582;
} else {
 lean::inc(x_585);
 lean::inc(x_587);
 lean::dec(x_582);
 x_589 = lean::box(0);
}
x_590 = lean::box(0);
if (lean::is_scalar(x_505)) {
 x_591 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_591 = x_505;
}
lean::cnstr_set(x_591, 0, x_585);
lean::cnstr_set(x_591, 1, x_590);
x_592 = l_List_append___rarg(x_558, x_591);
if (lean::is_scalar(x_589)) {
 x_593 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_593 = x_589;
}
lean::cnstr_set(x_593, 0, x_592);
lean::cnstr_set(x_593, 1, x_587);
x_531 = x_593;
goto lbl_532;
}
}
}
lbl_532:
{
obj* x_594; obj* x_596; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; uint8 x_605; obj* x_606; obj* x_607; obj* x_610; obj* x_611; obj* x_612; 
x_594 = lean::cnstr_get(x_531, 0);
x_596 = lean::cnstr_get(x_531, 1);
if (lean::is_exclusive(x_531)) {
 lean::cnstr_set(x_531, 0, lean::box(0));
 lean::cnstr_set(x_531, 1, lean::box(0));
 x_598 = x_531;
} else {
 lean::inc(x_594);
 lean::inc(x_596);
 lean::dec(x_531);
 x_598 = lean::box(0);
}
x_599 = lean::mk_nat_obj(0ul);
x_600 = l_List_lengthAux___main___rarg(x_526, x_599);
x_601 = lean::box(0);
x_602 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_603 = l_Lean_KVMap_setNat(x_601, x_602, x_600);
x_604 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_605 = 1;
x_606 = l_Lean_KVMap_setBool(x_603, x_604, x_605);
x_607 = lean::cnstr_get(x_210, 1);
lean::inc(x_607);
lean::dec(x_210);
x_610 = l_List_append___rarg(x_526, x_594);
x_611 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_612 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__12(x_611, x_610);
if (lean::obj_tag(x_607) == 0)
{
obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; 
x_613 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_614 = lean::box(0);
x_615 = l_Lean_KVMap_setName(x_606, x_613, x_614);
x_616 = lean_expr_mk_mdata(x_615, x_612);
if (lean::is_scalar(x_598)) {
 x_617 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_617 = x_598;
}
lean::cnstr_set(x_617, 0, x_616);
lean::cnstr_set(x_617, 1, x_596);
x_15 = x_617;
goto lbl_16;
}
else
{
obj* x_618; obj* x_621; obj* x_624; obj* x_625; obj* x_626; obj* x_627; obj* x_628; 
x_618 = lean::cnstr_get(x_607, 0);
lean::inc(x_618);
lean::dec(x_607);
x_621 = lean::cnstr_get(x_618, 0);
lean::inc(x_621);
lean::dec(x_618);
x_624 = l_Lean_Elaborator_mangleIdent(x_621);
x_625 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_626 = l_Lean_KVMap_setName(x_606, x_625, x_624);
x_627 = lean_expr_mk_mdata(x_626, x_612);
if (lean::is_scalar(x_598)) {
 x_628 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_628 = x_598;
}
lean::cnstr_set(x_628, 0, x_627);
lean::cnstr_set(x_628, 1, x_596);
x_15 = x_628;
goto lbl_16;
}
}
}
}
else
{
obj* x_630; obj* x_631; obj* x_634; obj* x_635; obj* x_638; obj* x_639; obj* x_640; obj* x_642; 
lean::dec(x_505);
if (lean::is_exclusive(x_503)) {
 lean::cnstr_release(x_503, 0);
 lean::cnstr_release(x_503, 1);
 x_630 = x_503;
} else {
 lean::dec(x_503);
 x_630 = lean::box(0);
}
x_631 = lean::cnstr_get(x_221, 0);
lean::inc(x_631);
lean::dec(x_221);
x_634 = l_Lean_Parser_Term_structInstItem_HasView;
x_635 = lean::cnstr_get(x_634, 1);
lean::inc(x_635);
lean::dec(x_634);
x_638 = lean::apply_1(x_635, x_344);
x_639 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_639, 0, x_638);
x_640 = l_Lean_Elaborator_toPexpr___main___closed__29;
lean::inc(x_2);
x_642 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_639, x_640, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_639);
if (lean::obj_tag(x_642) == 0)
{
obj* x_652; obj* x_654; obj* x_655; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_630);
lean::dec(x_631);
lean::dec(x_215);
lean::dec(x_210);
x_652 = lean::cnstr_get(x_642, 0);
if (lean::is_exclusive(x_642)) {
 x_654 = x_642;
} else {
 lean::inc(x_652);
 lean::dec(x_642);
 x_654 = lean::box(0);
}
if (lean::is_scalar(x_654)) {
 x_655 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_655 = x_654;
}
lean::cnstr_set(x_655, 0, x_652);
return x_655;
}
else
{
obj* x_656; obj* x_659; obj* x_661; obj* x_666; 
x_656 = lean::cnstr_get(x_642, 0);
lean::inc(x_656);
lean::dec(x_642);
x_659 = lean::cnstr_get(x_656, 0);
lean::inc(x_659);
x_661 = lean::cnstr_get(x_656, 1);
lean::inc(x_661);
lean::dec(x_656);
lean::inc(x_2);
lean::inc(x_0);
x_666 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__14(x_0, x_215, x_1, x_2, x_661);
if (lean::obj_tag(x_666) == 0)
{
obj* x_674; obj* x_676; obj* x_677; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_630);
lean::dec(x_631);
lean::dec(x_659);
lean::dec(x_210);
x_674 = lean::cnstr_get(x_666, 0);
if (lean::is_exclusive(x_666)) {
 x_676 = x_666;
} else {
 lean::inc(x_674);
 lean::dec(x_666);
 x_676 = lean::box(0);
}
if (lean::is_scalar(x_676)) {
 x_677 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_677 = x_676;
}
lean::cnstr_set(x_677, 0, x_674);
return x_677;
}
else
{
obj* x_678; obj* x_681; obj* x_683; obj* x_686; obj* x_690; 
x_678 = lean::cnstr_get(x_666, 0);
lean::inc(x_678);
lean::dec(x_666);
x_681 = lean::cnstr_get(x_678, 0);
lean::inc(x_681);
x_683 = lean::cnstr_get(x_678, 1);
lean::inc(x_683);
lean::dec(x_678);
lean::inc(x_2);
lean::inc(x_0);
x_690 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__16(x_0, x_631, x_1, x_2, x_683);
if (lean::obj_tag(x_690) == 0)
{
obj* x_698; obj* x_700; obj* x_701; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_681);
lean::dec(x_630);
lean::dec(x_659);
lean::dec(x_210);
x_698 = lean::cnstr_get(x_690, 0);
if (lean::is_exclusive(x_690)) {
 x_700 = x_690;
} else {
 lean::inc(x_698);
 lean::dec(x_690);
 x_700 = lean::box(0);
}
if (lean::is_scalar(x_700)) {
 x_701 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_701 = x_700;
}
lean::cnstr_set(x_701, 0, x_698);
return x_701;
}
else
{
obj* x_702; obj* x_705; 
x_702 = lean::cnstr_get(x_690, 0);
lean::inc(x_702);
lean::dec(x_690);
x_705 = lean::cnstr_get(x_210, 2);
lean::inc(x_705);
if (lean::obj_tag(x_705) == 0)
{
obj* x_708; obj* x_710; obj* x_712; obj* x_713; 
lean::dec(x_630);
x_708 = lean::cnstr_get(x_702, 0);
x_710 = lean::cnstr_get(x_702, 1);
if (lean::is_exclusive(x_702)) {
 x_712 = x_702;
} else {
 lean::inc(x_708);
 lean::inc(x_710);
 lean::dec(x_702);
 x_712 = lean::box(0);
}
if (lean::is_scalar(x_712)) {
 x_713 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_713 = x_712;
}
lean::cnstr_set(x_713, 0, x_708);
lean::cnstr_set(x_713, 1, x_710);
x_686 = x_713;
goto lbl_687;
}
else
{
obj* x_714; obj* x_716; obj* x_719; obj* x_722; obj* x_726; 
x_714 = lean::cnstr_get(x_702, 0);
lean::inc(x_714);
x_716 = lean::cnstr_get(x_702, 1);
lean::inc(x_716);
lean::dec(x_702);
x_719 = lean::cnstr_get(x_705, 0);
lean::inc(x_719);
lean::dec(x_705);
x_722 = lean::cnstr_get(x_719, 0);
lean::inc(x_722);
lean::dec(x_719);
lean::inc(x_2);
x_726 = l_Lean_Elaborator_toPexpr___main(x_722, x_1, x_2, x_716);
if (lean::obj_tag(x_726) == 0)
{
obj* x_735; obj* x_737; obj* x_738; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_681);
lean::dec(x_714);
lean::dec(x_630);
lean::dec(x_659);
lean::dec(x_210);
x_735 = lean::cnstr_get(x_726, 0);
if (lean::is_exclusive(x_726)) {
 x_737 = x_726;
} else {
 lean::inc(x_735);
 lean::dec(x_726);
 x_737 = lean::box(0);
}
if (lean::is_scalar(x_737)) {
 x_738 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_738 = x_737;
}
lean::cnstr_set(x_738, 0, x_735);
return x_738;
}
else
{
obj* x_739; obj* x_742; obj* x_744; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; 
x_739 = lean::cnstr_get(x_726, 0);
lean::inc(x_739);
lean::dec(x_726);
x_742 = lean::cnstr_get(x_739, 0);
x_744 = lean::cnstr_get(x_739, 1);
if (lean::is_exclusive(x_739)) {
 x_746 = x_739;
} else {
 lean::inc(x_742);
 lean::inc(x_744);
 lean::dec(x_739);
 x_746 = lean::box(0);
}
x_747 = lean::box(0);
if (lean::is_scalar(x_630)) {
 x_748 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_748 = x_630;
}
lean::cnstr_set(x_748, 0, x_742);
lean::cnstr_set(x_748, 1, x_747);
x_749 = l_List_append___rarg(x_714, x_748);
if (lean::is_scalar(x_746)) {
 x_750 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_750 = x_746;
}
lean::cnstr_set(x_750, 0, x_749);
lean::cnstr_set(x_750, 1, x_744);
x_686 = x_750;
goto lbl_687;
}
}
}
lbl_687:
{
obj* x_751; obj* x_753; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; obj* x_761; uint8 x_762; obj* x_763; obj* x_764; obj* x_767; obj* x_768; obj* x_769; 
x_751 = lean::cnstr_get(x_686, 0);
x_753 = lean::cnstr_get(x_686, 1);
if (lean::is_exclusive(x_686)) {
 lean::cnstr_set(x_686, 0, lean::box(0));
 lean::cnstr_set(x_686, 1, lean::box(0));
 x_755 = x_686;
} else {
 lean::inc(x_751);
 lean::inc(x_753);
 lean::dec(x_686);
 x_755 = lean::box(0);
}
x_756 = lean::mk_nat_obj(0ul);
x_757 = l_List_lengthAux___main___rarg(x_681, x_756);
x_758 = lean::box(0);
x_759 = l_Lean_Elaborator_toPexpr___main___closed__25;
x_760 = l_Lean_KVMap_setNat(x_758, x_759, x_757);
x_761 = l_Lean_Elaborator_toPexpr___main___closed__26;
x_762 = lean::unbox(x_659);
x_763 = l_Lean_KVMap_setBool(x_760, x_761, x_762);
x_764 = lean::cnstr_get(x_210, 1);
lean::inc(x_764);
lean::dec(x_210);
x_767 = l_List_append___rarg(x_681, x_751);
x_768 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_769 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__15(x_768, x_767);
if (lean::obj_tag(x_764) == 0)
{
obj* x_770; obj* x_771; obj* x_772; obj* x_773; obj* x_774; 
x_770 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_771 = lean::box(0);
x_772 = l_Lean_KVMap_setName(x_763, x_770, x_771);
x_773 = lean_expr_mk_mdata(x_772, x_769);
if (lean::is_scalar(x_755)) {
 x_774 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_774 = x_755;
}
lean::cnstr_set(x_774, 0, x_773);
lean::cnstr_set(x_774, 1, x_753);
x_15 = x_774;
goto lbl_16;
}
else
{
obj* x_775; obj* x_778; obj* x_781; obj* x_782; obj* x_783; obj* x_784; obj* x_785; 
x_775 = lean::cnstr_get(x_764, 0);
lean::inc(x_775);
lean::dec(x_764);
x_778 = lean::cnstr_get(x_775, 0);
lean::inc(x_778);
lean::dec(x_775);
x_781 = l_Lean_Elaborator_mangleIdent(x_778);
x_782 = l_Lean_Elaborator_toPexpr___main___closed__28;
x_783 = l_Lean_KVMap_setName(x_763, x_782, x_781);
x_784 = lean_expr_mk_mdata(x_783, x_769);
if (lean::is_scalar(x_755)) {
 x_785 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_785 = x_755;
}
lean::cnstr_set(x_785, 0, x_784);
lean::cnstr_set(x_785, 1, x_753);
x_15 = x_785;
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
obj* x_788; 
lean::inc(x_2);
lean::inc(x_10);
x_788 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__17(x_10, x_1, x_2, x_3);
if (lean::obj_tag(x_788) == 0)
{
obj* x_793; obj* x_795; obj* x_796; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
x_793 = lean::cnstr_get(x_788, 0);
if (lean::is_exclusive(x_788)) {
 x_795 = x_788;
} else {
 lean::inc(x_793);
 lean::dec(x_788);
 x_795 = lean::box(0);
}
if (lean::is_scalar(x_795)) {
 x_796 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_796 = x_795;
}
lean::cnstr_set(x_796, 0, x_793);
return x_796;
}
else
{
obj* x_797; obj* x_800; obj* x_802; obj* x_804; obj* x_805; 
x_797 = lean::cnstr_get(x_788, 0);
lean::inc(x_797);
lean::dec(x_788);
x_800 = lean::cnstr_get(x_797, 0);
x_802 = lean::cnstr_get(x_797, 1);
if (lean::is_exclusive(x_797)) {
 lean::cnstr_set(x_797, 0, lean::box(0));
 lean::cnstr_set(x_797, 1, lean::box(0));
 x_804 = x_797;
} else {
 lean::inc(x_800);
 lean::inc(x_802);
 lean::dec(x_797);
 x_804 = lean::box(0);
}
x_805 = l_List_reverse___rarg(x_800);
if (lean::obj_tag(x_805) == 0)
{
obj* x_809; obj* x_810; obj* x_812; 
lean::dec(x_804);
lean::dec(x_10);
lean::inc(x_0);
x_809 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_809, 0, x_0);
x_810 = l_Lean_Elaborator_toPexpr___main___closed__30;
lean::inc(x_2);
x_812 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_809, x_810, x_1, x_2, x_802);
lean::dec(x_802);
lean::dec(x_809);
if (lean::obj_tag(x_812) == 0)
{
obj* x_818; obj* x_820; obj* x_821; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_818 = lean::cnstr_get(x_812, 0);
if (lean::is_exclusive(x_812)) {
 x_820 = x_812;
} else {
 lean::inc(x_818);
 lean::dec(x_812);
 x_820 = lean::box(0);
}
if (lean::is_scalar(x_820)) {
 x_821 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_821 = x_820;
}
lean::cnstr_set(x_821, 0, x_818);
return x_821;
}
else
{
obj* x_822; 
x_822 = lean::cnstr_get(x_812, 0);
lean::inc(x_822);
lean::dec(x_812);
x_15 = x_822;
goto lbl_16;
}
}
else
{
obj* x_825; obj* x_827; obj* x_830; obj* x_831; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_839; obj* x_840; 
x_825 = lean::cnstr_get(x_805, 0);
lean::inc(x_825);
x_827 = lean::cnstr_get(x_805, 1);
lean::inc(x_827);
lean::dec(x_805);
x_830 = lean::mk_nat_obj(0ul);
x_831 = l_List_lengthAux___main___rarg(x_10, x_830);
lean::dec(x_10);
x_833 = lean::box(0);
x_834 = l_Lean_Elaborator_toPexpr___main___closed__31;
x_835 = l_Lean_KVMap_setNat(x_833, x_834, x_831);
x_836 = l_List_reverse___rarg(x_827);
x_837 = l_List_foldr___main___at_Lean_Elaborator_toPexpr___main___spec__18(x_825, x_836);
lean::dec(x_825);
x_839 = lean_expr_mk_mdata(x_835, x_837);
if (lean::is_scalar(x_804)) {
 x_840 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_840 = x_804;
}
lean::cnstr_set(x_840, 0, x_839);
lean::cnstr_set(x_840, 1, x_802);
x_15 = x_840;
goto lbl_16;
}
}
}
}
else
{
obj* x_843; obj* x_844; obj* x_848; obj* x_849; 
lean::dec(x_8);
lean::dec(x_10);
x_843 = l_Lean_Parser_stringLit_HasView;
x_844 = lean::cnstr_get(x_843, 0);
lean::inc(x_844);
lean::dec(x_843);
lean::inc(x_0);
x_848 = lean::apply_1(x_844, x_0);
x_849 = l_Lean_Parser_stringLit_View_value(x_848);
if (lean::obj_tag(x_849) == 0)
{
if (x_20 == 0)
{
obj* x_850; 
x_850 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_850) == 0)
{
obj* x_853; obj* x_854; obj* x_855; 
lean::dec(x_2);
x_853 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_854 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_854, 0, x_853);
lean::cnstr_set(x_854, 1, x_3);
x_855 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_855, 0, x_854);
return x_855;
}
else
{
obj* x_856; obj* x_859; obj* x_862; obj* x_865; obj* x_866; obj* x_868; obj* x_869; obj* x_870; obj* x_871; obj* x_874; obj* x_875; obj* x_876; obj* x_877; obj* x_878; obj* x_879; 
x_856 = lean::cnstr_get(x_850, 0);
lean::inc(x_856);
lean::dec(x_850);
x_859 = lean::cnstr_get(x_2, 0);
lean::inc(x_859);
lean::dec(x_2);
x_862 = lean::cnstr_get(x_859, 2);
lean::inc(x_862);
lean::dec(x_859);
x_865 = l_Lean_FileMap_toPosition(x_862, x_856);
x_866 = lean::cnstr_get(x_865, 1);
lean::inc(x_866);
x_868 = lean::box(0);
x_869 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_870 = l_Lean_KVMap_setNat(x_868, x_869, x_866);
x_871 = lean::cnstr_get(x_865, 0);
lean::inc(x_871);
lean::dec(x_865);
x_874 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_875 = l_Lean_KVMap_setNat(x_870, x_874, x_871);
x_876 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_877 = lean_expr_mk_mdata(x_875, x_876);
x_878 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_878, 0, x_877);
lean::cnstr_set(x_878, 1, x_3);
x_879 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_879, 0, x_878);
return x_879;
}
}
else
{
obj* x_882; obj* x_883; obj* x_884; 
lean::dec(x_0);
lean::dec(x_2);
x_882 = l_Lean_Elaborator_toPexpr___main___closed__32;
x_883 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_883, 0, x_882);
lean::cnstr_set(x_883, 1, x_3);
x_884 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_884, 0, x_883);
return x_884;
}
}
else
{
obj* x_885; obj* x_888; obj* x_889; 
x_885 = lean::cnstr_get(x_849, 0);
lean::inc(x_885);
lean::dec(x_849);
x_888 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_888, 0, x_885);
x_889 = lean_expr_mk_lit(x_888);
if (x_20 == 0)
{
obj* x_890; 
x_890 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_890) == 0)
{
obj* x_893; obj* x_894; 
lean::dec(x_2);
x_893 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_893, 0, x_889);
lean::cnstr_set(x_893, 1, x_3);
x_894 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_894, 0, x_893);
return x_894;
}
else
{
obj* x_895; obj* x_898; obj* x_901; obj* x_904; obj* x_905; obj* x_907; obj* x_908; obj* x_909; obj* x_910; obj* x_913; obj* x_914; obj* x_915; obj* x_916; obj* x_917; 
x_895 = lean::cnstr_get(x_890, 0);
lean::inc(x_895);
lean::dec(x_890);
x_898 = lean::cnstr_get(x_2, 0);
lean::inc(x_898);
lean::dec(x_2);
x_901 = lean::cnstr_get(x_898, 2);
lean::inc(x_901);
lean::dec(x_898);
x_904 = l_Lean_FileMap_toPosition(x_901, x_895);
x_905 = lean::cnstr_get(x_904, 1);
lean::inc(x_905);
x_907 = lean::box(0);
x_908 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_909 = l_Lean_KVMap_setNat(x_907, x_908, x_905);
x_910 = lean::cnstr_get(x_904, 0);
lean::inc(x_910);
lean::dec(x_904);
x_913 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_914 = l_Lean_KVMap_setNat(x_909, x_913, x_910);
x_915 = lean_expr_mk_mdata(x_914, x_889);
x_916 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_916, 0, x_915);
lean::cnstr_set(x_916, 1, x_3);
x_917 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_917, 0, x_916);
return x_917;
}
}
else
{
obj* x_920; obj* x_921; 
lean::dec(x_0);
lean::dec(x_2);
x_920 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_920, 0, x_889);
lean::cnstr_set(x_920, 1, x_3);
x_921 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_921, 0, x_920);
return x_921;
}
}
}
}
else
{
obj* x_924; obj* x_925; obj* x_929; obj* x_930; obj* x_931; obj* x_932; 
lean::dec(x_8);
lean::dec(x_10);
x_924 = l_Lean_Parser_number_HasView;
x_925 = lean::cnstr_get(x_924, 0);
lean::inc(x_925);
lean::dec(x_924);
lean::inc(x_0);
x_929 = lean::apply_1(x_925, x_0);
x_930 = l_Lean_Parser_number_View_toNat___main(x_929);
x_931 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_931, 0, x_930);
x_932 = lean_expr_mk_lit(x_931);
if (x_20 == 0)
{
obj* x_933; 
x_933 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_933) == 0)
{
obj* x_936; obj* x_937; 
lean::dec(x_2);
x_936 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_936, 0, x_932);
lean::cnstr_set(x_936, 1, x_3);
x_937 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_937, 0, x_936);
return x_937;
}
else
{
obj* x_938; obj* x_941; obj* x_944; obj* x_947; obj* x_948; obj* x_950; obj* x_951; obj* x_952; obj* x_953; obj* x_956; obj* x_957; obj* x_958; obj* x_959; obj* x_960; 
x_938 = lean::cnstr_get(x_933, 0);
lean::inc(x_938);
lean::dec(x_933);
x_941 = lean::cnstr_get(x_2, 0);
lean::inc(x_941);
lean::dec(x_2);
x_944 = lean::cnstr_get(x_941, 2);
lean::inc(x_944);
lean::dec(x_941);
x_947 = l_Lean_FileMap_toPosition(x_944, x_938);
x_948 = lean::cnstr_get(x_947, 1);
lean::inc(x_948);
x_950 = lean::box(0);
x_951 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_952 = l_Lean_KVMap_setNat(x_950, x_951, x_948);
x_953 = lean::cnstr_get(x_947, 0);
lean::inc(x_953);
lean::dec(x_947);
x_956 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_957 = l_Lean_KVMap_setNat(x_952, x_956, x_953);
x_958 = lean_expr_mk_mdata(x_957, x_932);
x_959 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_959, 0, x_958);
lean::cnstr_set(x_959, 1, x_3);
x_960 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_960, 0, x_959);
return x_960;
}
}
else
{
obj* x_963; obj* x_964; 
lean::dec(x_0);
lean::dec(x_2);
x_963 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_963, 0, x_932);
lean::cnstr_set(x_963, 1, x_3);
x_964 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_964, 0, x_963);
return x_964;
}
}
}
else
{
obj* x_967; obj* x_968; obj* x_972; obj* x_973; obj* x_977; 
lean::dec(x_8);
lean::dec(x_10);
x_967 = l_Lean_Parser_Term_borrowed_HasView;
x_968 = lean::cnstr_get(x_967, 0);
lean::inc(x_968);
lean::dec(x_967);
lean::inc(x_0);
x_972 = lean::apply_1(x_968, x_0);
x_973 = lean::cnstr_get(x_972, 1);
lean::inc(x_973);
lean::dec(x_972);
lean::inc(x_2);
x_977 = l_Lean_Elaborator_toPexpr___main(x_973, x_1, x_2, x_3);
if (lean::obj_tag(x_977) == 0)
{
obj* x_980; obj* x_982; obj* x_983; 
lean::dec(x_0);
lean::dec(x_2);
x_980 = lean::cnstr_get(x_977, 0);
if (lean::is_exclusive(x_977)) {
 x_982 = x_977;
} else {
 lean::inc(x_980);
 lean::dec(x_977);
 x_982 = lean::box(0);
}
if (lean::is_scalar(x_982)) {
 x_983 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_983 = x_982;
}
lean::cnstr_set(x_983, 0, x_980);
return x_983;
}
else
{
obj* x_984; obj* x_986; obj* x_987; obj* x_989; obj* x_991; obj* x_992; obj* x_993; 
x_984 = lean::cnstr_get(x_977, 0);
if (lean::is_exclusive(x_977)) {
 lean::cnstr_set(x_977, 0, lean::box(0));
 x_986 = x_977;
} else {
 lean::inc(x_984);
 lean::dec(x_977);
 x_986 = lean::box(0);
}
x_987 = lean::cnstr_get(x_984, 0);
x_989 = lean::cnstr_get(x_984, 1);
if (lean::is_exclusive(x_984)) {
 lean::cnstr_set(x_984, 0, lean::box(0));
 lean::cnstr_set(x_984, 1, lean::box(0));
 x_991 = x_984;
} else {
 lean::inc(x_987);
 lean::inc(x_989);
 lean::dec(x_984);
 x_991 = lean::box(0);
}
x_992 = l_Lean_Elaborator_toPexpr___main___closed__33;
x_993 = l_Lean_Elaborator_Expr_mkAnnotation(x_992, x_987);
if (x_20 == 0)
{
obj* x_994; 
x_994 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_994) == 0)
{
obj* x_997; obj* x_998; 
lean::dec(x_2);
if (lean::is_scalar(x_991)) {
 x_997 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_997 = x_991;
}
lean::cnstr_set(x_997, 0, x_993);
lean::cnstr_set(x_997, 1, x_989);
if (lean::is_scalar(x_986)) {
 x_998 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_998 = x_986;
}
lean::cnstr_set(x_998, 0, x_997);
return x_998;
}
else
{
obj* x_999; obj* x_1002; obj* x_1005; obj* x_1008; obj* x_1009; obj* x_1011; obj* x_1012; obj* x_1013; obj* x_1014; obj* x_1017; obj* x_1018; obj* x_1019; obj* x_1020; obj* x_1021; 
x_999 = lean::cnstr_get(x_994, 0);
lean::inc(x_999);
lean::dec(x_994);
x_1002 = lean::cnstr_get(x_2, 0);
lean::inc(x_1002);
lean::dec(x_2);
x_1005 = lean::cnstr_get(x_1002, 2);
lean::inc(x_1005);
lean::dec(x_1002);
x_1008 = l_Lean_FileMap_toPosition(x_1005, x_999);
x_1009 = lean::cnstr_get(x_1008, 1);
lean::inc(x_1009);
x_1011 = lean::box(0);
x_1012 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1013 = l_Lean_KVMap_setNat(x_1011, x_1012, x_1009);
x_1014 = lean::cnstr_get(x_1008, 0);
lean::inc(x_1014);
lean::dec(x_1008);
x_1017 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1018 = l_Lean_KVMap_setNat(x_1013, x_1017, x_1014);
x_1019 = lean_expr_mk_mdata(x_1018, x_993);
if (lean::is_scalar(x_991)) {
 x_1020 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1020 = x_991;
}
lean::cnstr_set(x_1020, 0, x_1019);
lean::cnstr_set(x_1020, 1, x_989);
if (lean::is_scalar(x_986)) {
 x_1021 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1021 = x_986;
}
lean::cnstr_set(x_1021, 0, x_1020);
return x_1021;
}
}
else
{
obj* x_1024; obj* x_1025; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_991)) {
 x_1024 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1024 = x_991;
}
lean::cnstr_set(x_1024, 0, x_993);
lean::cnstr_set(x_1024, 1, x_989);
if (lean::is_scalar(x_986)) {
 x_1025 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1025 = x_986;
}
lean::cnstr_set(x_1025, 0, x_1024);
return x_1025;
}
}
}
}
else
{
obj* x_1028; obj* x_1029; obj* x_1033; obj* x_1034; obj* x_1038; 
lean::dec(x_8);
lean::dec(x_10);
x_1028 = l_Lean_Parser_Term_inaccessible_HasView;
x_1029 = lean::cnstr_get(x_1028, 0);
lean::inc(x_1029);
lean::dec(x_1028);
lean::inc(x_0);
x_1033 = lean::apply_1(x_1029, x_0);
x_1034 = lean::cnstr_get(x_1033, 1);
lean::inc(x_1034);
lean::dec(x_1033);
lean::inc(x_2);
x_1038 = l_Lean_Elaborator_toPexpr___main(x_1034, x_1, x_2, x_3);
if (lean::obj_tag(x_1038) == 0)
{
obj* x_1041; obj* x_1043; obj* x_1044; 
lean::dec(x_0);
lean::dec(x_2);
x_1041 = lean::cnstr_get(x_1038, 0);
if (lean::is_exclusive(x_1038)) {
 x_1043 = x_1038;
} else {
 lean::inc(x_1041);
 lean::dec(x_1038);
 x_1043 = lean::box(0);
}
if (lean::is_scalar(x_1043)) {
 x_1044 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1044 = x_1043;
}
lean::cnstr_set(x_1044, 0, x_1041);
return x_1044;
}
else
{
obj* x_1045; obj* x_1047; obj* x_1048; obj* x_1050; obj* x_1052; obj* x_1053; obj* x_1054; 
x_1045 = lean::cnstr_get(x_1038, 0);
if (lean::is_exclusive(x_1038)) {
 lean::cnstr_set(x_1038, 0, lean::box(0));
 x_1047 = x_1038;
} else {
 lean::inc(x_1045);
 lean::dec(x_1038);
 x_1047 = lean::box(0);
}
x_1048 = lean::cnstr_get(x_1045, 0);
x_1050 = lean::cnstr_get(x_1045, 1);
if (lean::is_exclusive(x_1045)) {
 lean::cnstr_set(x_1045, 0, lean::box(0));
 lean::cnstr_set(x_1045, 1, lean::box(0));
 x_1052 = x_1045;
} else {
 lean::inc(x_1048);
 lean::inc(x_1050);
 lean::dec(x_1045);
 x_1052 = lean::box(0);
}
x_1053 = l_Lean_Elaborator_toPexpr___main___closed__34;
x_1054 = l_Lean_Elaborator_Expr_mkAnnotation(x_1053, x_1048);
if (x_20 == 0)
{
obj* x_1055; 
x_1055 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1055) == 0)
{
obj* x_1058; obj* x_1059; 
lean::dec(x_2);
if (lean::is_scalar(x_1052)) {
 x_1058 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1058 = x_1052;
}
lean::cnstr_set(x_1058, 0, x_1054);
lean::cnstr_set(x_1058, 1, x_1050);
if (lean::is_scalar(x_1047)) {
 x_1059 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1059 = x_1047;
}
lean::cnstr_set(x_1059, 0, x_1058);
return x_1059;
}
else
{
obj* x_1060; obj* x_1063; obj* x_1066; obj* x_1069; obj* x_1070; obj* x_1072; obj* x_1073; obj* x_1074; obj* x_1075; obj* x_1078; obj* x_1079; obj* x_1080; obj* x_1081; obj* x_1082; 
x_1060 = lean::cnstr_get(x_1055, 0);
lean::inc(x_1060);
lean::dec(x_1055);
x_1063 = lean::cnstr_get(x_2, 0);
lean::inc(x_1063);
lean::dec(x_2);
x_1066 = lean::cnstr_get(x_1063, 2);
lean::inc(x_1066);
lean::dec(x_1063);
x_1069 = l_Lean_FileMap_toPosition(x_1066, x_1060);
x_1070 = lean::cnstr_get(x_1069, 1);
lean::inc(x_1070);
x_1072 = lean::box(0);
x_1073 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1074 = l_Lean_KVMap_setNat(x_1072, x_1073, x_1070);
x_1075 = lean::cnstr_get(x_1069, 0);
lean::inc(x_1075);
lean::dec(x_1069);
x_1078 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1079 = l_Lean_KVMap_setNat(x_1074, x_1078, x_1075);
x_1080 = lean_expr_mk_mdata(x_1079, x_1054);
if (lean::is_scalar(x_1052)) {
 x_1081 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1081 = x_1052;
}
lean::cnstr_set(x_1081, 0, x_1080);
lean::cnstr_set(x_1081, 1, x_1050);
if (lean::is_scalar(x_1047)) {
 x_1082 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1082 = x_1047;
}
lean::cnstr_set(x_1082, 0, x_1081);
return x_1082;
}
}
else
{
obj* x_1085; obj* x_1086; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1052)) {
 x_1085 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1085 = x_1052;
}
lean::cnstr_set(x_1085, 0, x_1054);
lean::cnstr_set(x_1085, 1, x_1050);
if (lean::is_scalar(x_1047)) {
 x_1086 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1086 = x_1047;
}
lean::cnstr_set(x_1086, 0, x_1085);
return x_1086;
}
}
}
}
else
{
obj* x_1089; obj* x_1090; obj* x_1094; obj* x_1095; obj* x_1097; obj* x_1098; obj* x_1101; obj* x_1104; 
lean::dec(x_8);
lean::dec(x_10);
x_1089 = l_Lean_Parser_Term_explicit_HasView;
x_1090 = lean::cnstr_get(x_1089, 0);
lean::inc(x_1090);
lean::dec(x_1089);
lean::inc(x_0);
x_1094 = lean::apply_1(x_1090, x_0);
x_1095 = lean::cnstr_get(x_1094, 0);
lean::inc(x_1095);
x_1097 = l_Lean_Parser_identUnivs_HasView;
x_1098 = lean::cnstr_get(x_1097, 1);
lean::inc(x_1098);
lean::dec(x_1097);
x_1101 = lean::cnstr_get(x_1094, 1);
lean::inc(x_1101);
lean::dec(x_1094);
x_1104 = lean::apply_1(x_1098, x_1101);
if (lean::obj_tag(x_1095) == 0)
{
obj* x_1107; 
lean::dec(x_1095);
lean::inc(x_2);
x_1107 = l_Lean_Elaborator_toPexpr___main(x_1104, x_1, x_2, x_3);
if (lean::obj_tag(x_1107) == 0)
{
obj* x_1110; obj* x_1112; obj* x_1113; 
lean::dec(x_0);
lean::dec(x_2);
x_1110 = lean::cnstr_get(x_1107, 0);
if (lean::is_exclusive(x_1107)) {
 x_1112 = x_1107;
} else {
 lean::inc(x_1110);
 lean::dec(x_1107);
 x_1112 = lean::box(0);
}
if (lean::is_scalar(x_1112)) {
 x_1113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1113 = x_1112;
}
lean::cnstr_set(x_1113, 0, x_1110);
return x_1113;
}
else
{
obj* x_1114; obj* x_1116; obj* x_1117; obj* x_1119; obj* x_1121; obj* x_1122; obj* x_1123; 
x_1114 = lean::cnstr_get(x_1107, 0);
if (lean::is_exclusive(x_1107)) {
 lean::cnstr_set(x_1107, 0, lean::box(0));
 x_1116 = x_1107;
} else {
 lean::inc(x_1114);
 lean::dec(x_1107);
 x_1116 = lean::box(0);
}
x_1117 = lean::cnstr_get(x_1114, 0);
x_1119 = lean::cnstr_get(x_1114, 1);
if (lean::is_exclusive(x_1114)) {
 lean::cnstr_set(x_1114, 0, lean::box(0));
 lean::cnstr_set(x_1114, 1, lean::box(0));
 x_1121 = x_1114;
} else {
 lean::inc(x_1117);
 lean::inc(x_1119);
 lean::dec(x_1114);
 x_1121 = lean::box(0);
}
x_1122 = l_List_map___main___at_Lean_Elaborator_mkEqns___spec__1___closed__1;
x_1123 = l_Lean_Elaborator_Expr_mkAnnotation(x_1122, x_1117);
if (x_20 == 0)
{
obj* x_1124; 
x_1124 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1124) == 0)
{
obj* x_1127; obj* x_1128; 
lean::dec(x_2);
if (lean::is_scalar(x_1121)) {
 x_1127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1127 = x_1121;
}
lean::cnstr_set(x_1127, 0, x_1123);
lean::cnstr_set(x_1127, 1, x_1119);
if (lean::is_scalar(x_1116)) {
 x_1128 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1128 = x_1116;
}
lean::cnstr_set(x_1128, 0, x_1127);
return x_1128;
}
else
{
obj* x_1129; obj* x_1132; obj* x_1135; obj* x_1138; obj* x_1139; obj* x_1141; obj* x_1142; obj* x_1143; obj* x_1144; obj* x_1147; obj* x_1148; obj* x_1149; obj* x_1150; obj* x_1151; 
x_1129 = lean::cnstr_get(x_1124, 0);
lean::inc(x_1129);
lean::dec(x_1124);
x_1132 = lean::cnstr_get(x_2, 0);
lean::inc(x_1132);
lean::dec(x_2);
x_1135 = lean::cnstr_get(x_1132, 2);
lean::inc(x_1135);
lean::dec(x_1132);
x_1138 = l_Lean_FileMap_toPosition(x_1135, x_1129);
x_1139 = lean::cnstr_get(x_1138, 1);
lean::inc(x_1139);
x_1141 = lean::box(0);
x_1142 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1143 = l_Lean_KVMap_setNat(x_1141, x_1142, x_1139);
x_1144 = lean::cnstr_get(x_1138, 0);
lean::inc(x_1144);
lean::dec(x_1138);
x_1147 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1148 = l_Lean_KVMap_setNat(x_1143, x_1147, x_1144);
x_1149 = lean_expr_mk_mdata(x_1148, x_1123);
if (lean::is_scalar(x_1121)) {
 x_1150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1150 = x_1121;
}
lean::cnstr_set(x_1150, 0, x_1149);
lean::cnstr_set(x_1150, 1, x_1119);
if (lean::is_scalar(x_1116)) {
 x_1151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1151 = x_1116;
}
lean::cnstr_set(x_1151, 0, x_1150);
return x_1151;
}
}
else
{
obj* x_1154; obj* x_1155; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1121)) {
 x_1154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1154 = x_1121;
}
lean::cnstr_set(x_1154, 0, x_1123);
lean::cnstr_set(x_1154, 1, x_1119);
if (lean::is_scalar(x_1116)) {
 x_1155 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1155 = x_1116;
}
lean::cnstr_set(x_1155, 0, x_1154);
return x_1155;
}
}
}
else
{
obj* x_1158; 
lean::dec(x_1095);
lean::inc(x_2);
x_1158 = l_Lean_Elaborator_toPexpr___main(x_1104, x_1, x_2, x_3);
if (lean::obj_tag(x_1158) == 0)
{
obj* x_1161; obj* x_1163; obj* x_1164; 
lean::dec(x_0);
lean::dec(x_2);
x_1161 = lean::cnstr_get(x_1158, 0);
if (lean::is_exclusive(x_1158)) {
 x_1163 = x_1158;
} else {
 lean::inc(x_1161);
 lean::dec(x_1158);
 x_1163 = lean::box(0);
}
if (lean::is_scalar(x_1163)) {
 x_1164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1164 = x_1163;
}
lean::cnstr_set(x_1164, 0, x_1161);
return x_1164;
}
else
{
obj* x_1165; obj* x_1167; obj* x_1168; obj* x_1170; obj* x_1172; obj* x_1173; obj* x_1174; 
x_1165 = lean::cnstr_get(x_1158, 0);
if (lean::is_exclusive(x_1158)) {
 lean::cnstr_set(x_1158, 0, lean::box(0));
 x_1167 = x_1158;
} else {
 lean::inc(x_1165);
 lean::dec(x_1158);
 x_1167 = lean::box(0);
}
x_1168 = lean::cnstr_get(x_1165, 0);
x_1170 = lean::cnstr_get(x_1165, 1);
if (lean::is_exclusive(x_1165)) {
 lean::cnstr_set(x_1165, 0, lean::box(0));
 lean::cnstr_set(x_1165, 1, lean::box(0));
 x_1172 = x_1165;
} else {
 lean::inc(x_1168);
 lean::inc(x_1170);
 lean::dec(x_1165);
 x_1172 = lean::box(0);
}
x_1173 = l_Lean_Elaborator_toPexpr___main___closed__35;
x_1174 = l_Lean_Elaborator_Expr_mkAnnotation(x_1173, x_1168);
if (x_20 == 0)
{
obj* x_1175; 
x_1175 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1175) == 0)
{
obj* x_1178; obj* x_1179; 
lean::dec(x_2);
if (lean::is_scalar(x_1172)) {
 x_1178 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1178 = x_1172;
}
lean::cnstr_set(x_1178, 0, x_1174);
lean::cnstr_set(x_1178, 1, x_1170);
if (lean::is_scalar(x_1167)) {
 x_1179 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1179 = x_1167;
}
lean::cnstr_set(x_1179, 0, x_1178);
return x_1179;
}
else
{
obj* x_1180; obj* x_1183; obj* x_1186; obj* x_1189; obj* x_1190; obj* x_1192; obj* x_1193; obj* x_1194; obj* x_1195; obj* x_1198; obj* x_1199; obj* x_1200; obj* x_1201; obj* x_1202; 
x_1180 = lean::cnstr_get(x_1175, 0);
lean::inc(x_1180);
lean::dec(x_1175);
x_1183 = lean::cnstr_get(x_2, 0);
lean::inc(x_1183);
lean::dec(x_2);
x_1186 = lean::cnstr_get(x_1183, 2);
lean::inc(x_1186);
lean::dec(x_1183);
x_1189 = l_Lean_FileMap_toPosition(x_1186, x_1180);
x_1190 = lean::cnstr_get(x_1189, 1);
lean::inc(x_1190);
x_1192 = lean::box(0);
x_1193 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1194 = l_Lean_KVMap_setNat(x_1192, x_1193, x_1190);
x_1195 = lean::cnstr_get(x_1189, 0);
lean::inc(x_1195);
lean::dec(x_1189);
x_1198 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1199 = l_Lean_KVMap_setNat(x_1194, x_1198, x_1195);
x_1200 = lean_expr_mk_mdata(x_1199, x_1174);
if (lean::is_scalar(x_1172)) {
 x_1201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1201 = x_1172;
}
lean::cnstr_set(x_1201, 0, x_1200);
lean::cnstr_set(x_1201, 1, x_1170);
if (lean::is_scalar(x_1167)) {
 x_1202 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1202 = x_1167;
}
lean::cnstr_set(x_1202, 0, x_1201);
return x_1202;
}
}
else
{
obj* x_1205; obj* x_1206; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1172)) {
 x_1205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1205 = x_1172;
}
lean::cnstr_set(x_1205, 0, x_1174);
lean::cnstr_set(x_1205, 1, x_1170);
if (lean::is_scalar(x_1167)) {
 x_1206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1206 = x_1167;
}
lean::cnstr_set(x_1206, 0, x_1205);
return x_1206;
}
}
}
}
}
else
{
obj* x_1209; obj* x_1210; obj* x_1214; obj* x_1215; 
lean::dec(x_8);
lean::dec(x_10);
x_1209 = l_Lean_Parser_Term_projection_HasView;
x_1210 = lean::cnstr_get(x_1209, 0);
lean::inc(x_1210);
lean::dec(x_1209);
lean::inc(x_0);
x_1214 = lean::apply_1(x_1210, x_0);
x_1215 = lean::cnstr_get(x_1214, 2);
lean::inc(x_1215);
if (lean::obj_tag(x_1215) == 0)
{
obj* x_1217; obj* x_1220; obj* x_1224; 
x_1217 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1217);
lean::dec(x_1214);
x_1220 = lean::cnstr_get(x_1215, 0);
lean::inc(x_1220);
lean::dec(x_1215);
lean::inc(x_2);
x_1224 = l_Lean_Elaborator_toPexpr___main(x_1217, x_1, x_2, x_3);
if (lean::obj_tag(x_1224) == 0)
{
obj* x_1228; obj* x_1230; obj* x_1231; 
lean::dec(x_1220);
lean::dec(x_0);
lean::dec(x_2);
x_1228 = lean::cnstr_get(x_1224, 0);
if (lean::is_exclusive(x_1224)) {
 x_1230 = x_1224;
} else {
 lean::inc(x_1228);
 lean::dec(x_1224);
 x_1230 = lean::box(0);
}
if (lean::is_scalar(x_1230)) {
 x_1231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1231 = x_1230;
}
lean::cnstr_set(x_1231, 0, x_1228);
return x_1231;
}
else
{
obj* x_1232; obj* x_1234; obj* x_1235; obj* x_1237; obj* x_1239; obj* x_1240; obj* x_1243; obj* x_1244; obj* x_1245; obj* x_1246; obj* x_1247; 
x_1232 = lean::cnstr_get(x_1224, 0);
if (lean::is_exclusive(x_1224)) {
 lean::cnstr_set(x_1224, 0, lean::box(0));
 x_1234 = x_1224;
} else {
 lean::inc(x_1232);
 lean::dec(x_1224);
 x_1234 = lean::box(0);
}
x_1235 = lean::cnstr_get(x_1232, 0);
x_1237 = lean::cnstr_get(x_1232, 1);
if (lean::is_exclusive(x_1232)) {
 lean::cnstr_set(x_1232, 0, lean::box(0));
 lean::cnstr_set(x_1232, 1, lean::box(0));
 x_1239 = x_1232;
} else {
 lean::inc(x_1235);
 lean::inc(x_1237);
 lean::dec(x_1232);
 x_1239 = lean::box(0);
}
x_1240 = lean::cnstr_get(x_1220, 2);
lean::inc(x_1240);
lean::dec(x_1220);
x_1243 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1243, 0, x_1240);
x_1244 = lean::box(0);
x_1245 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1246 = l_Lean_KVMap_insertCore___main(x_1244, x_1245, x_1243);
x_1247 = lean_expr_mk_mdata(x_1246, x_1235);
if (x_20 == 0)
{
obj* x_1248; 
x_1248 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1248) == 0)
{
obj* x_1251; obj* x_1252; 
lean::dec(x_2);
if (lean::is_scalar(x_1239)) {
 x_1251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1251 = x_1239;
}
lean::cnstr_set(x_1251, 0, x_1247);
lean::cnstr_set(x_1251, 1, x_1237);
if (lean::is_scalar(x_1234)) {
 x_1252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1252 = x_1234;
}
lean::cnstr_set(x_1252, 0, x_1251);
return x_1252;
}
else
{
obj* x_1253; obj* x_1256; obj* x_1259; obj* x_1262; obj* x_1263; obj* x_1265; obj* x_1266; obj* x_1267; obj* x_1270; obj* x_1271; obj* x_1272; obj* x_1273; obj* x_1274; 
x_1253 = lean::cnstr_get(x_1248, 0);
lean::inc(x_1253);
lean::dec(x_1248);
x_1256 = lean::cnstr_get(x_2, 0);
lean::inc(x_1256);
lean::dec(x_2);
x_1259 = lean::cnstr_get(x_1256, 2);
lean::inc(x_1259);
lean::dec(x_1256);
x_1262 = l_Lean_FileMap_toPosition(x_1259, x_1253);
x_1263 = lean::cnstr_get(x_1262, 1);
lean::inc(x_1263);
x_1265 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1266 = l_Lean_KVMap_setNat(x_1244, x_1265, x_1263);
x_1267 = lean::cnstr_get(x_1262, 0);
lean::inc(x_1267);
lean::dec(x_1262);
x_1270 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1271 = l_Lean_KVMap_setNat(x_1266, x_1270, x_1267);
x_1272 = lean_expr_mk_mdata(x_1271, x_1247);
if (lean::is_scalar(x_1239)) {
 x_1273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1273 = x_1239;
}
lean::cnstr_set(x_1273, 0, x_1272);
lean::cnstr_set(x_1273, 1, x_1237);
if (lean::is_scalar(x_1234)) {
 x_1274 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1274 = x_1234;
}
lean::cnstr_set(x_1274, 0, x_1273);
return x_1274;
}
}
else
{
obj* x_1277; obj* x_1278; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1239)) {
 x_1277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1277 = x_1239;
}
lean::cnstr_set(x_1277, 0, x_1247);
lean::cnstr_set(x_1277, 1, x_1237);
if (lean::is_scalar(x_1234)) {
 x_1278 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1278 = x_1234;
}
lean::cnstr_set(x_1278, 0, x_1277);
return x_1278;
}
}
}
else
{
obj* x_1279; obj* x_1282; obj* x_1286; 
x_1279 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1279);
lean::dec(x_1214);
x_1282 = lean::cnstr_get(x_1215, 0);
lean::inc(x_1282);
lean::dec(x_1215);
lean::inc(x_2);
x_1286 = l_Lean_Elaborator_toPexpr___main(x_1279, x_1, x_2, x_3);
if (lean::obj_tag(x_1286) == 0)
{
obj* x_1290; obj* x_1292; obj* x_1293; 
lean::dec(x_1282);
lean::dec(x_0);
lean::dec(x_2);
x_1290 = lean::cnstr_get(x_1286, 0);
if (lean::is_exclusive(x_1286)) {
 x_1292 = x_1286;
} else {
 lean::inc(x_1290);
 lean::dec(x_1286);
 x_1292 = lean::box(0);
}
if (lean::is_scalar(x_1292)) {
 x_1293 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1293 = x_1292;
}
lean::cnstr_set(x_1293, 0, x_1290);
return x_1293;
}
else
{
obj* x_1294; obj* x_1296; obj* x_1297; obj* x_1299; obj* x_1301; obj* x_1302; obj* x_1303; obj* x_1304; obj* x_1305; obj* x_1306; obj* x_1307; 
x_1294 = lean::cnstr_get(x_1286, 0);
if (lean::is_exclusive(x_1286)) {
 lean::cnstr_set(x_1286, 0, lean::box(0));
 x_1296 = x_1286;
} else {
 lean::inc(x_1294);
 lean::dec(x_1286);
 x_1296 = lean::box(0);
}
x_1297 = lean::cnstr_get(x_1294, 0);
x_1299 = lean::cnstr_get(x_1294, 1);
if (lean::is_exclusive(x_1294)) {
 lean::cnstr_set(x_1294, 0, lean::box(0));
 lean::cnstr_set(x_1294, 1, lean::box(0));
 x_1301 = x_1294;
} else {
 lean::inc(x_1297);
 lean::inc(x_1299);
 lean::dec(x_1294);
 x_1301 = lean::box(0);
}
x_1302 = l_Lean_Parser_number_View_toNat___main(x_1282);
x_1303 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1303, 0, x_1302);
x_1304 = lean::box(0);
x_1305 = l_Lean_Elaborator_toPexpr___main___closed__36;
x_1306 = l_Lean_KVMap_insertCore___main(x_1304, x_1305, x_1303);
x_1307 = lean_expr_mk_mdata(x_1306, x_1297);
if (x_20 == 0)
{
obj* x_1308; 
x_1308 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1308) == 0)
{
obj* x_1311; obj* x_1312; 
lean::dec(x_2);
if (lean::is_scalar(x_1301)) {
 x_1311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1311 = x_1301;
}
lean::cnstr_set(x_1311, 0, x_1307);
lean::cnstr_set(x_1311, 1, x_1299);
if (lean::is_scalar(x_1296)) {
 x_1312 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1312 = x_1296;
}
lean::cnstr_set(x_1312, 0, x_1311);
return x_1312;
}
else
{
obj* x_1313; obj* x_1316; obj* x_1319; obj* x_1322; obj* x_1323; obj* x_1325; obj* x_1326; obj* x_1327; obj* x_1330; obj* x_1331; obj* x_1332; obj* x_1333; obj* x_1334; 
x_1313 = lean::cnstr_get(x_1308, 0);
lean::inc(x_1313);
lean::dec(x_1308);
x_1316 = lean::cnstr_get(x_2, 0);
lean::inc(x_1316);
lean::dec(x_2);
x_1319 = lean::cnstr_get(x_1316, 2);
lean::inc(x_1319);
lean::dec(x_1316);
x_1322 = l_Lean_FileMap_toPosition(x_1319, x_1313);
x_1323 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1323);
x_1325 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1326 = l_Lean_KVMap_setNat(x_1304, x_1325, x_1323);
x_1327 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1327);
lean::dec(x_1322);
x_1330 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1331 = l_Lean_KVMap_setNat(x_1326, x_1330, x_1327);
x_1332 = lean_expr_mk_mdata(x_1331, x_1307);
if (lean::is_scalar(x_1301)) {
 x_1333 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1333 = x_1301;
}
lean::cnstr_set(x_1333, 0, x_1332);
lean::cnstr_set(x_1333, 1, x_1299);
if (lean::is_scalar(x_1296)) {
 x_1334 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1334 = x_1296;
}
lean::cnstr_set(x_1334, 0, x_1333);
return x_1334;
}
}
else
{
obj* x_1337; obj* x_1338; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1301)) {
 x_1337 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1337 = x_1301;
}
lean::cnstr_set(x_1337, 0, x_1307);
lean::cnstr_set(x_1337, 1, x_1299);
if (lean::is_scalar(x_1296)) {
 x_1338 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1338 = x_1296;
}
lean::cnstr_set(x_1338, 0, x_1337);
return x_1338;
}
}
}
}
}
else
{
obj* x_1340; obj* x_1341; obj* x_1345; obj* x_1346; 
lean::dec(x_10);
x_1340 = l_Lean_Parser_Term_let_HasView;
x_1341 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1341);
lean::dec(x_1340);
lean::inc(x_0);
x_1345 = lean::apply_1(x_1341, x_0);
x_1346 = lean::cnstr_get(x_1345, 1);
lean::inc(x_1346);
if (lean::obj_tag(x_1346) == 0)
{
obj* x_1348; obj* x_1351; 
x_1348 = lean::cnstr_get(x_1346, 0);
lean::inc(x_1348);
lean::dec(x_1346);
x_1351 = lean::cnstr_get(x_1348, 1);
lean::inc(x_1351);
if (lean::obj_tag(x_1351) == 0)
{
obj* x_1353; 
x_1353 = lean::cnstr_get(x_1348, 2);
lean::inc(x_1353);
if (lean::obj_tag(x_1353) == 0)
{
obj* x_1358; obj* x_1359; obj* x_1361; 
lean::dec(x_1348);
lean::dec(x_1345);
lean::inc(x_0);
x_1358 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1358, 0, x_0);
x_1359 = l_Lean_Elaborator_toPexpr___main___closed__37;
lean::inc(x_2);
x_1361 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1358, x_1359, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1358);
if (lean::obj_tag(x_1361) == 0)
{
obj* x_1367; obj* x_1369; obj* x_1370; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1367 = lean::cnstr_get(x_1361, 0);
if (lean::is_exclusive(x_1361)) {
 x_1369 = x_1361;
} else {
 lean::inc(x_1367);
 lean::dec(x_1361);
 x_1369 = lean::box(0);
}
if (lean::is_scalar(x_1369)) {
 x_1370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1370 = x_1369;
}
lean::cnstr_set(x_1370, 0, x_1367);
return x_1370;
}
else
{
obj* x_1371; 
x_1371 = lean::cnstr_get(x_1361, 0);
lean::inc(x_1371);
lean::dec(x_1361);
x_15 = x_1371;
goto lbl_16;
}
}
else
{
obj* x_1374; obj* x_1377; obj* x_1380; obj* x_1384; 
x_1374 = lean::cnstr_get(x_1348, 0);
lean::inc(x_1374);
lean::dec(x_1348);
x_1377 = lean::cnstr_get(x_1353, 0);
lean::inc(x_1377);
lean::dec(x_1353);
x_1380 = lean::cnstr_get(x_1377, 1);
lean::inc(x_1380);
lean::dec(x_1377);
lean::inc(x_2);
x_1384 = l_Lean_Elaborator_toPexpr___main(x_1380, x_1, x_2, x_3);
if (lean::obj_tag(x_1384) == 0)
{
obj* x_1390; obj* x_1392; obj* x_1393; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1345);
lean::dec(x_1374);
x_1390 = lean::cnstr_get(x_1384, 0);
if (lean::is_exclusive(x_1384)) {
 x_1392 = x_1384;
} else {
 lean::inc(x_1390);
 lean::dec(x_1384);
 x_1392 = lean::box(0);
}
if (lean::is_scalar(x_1392)) {
 x_1393 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1393 = x_1392;
}
lean::cnstr_set(x_1393, 0, x_1390);
return x_1393;
}
else
{
obj* x_1394; obj* x_1397; obj* x_1399; obj* x_1402; obj* x_1405; 
x_1394 = lean::cnstr_get(x_1384, 0);
lean::inc(x_1394);
lean::dec(x_1384);
x_1397 = lean::cnstr_get(x_1394, 0);
lean::inc(x_1397);
x_1399 = lean::cnstr_get(x_1394, 1);
lean::inc(x_1399);
lean::dec(x_1394);
x_1402 = lean::cnstr_get(x_1345, 3);
lean::inc(x_1402);
lean::inc(x_2);
x_1405 = l_Lean_Elaborator_toPexpr___main(x_1402, x_1, x_2, x_1399);
if (lean::obj_tag(x_1405) == 0)
{
obj* x_1412; obj* x_1414; obj* x_1415; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1345);
lean::dec(x_1374);
lean::dec(x_1397);
x_1412 = lean::cnstr_get(x_1405, 0);
if (lean::is_exclusive(x_1405)) {
 x_1414 = x_1405;
} else {
 lean::inc(x_1412);
 lean::dec(x_1405);
 x_1414 = lean::box(0);
}
if (lean::is_scalar(x_1414)) {
 x_1415 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1415 = x_1414;
}
lean::cnstr_set(x_1415, 0, x_1412);
return x_1415;
}
else
{
obj* x_1416; obj* x_1419; obj* x_1421; obj* x_1424; obj* x_1428; 
x_1416 = lean::cnstr_get(x_1405, 0);
lean::inc(x_1416);
lean::dec(x_1405);
x_1419 = lean::cnstr_get(x_1416, 0);
lean::inc(x_1419);
x_1421 = lean::cnstr_get(x_1416, 1);
lean::inc(x_1421);
lean::dec(x_1416);
x_1424 = lean::cnstr_get(x_1345, 5);
lean::inc(x_1424);
lean::dec(x_1345);
lean::inc(x_2);
x_1428 = l_Lean_Elaborator_toPexpr___main(x_1424, x_1, x_2, x_1421);
if (lean::obj_tag(x_1428) == 0)
{
obj* x_1435; obj* x_1437; obj* x_1438; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1374);
lean::dec(x_1397);
lean::dec(x_1419);
x_1435 = lean::cnstr_get(x_1428, 0);
if (lean::is_exclusive(x_1428)) {
 x_1437 = x_1428;
} else {
 lean::inc(x_1435);
 lean::dec(x_1428);
 x_1437 = lean::box(0);
}
if (lean::is_scalar(x_1437)) {
 x_1438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1438 = x_1437;
}
lean::cnstr_set(x_1438, 0, x_1435);
return x_1438;
}
else
{
obj* x_1439; obj* x_1442; obj* x_1444; obj* x_1446; obj* x_1447; obj* x_1448; obj* x_1449; 
x_1439 = lean::cnstr_get(x_1428, 0);
lean::inc(x_1439);
lean::dec(x_1428);
x_1442 = lean::cnstr_get(x_1439, 0);
x_1444 = lean::cnstr_get(x_1439, 1);
if (lean::is_exclusive(x_1439)) {
 x_1446 = x_1439;
} else {
 lean::inc(x_1442);
 lean::inc(x_1444);
 lean::dec(x_1439);
 x_1446 = lean::box(0);
}
x_1447 = l_Lean_Elaborator_mangleIdent(x_1374);
x_1448 = lean_expr_mk_let(x_1447, x_1397, x_1419, x_1442);
if (lean::is_scalar(x_1446)) {
 x_1449 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1449 = x_1446;
}
lean::cnstr_set(x_1449, 0, x_1448);
lean::cnstr_set(x_1449, 1, x_1444);
x_15 = x_1449;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1454; obj* x_1455; obj* x_1457; 
lean::dec(x_1351);
lean::dec(x_1348);
lean::dec(x_1345);
lean::inc(x_0);
x_1454 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1454, 0, x_0);
x_1455 = l_Lean_Elaborator_toPexpr___main___closed__37;
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
else
{
obj* x_1473; obj* x_1474; obj* x_1476; 
lean::dec(x_1345);
lean::dec(x_1346);
lean::inc(x_0);
x_1473 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1473, 0, x_0);
x_1474 = l_Lean_Elaborator_toPexpr___main___closed__37;
lean::inc(x_2);
x_1476 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_1473, x_1474, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1473);
if (lean::obj_tag(x_1476) == 0)
{
obj* x_1482; obj* x_1484; obj* x_1485; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_1482 = lean::cnstr_get(x_1476, 0);
if (lean::is_exclusive(x_1476)) {
 x_1484 = x_1476;
} else {
 lean::inc(x_1482);
 lean::dec(x_1476);
 x_1484 = lean::box(0);
}
if (lean::is_scalar(x_1484)) {
 x_1485 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1485 = x_1484;
}
lean::cnstr_set(x_1485, 0, x_1482);
return x_1485;
}
else
{
obj* x_1486; 
x_1486 = lean::cnstr_get(x_1476, 0);
lean::inc(x_1486);
lean::dec(x_1476);
x_15 = x_1486;
goto lbl_16;
}
}
}
}
else
{
obj* x_1491; obj* x_1492; obj* x_1496; obj* x_1497; obj* x_1500; 
lean::dec(x_8);
lean::dec(x_10);
x_1491 = l_Lean_Parser_Term_show_HasView;
x_1492 = lean::cnstr_get(x_1491, 0);
lean::inc(x_1492);
lean::dec(x_1491);
lean::inc(x_0);
x_1496 = lean::apply_1(x_1492, x_0);
x_1497 = lean::cnstr_get(x_1496, 1);
lean::inc(x_1497);
lean::inc(x_2);
x_1500 = l_Lean_Elaborator_toPexpr___main(x_1497, x_1, x_2, x_3);
if (lean::obj_tag(x_1500) == 0)
{
obj* x_1504; obj* x_1506; obj* x_1507; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1496);
x_1504 = lean::cnstr_get(x_1500, 0);
if (lean::is_exclusive(x_1500)) {
 x_1506 = x_1500;
} else {
 lean::inc(x_1504);
 lean::dec(x_1500);
 x_1506 = lean::box(0);
}
if (lean::is_scalar(x_1506)) {
 x_1507 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1507 = x_1506;
}
lean::cnstr_set(x_1507, 0, x_1504);
return x_1507;
}
else
{
obj* x_1508; obj* x_1511; obj* x_1513; obj* x_1516; obj* x_1519; obj* x_1523; 
x_1508 = lean::cnstr_get(x_1500, 0);
lean::inc(x_1508);
lean::dec(x_1500);
x_1511 = lean::cnstr_get(x_1508, 0);
lean::inc(x_1511);
x_1513 = lean::cnstr_get(x_1508, 1);
lean::inc(x_1513);
lean::dec(x_1508);
x_1516 = lean::cnstr_get(x_1496, 3);
lean::inc(x_1516);
lean::dec(x_1496);
x_1519 = lean::cnstr_get(x_1516, 1);
lean::inc(x_1519);
lean::dec(x_1516);
lean::inc(x_2);
x_1523 = l_Lean_Elaborator_toPexpr___main(x_1519, x_1, x_2, x_1513);
if (lean::obj_tag(x_1523) == 0)
{
obj* x_1527; obj* x_1529; obj* x_1530; 
lean::dec(x_1511);
lean::dec(x_0);
lean::dec(x_2);
x_1527 = lean::cnstr_get(x_1523, 0);
if (lean::is_exclusive(x_1523)) {
 x_1529 = x_1523;
} else {
 lean::inc(x_1527);
 lean::dec(x_1523);
 x_1529 = lean::box(0);
}
if (lean::is_scalar(x_1529)) {
 x_1530 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1530 = x_1529;
}
lean::cnstr_set(x_1530, 0, x_1527);
return x_1530;
}
else
{
obj* x_1531; obj* x_1533; obj* x_1534; obj* x_1536; obj* x_1538; obj* x_1539; uint8 x_1540; obj* x_1541; obj* x_1542; obj* x_1543; obj* x_1544; obj* x_1545; 
x_1531 = lean::cnstr_get(x_1523, 0);
if (lean::is_exclusive(x_1523)) {
 lean::cnstr_set(x_1523, 0, lean::box(0));
 x_1533 = x_1523;
} else {
 lean::inc(x_1531);
 lean::dec(x_1523);
 x_1533 = lean::box(0);
}
x_1534 = lean::cnstr_get(x_1531, 0);
x_1536 = lean::cnstr_get(x_1531, 1);
if (lean::is_exclusive(x_1531)) {
 lean::cnstr_set(x_1531, 0, lean::box(0));
 lean::cnstr_set(x_1531, 1, lean::box(0));
 x_1538 = x_1531;
} else {
 lean::inc(x_1534);
 lean::inc(x_1536);
 lean::dec(x_1531);
 x_1538 = lean::box(0);
}
x_1539 = l_Lean_Elaborator_toPexpr___main___closed__38;
x_1540 = 0;
x_1541 = l_Lean_Elaborator_toPexpr___main___closed__39;
x_1542 = lean_expr_mk_lambda(x_1539, x_1540, x_1511, x_1541);
x_1543 = lean_expr_mk_app(x_1542, x_1534);
x_1544 = l_Lean_Elaborator_toPexpr___main___closed__40;
x_1545 = l_Lean_Elaborator_Expr_mkAnnotation(x_1544, x_1543);
if (x_20 == 0)
{
obj* x_1546; 
x_1546 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1546) == 0)
{
obj* x_1549; obj* x_1550; 
lean::dec(x_2);
if (lean::is_scalar(x_1538)) {
 x_1549 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1549 = x_1538;
}
lean::cnstr_set(x_1549, 0, x_1545);
lean::cnstr_set(x_1549, 1, x_1536);
if (lean::is_scalar(x_1533)) {
 x_1550 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1550 = x_1533;
}
lean::cnstr_set(x_1550, 0, x_1549);
return x_1550;
}
else
{
obj* x_1551; obj* x_1554; obj* x_1557; obj* x_1560; obj* x_1561; obj* x_1563; obj* x_1564; obj* x_1565; obj* x_1566; obj* x_1569; obj* x_1570; obj* x_1571; obj* x_1572; obj* x_1573; 
x_1551 = lean::cnstr_get(x_1546, 0);
lean::inc(x_1551);
lean::dec(x_1546);
x_1554 = lean::cnstr_get(x_2, 0);
lean::inc(x_1554);
lean::dec(x_2);
x_1557 = lean::cnstr_get(x_1554, 2);
lean::inc(x_1557);
lean::dec(x_1554);
x_1560 = l_Lean_FileMap_toPosition(x_1557, x_1551);
x_1561 = lean::cnstr_get(x_1560, 1);
lean::inc(x_1561);
x_1563 = lean::box(0);
x_1564 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1565 = l_Lean_KVMap_setNat(x_1563, x_1564, x_1561);
x_1566 = lean::cnstr_get(x_1560, 0);
lean::inc(x_1566);
lean::dec(x_1560);
x_1569 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1570 = l_Lean_KVMap_setNat(x_1565, x_1569, x_1566);
x_1571 = lean_expr_mk_mdata(x_1570, x_1545);
if (lean::is_scalar(x_1538)) {
 x_1572 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1572 = x_1538;
}
lean::cnstr_set(x_1572, 0, x_1571);
lean::cnstr_set(x_1572, 1, x_1536);
if (lean::is_scalar(x_1533)) {
 x_1573 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1573 = x_1533;
}
lean::cnstr_set(x_1573, 0, x_1572);
return x_1573;
}
}
else
{
obj* x_1576; obj* x_1577; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1538)) {
 x_1576 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1576 = x_1538;
}
lean::cnstr_set(x_1576, 0, x_1545);
lean::cnstr_set(x_1576, 1, x_1536);
if (lean::is_scalar(x_1533)) {
 x_1577 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1577 = x_1533;
}
lean::cnstr_set(x_1577, 0, x_1576);
return x_1577;
}
}
}
}
}
else
{
obj* x_1579; obj* x_1580; obj* x_1584; obj* x_1585; 
lean::dec(x_10);
x_1579 = l_Lean_Parser_Term_have_HasView;
x_1580 = lean::cnstr_get(x_1579, 0);
lean::inc(x_1580);
lean::dec(x_1579);
lean::inc(x_0);
x_1584 = lean::apply_1(x_1580, x_0);
x_1585 = lean::cnstr_get(x_1584, 1);
lean::inc(x_1585);
if (lean::obj_tag(x_1585) == 0)
{
obj* x_1587; obj* x_1589; obj* x_1592; 
x_1587 = lean::cnstr_get(x_1584, 2);
lean::inc(x_1587);
x_1589 = lean::cnstr_get(x_1584, 5);
lean::inc(x_1589);
lean::inc(x_2);
x_1592 = l_Lean_Elaborator_toPexpr___main(x_1587, x_1, x_2, x_3);
if (lean::obj_tag(x_1592) == 0)
{
obj* x_1598; obj* x_1600; obj* x_1601; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1584);
lean::dec(x_1589);
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
obj* x_1602; obj* x_1605; obj* x_1607; obj* x_1611; 
x_1602 = lean::cnstr_get(x_1592, 0);
lean::inc(x_1602);
lean::dec(x_1592);
x_1605 = lean::cnstr_get(x_1602, 0);
lean::inc(x_1605);
x_1607 = lean::cnstr_get(x_1602, 1);
lean::inc(x_1607);
lean::dec(x_1602);
lean::inc(x_2);
x_1611 = l_Lean_Elaborator_toPexpr___main(x_1589, x_1, x_2, x_1607);
if (lean::obj_tag(x_1611) == 0)
{
obj* x_1617; obj* x_1619; obj* x_1620; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1584);
lean::dec(x_1605);
x_1617 = lean::cnstr_get(x_1611, 0);
if (lean::is_exclusive(x_1611)) {
 x_1619 = x_1611;
} else {
 lean::inc(x_1617);
 lean::dec(x_1611);
 x_1619 = lean::box(0);
}
if (lean::is_scalar(x_1619)) {
 x_1620 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1620 = x_1619;
}
lean::cnstr_set(x_1620, 0, x_1617);
return x_1620;
}
else
{
obj* x_1621; obj* x_1624; obj* x_1626; obj* x_1629; uint8 x_1630; obj* x_1631; obj* x_1632; 
x_1621 = lean::cnstr_get(x_1611, 0);
lean::inc(x_1621);
lean::dec(x_1611);
x_1624 = lean::cnstr_get(x_1621, 0);
lean::inc(x_1624);
x_1626 = lean::cnstr_get(x_1621, 1);
lean::inc(x_1626);
lean::dec(x_1621);
x_1629 = l_Lean_Elaborator_toPexpr___main___closed__38;
x_1630 = 0;
x_1631 = lean_expr_mk_lambda(x_1629, x_1630, x_1605, x_1624);
x_1632 = lean::cnstr_get(x_1584, 3);
lean::inc(x_1632);
lean::dec(x_1584);
if (lean::obj_tag(x_1632) == 0)
{
obj* x_1635; obj* x_1638; obj* x_1642; 
x_1635 = lean::cnstr_get(x_1632, 0);
lean::inc(x_1635);
lean::dec(x_1632);
x_1638 = lean::cnstr_get(x_1635, 1);
lean::inc(x_1638);
lean::dec(x_1635);
lean::inc(x_2);
x_1642 = l_Lean_Elaborator_toPexpr___main(x_1638, x_1, x_2, x_1626);
if (lean::obj_tag(x_1642) == 0)
{
obj* x_1647; obj* x_1649; obj* x_1650; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1631);
x_1647 = lean::cnstr_get(x_1642, 0);
if (lean::is_exclusive(x_1642)) {
 x_1649 = x_1642;
} else {
 lean::inc(x_1647);
 lean::dec(x_1642);
 x_1649 = lean::box(0);
}
if (lean::is_scalar(x_1649)) {
 x_1650 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1650 = x_1649;
}
lean::cnstr_set(x_1650, 0, x_1647);
return x_1650;
}
else
{
obj* x_1651; obj* x_1654; obj* x_1656; obj* x_1658; obj* x_1659; obj* x_1660; obj* x_1661; obj* x_1662; 
x_1651 = lean::cnstr_get(x_1642, 0);
lean::inc(x_1651);
lean::dec(x_1642);
x_1654 = lean::cnstr_get(x_1651, 0);
x_1656 = lean::cnstr_get(x_1651, 1);
if (lean::is_exclusive(x_1651)) {
 x_1658 = x_1651;
} else {
 lean::inc(x_1654);
 lean::inc(x_1656);
 lean::dec(x_1651);
 x_1658 = lean::box(0);
}
x_1659 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1660 = l_Lean_Elaborator_Expr_mkAnnotation(x_1659, x_1631);
x_1661 = lean_expr_mk_app(x_1660, x_1654);
if (lean::is_scalar(x_1658)) {
 x_1662 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1662 = x_1658;
}
lean::cnstr_set(x_1662, 0, x_1661);
lean::cnstr_set(x_1662, 1, x_1656);
x_15 = x_1662;
goto lbl_16;
}
}
else
{
obj* x_1663; obj* x_1666; obj* x_1669; obj* x_1673; 
x_1663 = lean::cnstr_get(x_1632, 0);
lean::inc(x_1663);
lean::dec(x_1632);
x_1666 = lean::cnstr_get(x_1663, 1);
lean::inc(x_1666);
lean::dec(x_1663);
x_1669 = lean::cnstr_get(x_1666, 1);
lean::inc(x_1669);
lean::dec(x_1666);
lean::inc(x_2);
x_1673 = l_Lean_Elaborator_toPexpr___main(x_1669, x_1, x_2, x_1626);
if (lean::obj_tag(x_1673) == 0)
{
obj* x_1678; obj* x_1680; obj* x_1681; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1631);
x_1678 = lean::cnstr_get(x_1673, 0);
if (lean::is_exclusive(x_1673)) {
 x_1680 = x_1673;
} else {
 lean::inc(x_1678);
 lean::dec(x_1673);
 x_1680 = lean::box(0);
}
if (lean::is_scalar(x_1680)) {
 x_1681 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1681 = x_1680;
}
lean::cnstr_set(x_1681, 0, x_1678);
return x_1681;
}
else
{
obj* x_1682; obj* x_1685; obj* x_1687; obj* x_1689; obj* x_1690; obj* x_1691; obj* x_1692; obj* x_1693; 
x_1682 = lean::cnstr_get(x_1673, 0);
lean::inc(x_1682);
lean::dec(x_1673);
x_1685 = lean::cnstr_get(x_1682, 0);
x_1687 = lean::cnstr_get(x_1682, 1);
if (lean::is_exclusive(x_1682)) {
 x_1689 = x_1682;
} else {
 lean::inc(x_1685);
 lean::inc(x_1687);
 lean::dec(x_1682);
 x_1689 = lean::box(0);
}
x_1690 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1691 = l_Lean_Elaborator_Expr_mkAnnotation(x_1690, x_1631);
x_1692 = lean_expr_mk_app(x_1691, x_1685);
if (lean::is_scalar(x_1689)) {
 x_1693 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1693 = x_1689;
}
lean::cnstr_set(x_1693, 0, x_1692);
lean::cnstr_set(x_1693, 1, x_1687);
x_15 = x_1693;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_1694; obj* x_1696; obj* x_1698; obj* x_1702; 
x_1694 = lean::cnstr_get(x_1584, 2);
lean::inc(x_1694);
x_1696 = lean::cnstr_get(x_1584, 5);
lean::inc(x_1696);
x_1698 = lean::cnstr_get(x_1585, 0);
lean::inc(x_1698);
lean::dec(x_1585);
lean::inc(x_2);
x_1702 = l_Lean_Elaborator_toPexpr___main(x_1694, x_1, x_2, x_3);
if (lean::obj_tag(x_1702) == 0)
{
obj* x_1709; obj* x_1711; obj* x_1712; 
lean::dec(x_1698);
lean::dec(x_1696);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1584);
x_1709 = lean::cnstr_get(x_1702, 0);
if (lean::is_exclusive(x_1702)) {
 x_1711 = x_1702;
} else {
 lean::inc(x_1709);
 lean::dec(x_1702);
 x_1711 = lean::box(0);
}
if (lean::is_scalar(x_1711)) {
 x_1712 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1712 = x_1711;
}
lean::cnstr_set(x_1712, 0, x_1709);
return x_1712;
}
else
{
obj* x_1713; obj* x_1716; obj* x_1718; obj* x_1722; 
x_1713 = lean::cnstr_get(x_1702, 0);
lean::inc(x_1713);
lean::dec(x_1702);
x_1716 = lean::cnstr_get(x_1713, 0);
lean::inc(x_1716);
x_1718 = lean::cnstr_get(x_1713, 1);
lean::inc(x_1718);
lean::dec(x_1713);
lean::inc(x_2);
x_1722 = l_Lean_Elaborator_toPexpr___main(x_1696, x_1, x_2, x_1718);
if (lean::obj_tag(x_1722) == 0)
{
obj* x_1729; obj* x_1731; obj* x_1732; 
lean::dec(x_1716);
lean::dec(x_1698);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1584);
x_1729 = lean::cnstr_get(x_1722, 0);
if (lean::is_exclusive(x_1722)) {
 x_1731 = x_1722;
} else {
 lean::inc(x_1729);
 lean::dec(x_1722);
 x_1731 = lean::box(0);
}
if (lean::is_scalar(x_1731)) {
 x_1732 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1732 = x_1731;
}
lean::cnstr_set(x_1732, 0, x_1729);
return x_1732;
}
else
{
obj* x_1733; obj* x_1736; obj* x_1738; obj* x_1741; obj* x_1744; uint8 x_1745; obj* x_1746; obj* x_1747; 
x_1733 = lean::cnstr_get(x_1722, 0);
lean::inc(x_1733);
lean::dec(x_1722);
x_1736 = lean::cnstr_get(x_1733, 0);
lean::inc(x_1736);
x_1738 = lean::cnstr_get(x_1733, 1);
lean::inc(x_1738);
lean::dec(x_1733);
x_1741 = lean::cnstr_get(x_1698, 0);
lean::inc(x_1741);
lean::dec(x_1698);
x_1744 = l_Lean_Elaborator_mangleIdent(x_1741);
x_1745 = 0;
x_1746 = lean_expr_mk_lambda(x_1744, x_1745, x_1716, x_1736);
x_1747 = lean::cnstr_get(x_1584, 3);
lean::inc(x_1747);
lean::dec(x_1584);
if (lean::obj_tag(x_1747) == 0)
{
obj* x_1750; obj* x_1753; obj* x_1757; 
x_1750 = lean::cnstr_get(x_1747, 0);
lean::inc(x_1750);
lean::dec(x_1747);
x_1753 = lean::cnstr_get(x_1750, 1);
lean::inc(x_1753);
lean::dec(x_1750);
lean::inc(x_2);
x_1757 = l_Lean_Elaborator_toPexpr___main(x_1753, x_1, x_2, x_1738);
if (lean::obj_tag(x_1757) == 0)
{
obj* x_1762; obj* x_1764; obj* x_1765; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1746);
x_1762 = lean::cnstr_get(x_1757, 0);
if (lean::is_exclusive(x_1757)) {
 x_1764 = x_1757;
} else {
 lean::inc(x_1762);
 lean::dec(x_1757);
 x_1764 = lean::box(0);
}
if (lean::is_scalar(x_1764)) {
 x_1765 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1765 = x_1764;
}
lean::cnstr_set(x_1765, 0, x_1762);
return x_1765;
}
else
{
obj* x_1766; obj* x_1769; obj* x_1771; obj* x_1773; obj* x_1774; obj* x_1775; obj* x_1776; obj* x_1777; 
x_1766 = lean::cnstr_get(x_1757, 0);
lean::inc(x_1766);
lean::dec(x_1757);
x_1769 = lean::cnstr_get(x_1766, 0);
x_1771 = lean::cnstr_get(x_1766, 1);
if (lean::is_exclusive(x_1766)) {
 x_1773 = x_1766;
} else {
 lean::inc(x_1769);
 lean::inc(x_1771);
 lean::dec(x_1766);
 x_1773 = lean::box(0);
}
x_1774 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1775 = l_Lean_Elaborator_Expr_mkAnnotation(x_1774, x_1746);
x_1776 = lean_expr_mk_app(x_1775, x_1769);
if (lean::is_scalar(x_1773)) {
 x_1777 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1777 = x_1773;
}
lean::cnstr_set(x_1777, 0, x_1776);
lean::cnstr_set(x_1777, 1, x_1771);
x_15 = x_1777;
goto lbl_16;
}
}
else
{
obj* x_1778; obj* x_1781; obj* x_1784; obj* x_1788; 
x_1778 = lean::cnstr_get(x_1747, 0);
lean::inc(x_1778);
lean::dec(x_1747);
x_1781 = lean::cnstr_get(x_1778, 1);
lean::inc(x_1781);
lean::dec(x_1778);
x_1784 = lean::cnstr_get(x_1781, 1);
lean::inc(x_1784);
lean::dec(x_1781);
lean::inc(x_2);
x_1788 = l_Lean_Elaborator_toPexpr___main(x_1784, x_1, x_2, x_1738);
if (lean::obj_tag(x_1788) == 0)
{
obj* x_1793; obj* x_1795; obj* x_1796; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_1746);
x_1793 = lean::cnstr_get(x_1788, 0);
if (lean::is_exclusive(x_1788)) {
 x_1795 = x_1788;
} else {
 lean::inc(x_1793);
 lean::dec(x_1788);
 x_1795 = lean::box(0);
}
if (lean::is_scalar(x_1795)) {
 x_1796 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1796 = x_1795;
}
lean::cnstr_set(x_1796, 0, x_1793);
return x_1796;
}
else
{
obj* x_1797; obj* x_1800; obj* x_1802; obj* x_1804; obj* x_1805; obj* x_1806; obj* x_1807; obj* x_1808; 
x_1797 = lean::cnstr_get(x_1788, 0);
lean::inc(x_1797);
lean::dec(x_1788);
x_1800 = lean::cnstr_get(x_1797, 0);
x_1802 = lean::cnstr_get(x_1797, 1);
if (lean::is_exclusive(x_1797)) {
 x_1804 = x_1797;
} else {
 lean::inc(x_1800);
 lean::inc(x_1802);
 lean::dec(x_1797);
 x_1804 = lean::box(0);
}
x_1805 = l_Lean_Elaborator_toPexpr___main___closed__41;
x_1806 = l_Lean_Elaborator_Expr_mkAnnotation(x_1805, x_1746);
x_1807 = lean_expr_mk_app(x_1806, x_1800);
if (lean::is_scalar(x_1804)) {
 x_1808 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1808 = x_1804;
}
lean::cnstr_set(x_1808, 0, x_1807);
lean::cnstr_set(x_1808, 1, x_1802);
x_15 = x_1808;
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
obj* x_1811; 
x_1811 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1811) == 0)
{
obj* x_1814; obj* x_1815; obj* x_1816; 
lean::dec(x_2);
x_1814 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_1815 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1815, 0, x_1814);
lean::cnstr_set(x_1815, 1, x_3);
x_1816 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1816, 0, x_1815);
return x_1816;
}
else
{
obj* x_1817; obj* x_1820; obj* x_1823; obj* x_1826; obj* x_1827; obj* x_1829; obj* x_1830; obj* x_1831; obj* x_1832; obj* x_1835; obj* x_1836; obj* x_1837; obj* x_1838; obj* x_1839; obj* x_1840; 
x_1817 = lean::cnstr_get(x_1811, 0);
lean::inc(x_1817);
lean::dec(x_1811);
x_1820 = lean::cnstr_get(x_2, 0);
lean::inc(x_1820);
lean::dec(x_2);
x_1823 = lean::cnstr_get(x_1820, 2);
lean::inc(x_1823);
lean::dec(x_1820);
x_1826 = l_Lean_FileMap_toPosition(x_1823, x_1817);
x_1827 = lean::cnstr_get(x_1826, 1);
lean::inc(x_1827);
x_1829 = lean::box(0);
x_1830 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1831 = l_Lean_KVMap_setNat(x_1829, x_1830, x_1827);
x_1832 = lean::cnstr_get(x_1826, 0);
lean::inc(x_1832);
lean::dec(x_1826);
x_1835 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1836 = l_Lean_KVMap_setNat(x_1831, x_1835, x_1832);
x_1837 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_1838 = lean_expr_mk_mdata(x_1836, x_1837);
x_1839 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1839, 0, x_1838);
lean::cnstr_set(x_1839, 1, x_3);
x_1840 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1840, 0, x_1839);
return x_1840;
}
}
else
{
obj* x_1843; obj* x_1844; obj* x_1845; 
lean::dec(x_0);
lean::dec(x_2);
x_1843 = l_Lean_Elaborator_toPexpr___main___closed__42;
x_1844 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1844, 0, x_1843);
lean::cnstr_set(x_1844, 1, x_3);
x_1845 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1845, 0, x_1844);
return x_1845;
}
}
}
else
{
obj* x_1848; obj* x_1849; obj* x_1853; obj* x_1854; obj* x_1857; obj* x_1858; obj* x_1859; obj* x_1861; 
lean::dec(x_8);
lean::dec(x_10);
x_1848 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_1849 = lean::cnstr_get(x_1848, 0);
lean::inc(x_1849);
lean::dec(x_1848);
lean::inc(x_0);
x_1853 = lean::apply_1(x_1849, x_0);
x_1854 = lean::cnstr_get(x_1853, 1);
lean::inc(x_1854);
lean::dec(x_1853);
x_1857 = l_List_map___main___at_Lean_Elaborator_toPexpr___main___spec__19(x_1854);
x_1858 = l_Lean_Expander_getOptType___main___closed__1;
x_1859 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_1858, x_1857);
lean::inc(x_2);
x_1861 = l_Lean_Elaborator_toPexpr___main(x_1859, x_1, x_2, x_3);
if (lean::obj_tag(x_1861) == 0)
{
obj* x_1864; obj* x_1866; obj* x_1867; 
lean::dec(x_0);
lean::dec(x_2);
x_1864 = lean::cnstr_get(x_1861, 0);
if (lean::is_exclusive(x_1861)) {
 x_1866 = x_1861;
} else {
 lean::inc(x_1864);
 lean::dec(x_1861);
 x_1866 = lean::box(0);
}
if (lean::is_scalar(x_1866)) {
 x_1867 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1867 = x_1866;
}
lean::cnstr_set(x_1867, 0, x_1864);
return x_1867;
}
else
{
obj* x_1868; obj* x_1870; obj* x_1871; obj* x_1873; obj* x_1875; obj* x_1876; obj* x_1877; 
x_1868 = lean::cnstr_get(x_1861, 0);
if (lean::is_exclusive(x_1861)) {
 lean::cnstr_set(x_1861, 0, lean::box(0));
 x_1870 = x_1861;
} else {
 lean::inc(x_1868);
 lean::dec(x_1861);
 x_1870 = lean::box(0);
}
x_1871 = lean::cnstr_get(x_1868, 0);
x_1873 = lean::cnstr_get(x_1868, 1);
if (lean::is_exclusive(x_1868)) {
 lean::cnstr_set(x_1868, 0, lean::box(0));
 lean::cnstr_set(x_1868, 1, lean::box(0));
 x_1875 = x_1868;
} else {
 lean::inc(x_1871);
 lean::inc(x_1873);
 lean::dec(x_1868);
 x_1875 = lean::box(0);
}
x_1876 = l_Lean_Elaborator_toPexpr___main___closed__43;
x_1877 = l_Lean_Elaborator_Expr_mkAnnotation(x_1876, x_1871);
if (x_20 == 0)
{
obj* x_1878; 
x_1878 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1878) == 0)
{
obj* x_1881; obj* x_1882; 
lean::dec(x_2);
if (lean::is_scalar(x_1875)) {
 x_1881 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1881 = x_1875;
}
lean::cnstr_set(x_1881, 0, x_1877);
lean::cnstr_set(x_1881, 1, x_1873);
if (lean::is_scalar(x_1870)) {
 x_1882 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1882 = x_1870;
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
if (lean::is_scalar(x_1875)) {
 x_1904 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1904 = x_1875;
}
lean::cnstr_set(x_1904, 0, x_1903);
lean::cnstr_set(x_1904, 1, x_1873);
if (lean::is_scalar(x_1870)) {
 x_1905 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1905 = x_1870;
}
lean::cnstr_set(x_1905, 0, x_1904);
return x_1905;
}
}
else
{
obj* x_1908; obj* x_1909; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1875)) {
 x_1908 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1908 = x_1875;
}
lean::cnstr_set(x_1908, 0, x_1877);
lean::cnstr_set(x_1908, 1, x_1873);
if (lean::is_scalar(x_1870)) {
 x_1909 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1909 = x_1870;
}
lean::cnstr_set(x_1909, 0, x_1908);
return x_1909;
}
}
}
}
else
{
obj* x_1912; obj* x_1913; obj* x_1917; obj* x_1918; obj* x_1919; obj* x_1922; obj* x_1924; 
lean::dec(x_8);
lean::dec(x_10);
x_1912 = l_Lean_Parser_Term_sortApp_HasView;
x_1913 = lean::cnstr_get(x_1912, 0);
lean::inc(x_1913);
lean::dec(x_1912);
lean::inc(x_0);
x_1917 = lean::apply_1(x_1913, x_0);
x_1918 = l_Lean_Parser_Term_sort_HasView;
x_1919 = lean::cnstr_get(x_1918, 0);
lean::inc(x_1919);
lean::dec(x_1918);
x_1922 = lean::cnstr_get(x_1917, 0);
lean::inc(x_1922);
x_1924 = lean::apply_1(x_1919, x_1922);
if (lean::obj_tag(x_1924) == 0)
{
obj* x_1926; obj* x_1930; 
lean::dec(x_1924);
x_1926 = lean::cnstr_get(x_1917, 1);
lean::inc(x_1926);
lean::dec(x_1917);
lean::inc(x_2);
x_1930 = l_Lean_Elaborator_toLevel___main(x_1926, x_1, x_2, x_3);
if (lean::obj_tag(x_1930) == 0)
{
obj* x_1933; obj* x_1935; obj* x_1936; 
lean::dec(x_0);
lean::dec(x_2);
x_1933 = lean::cnstr_get(x_1930, 0);
if (lean::is_exclusive(x_1930)) {
 x_1935 = x_1930;
} else {
 lean::inc(x_1933);
 lean::dec(x_1930);
 x_1935 = lean::box(0);
}
if (lean::is_scalar(x_1935)) {
 x_1936 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1936 = x_1935;
}
lean::cnstr_set(x_1936, 0, x_1933);
return x_1936;
}
else
{
obj* x_1937; obj* x_1939; obj* x_1940; obj* x_1942; obj* x_1944; obj* x_1945; 
x_1937 = lean::cnstr_get(x_1930, 0);
if (lean::is_exclusive(x_1930)) {
 lean::cnstr_set(x_1930, 0, lean::box(0));
 x_1939 = x_1930;
} else {
 lean::inc(x_1937);
 lean::dec(x_1930);
 x_1939 = lean::box(0);
}
x_1940 = lean::cnstr_get(x_1937, 0);
x_1942 = lean::cnstr_get(x_1937, 1);
if (lean::is_exclusive(x_1937)) {
 lean::cnstr_set(x_1937, 0, lean::box(0));
 lean::cnstr_set(x_1937, 1, lean::box(0));
 x_1944 = x_1937;
} else {
 lean::inc(x_1940);
 lean::inc(x_1942);
 lean::dec(x_1937);
 x_1944 = lean::box(0);
}
x_1945 = lean_expr_mk_sort(x_1940);
if (x_20 == 0)
{
obj* x_1946; 
x_1946 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1946) == 0)
{
obj* x_1949; obj* x_1950; 
lean::dec(x_2);
if (lean::is_scalar(x_1944)) {
 x_1949 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1949 = x_1944;
}
lean::cnstr_set(x_1949, 0, x_1945);
lean::cnstr_set(x_1949, 1, x_1942);
if (lean::is_scalar(x_1939)) {
 x_1950 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1950 = x_1939;
}
lean::cnstr_set(x_1950, 0, x_1949);
return x_1950;
}
else
{
obj* x_1951; obj* x_1954; obj* x_1957; obj* x_1960; obj* x_1961; obj* x_1963; obj* x_1964; obj* x_1965; obj* x_1966; obj* x_1969; obj* x_1970; obj* x_1971; obj* x_1972; obj* x_1973; 
x_1951 = lean::cnstr_get(x_1946, 0);
lean::inc(x_1951);
lean::dec(x_1946);
x_1954 = lean::cnstr_get(x_2, 0);
lean::inc(x_1954);
lean::dec(x_2);
x_1957 = lean::cnstr_get(x_1954, 2);
lean::inc(x_1957);
lean::dec(x_1954);
x_1960 = l_Lean_FileMap_toPosition(x_1957, x_1951);
x_1961 = lean::cnstr_get(x_1960, 1);
lean::inc(x_1961);
x_1963 = lean::box(0);
x_1964 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_1965 = l_Lean_KVMap_setNat(x_1963, x_1964, x_1961);
x_1966 = lean::cnstr_get(x_1960, 0);
lean::inc(x_1966);
lean::dec(x_1960);
x_1969 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_1970 = l_Lean_KVMap_setNat(x_1965, x_1969, x_1966);
x_1971 = lean_expr_mk_mdata(x_1970, x_1945);
if (lean::is_scalar(x_1944)) {
 x_1972 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1972 = x_1944;
}
lean::cnstr_set(x_1972, 0, x_1971);
lean::cnstr_set(x_1972, 1, x_1942);
if (lean::is_scalar(x_1939)) {
 x_1973 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1973 = x_1939;
}
lean::cnstr_set(x_1973, 0, x_1972);
return x_1973;
}
}
else
{
obj* x_1976; obj* x_1977; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1944)) {
 x_1976 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1976 = x_1944;
}
lean::cnstr_set(x_1976, 0, x_1945);
lean::cnstr_set(x_1976, 1, x_1942);
if (lean::is_scalar(x_1939)) {
 x_1977 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1977 = x_1939;
}
lean::cnstr_set(x_1977, 0, x_1976);
return x_1977;
}
}
}
else
{
obj* x_1979; obj* x_1983; 
lean::dec(x_1924);
x_1979 = lean::cnstr_get(x_1917, 1);
lean::inc(x_1979);
lean::dec(x_1917);
lean::inc(x_2);
x_1983 = l_Lean_Elaborator_toLevel___main(x_1979, x_1, x_2, x_3);
if (lean::obj_tag(x_1983) == 0)
{
obj* x_1986; obj* x_1988; obj* x_1989; 
lean::dec(x_0);
lean::dec(x_2);
x_1986 = lean::cnstr_get(x_1983, 0);
if (lean::is_exclusive(x_1983)) {
 x_1988 = x_1983;
} else {
 lean::inc(x_1986);
 lean::dec(x_1983);
 x_1988 = lean::box(0);
}
if (lean::is_scalar(x_1988)) {
 x_1989 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1989 = x_1988;
}
lean::cnstr_set(x_1989, 0, x_1986);
return x_1989;
}
else
{
obj* x_1990; obj* x_1992; obj* x_1993; obj* x_1995; obj* x_1997; obj* x_1998; obj* x_1999; 
x_1990 = lean::cnstr_get(x_1983, 0);
if (lean::is_exclusive(x_1983)) {
 lean::cnstr_set(x_1983, 0, lean::box(0));
 x_1992 = x_1983;
} else {
 lean::inc(x_1990);
 lean::dec(x_1983);
 x_1992 = lean::box(0);
}
x_1993 = lean::cnstr_get(x_1990, 0);
x_1995 = lean::cnstr_get(x_1990, 1);
if (lean::is_exclusive(x_1990)) {
 lean::cnstr_set(x_1990, 0, lean::box(0));
 lean::cnstr_set(x_1990, 1, lean::box(0));
 x_1997 = x_1990;
} else {
 lean::inc(x_1993);
 lean::inc(x_1995);
 lean::dec(x_1990);
 x_1997 = lean::box(0);
}
x_1998 = level_mk_succ(x_1993);
x_1999 = lean_expr_mk_sort(x_1998);
if (x_20 == 0)
{
obj* x_2000; 
x_2000 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2000) == 0)
{
obj* x_2003; obj* x_2004; 
lean::dec(x_2);
if (lean::is_scalar(x_1997)) {
 x_2003 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2003 = x_1997;
}
lean::cnstr_set(x_2003, 0, x_1999);
lean::cnstr_set(x_2003, 1, x_1995);
if (lean::is_scalar(x_1992)) {
 x_2004 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2004 = x_1992;
}
lean::cnstr_set(x_2004, 0, x_2003);
return x_2004;
}
else
{
obj* x_2005; obj* x_2008; obj* x_2011; obj* x_2014; obj* x_2015; obj* x_2017; obj* x_2018; obj* x_2019; obj* x_2020; obj* x_2023; obj* x_2024; obj* x_2025; obj* x_2026; obj* x_2027; 
x_2005 = lean::cnstr_get(x_2000, 0);
lean::inc(x_2005);
lean::dec(x_2000);
x_2008 = lean::cnstr_get(x_2, 0);
lean::inc(x_2008);
lean::dec(x_2);
x_2011 = lean::cnstr_get(x_2008, 2);
lean::inc(x_2011);
lean::dec(x_2008);
x_2014 = l_Lean_FileMap_toPosition(x_2011, x_2005);
x_2015 = lean::cnstr_get(x_2014, 1);
lean::inc(x_2015);
x_2017 = lean::box(0);
x_2018 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2019 = l_Lean_KVMap_setNat(x_2017, x_2018, x_2015);
x_2020 = lean::cnstr_get(x_2014, 0);
lean::inc(x_2020);
lean::dec(x_2014);
x_2023 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2024 = l_Lean_KVMap_setNat(x_2019, x_2023, x_2020);
x_2025 = lean_expr_mk_mdata(x_2024, x_1999);
if (lean::is_scalar(x_1997)) {
 x_2026 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2026 = x_1997;
}
lean::cnstr_set(x_2026, 0, x_2025);
lean::cnstr_set(x_2026, 1, x_1995);
if (lean::is_scalar(x_1992)) {
 x_2027 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2027 = x_1992;
}
lean::cnstr_set(x_2027, 0, x_2026);
return x_2027;
}
}
else
{
obj* x_2030; obj* x_2031; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_1997)) {
 x_2030 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2030 = x_1997;
}
lean::cnstr_set(x_2030, 0, x_1999);
lean::cnstr_set(x_2030, 1, x_1995);
if (lean::is_scalar(x_1992)) {
 x_2031 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2031 = x_1992;
}
lean::cnstr_set(x_2031, 0, x_2030);
return x_2031;
}
}
}
}
}
else
{
obj* x_2034; obj* x_2035; obj* x_2039; 
lean::dec(x_8);
lean::dec(x_10);
x_2034 = l_Lean_Parser_Term_sort_HasView;
x_2035 = lean::cnstr_get(x_2034, 0);
lean::inc(x_2035);
lean::dec(x_2034);
lean::inc(x_0);
x_2039 = lean::apply_1(x_2035, x_0);
if (lean::obj_tag(x_2039) == 0)
{
lean::dec(x_2039);
if (x_20 == 0)
{
obj* x_2041; 
x_2041 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2041) == 0)
{
obj* x_2044; obj* x_2045; obj* x_2046; 
lean::dec(x_2);
x_2044 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2045 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2045, 0, x_2044);
lean::cnstr_set(x_2045, 1, x_3);
x_2046 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2046, 0, x_2045);
return x_2046;
}
else
{
obj* x_2047; obj* x_2050; obj* x_2053; obj* x_2056; obj* x_2057; obj* x_2059; obj* x_2060; obj* x_2061; obj* x_2062; obj* x_2065; obj* x_2066; obj* x_2067; obj* x_2068; obj* x_2069; obj* x_2070; 
x_2047 = lean::cnstr_get(x_2041, 0);
lean::inc(x_2047);
lean::dec(x_2041);
x_2050 = lean::cnstr_get(x_2, 0);
lean::inc(x_2050);
lean::dec(x_2);
x_2053 = lean::cnstr_get(x_2050, 2);
lean::inc(x_2053);
lean::dec(x_2050);
x_2056 = l_Lean_FileMap_toPosition(x_2053, x_2047);
x_2057 = lean::cnstr_get(x_2056, 1);
lean::inc(x_2057);
x_2059 = lean::box(0);
x_2060 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2061 = l_Lean_KVMap_setNat(x_2059, x_2060, x_2057);
x_2062 = lean::cnstr_get(x_2056, 0);
lean::inc(x_2062);
lean::dec(x_2056);
x_2065 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2066 = l_Lean_KVMap_setNat(x_2061, x_2065, x_2062);
x_2067 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2068 = lean_expr_mk_mdata(x_2066, x_2067);
x_2069 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2069, 0, x_2068);
lean::cnstr_set(x_2069, 1, x_3);
x_2070 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2070, 0, x_2069);
return x_2070;
}
}
else
{
obj* x_2073; obj* x_2074; obj* x_2075; 
lean::dec(x_0);
lean::dec(x_2);
x_2073 = l_Lean_Elaborator_toPexpr___main___closed__27;
x_2074 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2074, 0, x_2073);
lean::cnstr_set(x_2074, 1, x_3);
x_2075 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2075, 0, x_2074);
return x_2075;
}
}
else
{
lean::dec(x_2039);
if (x_20 == 0)
{
obj* x_2077; 
x_2077 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2077) == 0)
{
obj* x_2080; obj* x_2081; obj* x_2082; 
lean::dec(x_2);
x_2080 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_2081 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2081, 0, x_2080);
lean::cnstr_set(x_2081, 1, x_3);
x_2082 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2082, 0, x_2081);
return x_2082;
}
else
{
obj* x_2083; obj* x_2086; obj* x_2089; obj* x_2092; obj* x_2093; obj* x_2095; obj* x_2096; obj* x_2097; obj* x_2098; obj* x_2101; obj* x_2102; obj* x_2103; obj* x_2104; obj* x_2105; obj* x_2106; 
x_2083 = lean::cnstr_get(x_2077, 0);
lean::inc(x_2083);
lean::dec(x_2077);
x_2086 = lean::cnstr_get(x_2, 0);
lean::inc(x_2086);
lean::dec(x_2);
x_2089 = lean::cnstr_get(x_2086, 2);
lean::inc(x_2089);
lean::dec(x_2086);
x_2092 = l_Lean_FileMap_toPosition(x_2089, x_2083);
x_2093 = lean::cnstr_get(x_2092, 1);
lean::inc(x_2093);
x_2095 = lean::box(0);
x_2096 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2097 = l_Lean_KVMap_setNat(x_2095, x_2096, x_2093);
x_2098 = lean::cnstr_get(x_2092, 0);
lean::inc(x_2098);
lean::dec(x_2092);
x_2101 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2102 = l_Lean_KVMap_setNat(x_2097, x_2101, x_2098);
x_2103 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_2104 = lean_expr_mk_mdata(x_2102, x_2103);
x_2105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2105, 0, x_2104);
lean::cnstr_set(x_2105, 1, x_3);
x_2106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2106, 0, x_2105);
return x_2106;
}
}
else
{
obj* x_2109; obj* x_2110; obj* x_2111; 
lean::dec(x_0);
lean::dec(x_2);
x_2109 = l_Lean_Elaborator_toPexpr___main___closed__44;
x_2110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2110, 0, x_2109);
lean::cnstr_set(x_2110, 1, x_3);
x_2111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2111, 0, x_2110);
return x_2111;
}
}
}
}
else
{
obj* x_2113; obj* x_2114; obj* x_2118; obj* x_2119; 
lean::dec(x_10);
x_2113 = l_Lean_Parser_Term_pi_HasView;
x_2114 = lean::cnstr_get(x_2113, 0);
lean::inc(x_2114);
lean::dec(x_2113);
lean::inc(x_0);
x_2118 = lean::apply_1(x_2114, x_0);
x_2119 = lean::cnstr_get(x_2118, 1);
lean::inc(x_2119);
if (lean::obj_tag(x_2119) == 0)
{
obj* x_2124; obj* x_2125; obj* x_2127; 
lean::dec(x_2118);
lean::dec(x_2119);
lean::inc(x_0);
x_2124 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2124, 0, x_0);
x_2125 = l_Lean_Elaborator_toPexpr___main___closed__45;
lean::inc(x_2);
x_2127 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2124, x_2125, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2124);
if (lean::obj_tag(x_2127) == 0)
{
obj* x_2133; obj* x_2135; obj* x_2136; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2133 = lean::cnstr_get(x_2127, 0);
if (lean::is_exclusive(x_2127)) {
 x_2135 = x_2127;
} else {
 lean::inc(x_2133);
 lean::dec(x_2127);
 x_2135 = lean::box(0);
}
if (lean::is_scalar(x_2135)) {
 x_2136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2136 = x_2135;
}
lean::cnstr_set(x_2136, 0, x_2133);
return x_2136;
}
else
{
obj* x_2137; 
x_2137 = lean::cnstr_get(x_2127, 0);
lean::inc(x_2137);
lean::dec(x_2127);
x_15 = x_2137;
goto lbl_16;
}
}
else
{
obj* x_2140; obj* x_2143; obj* x_2144; obj* x_2146; obj* x_2149; obj* x_2151; obj* x_2155; 
x_2140 = lean::cnstr_get(x_2119, 0);
lean::inc(x_2140);
lean::dec(x_2119);
x_2143 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2140);
x_2144 = lean::cnstr_get(x_2143, 1);
lean::inc(x_2144);
x_2146 = lean::cnstr_get(x_2143, 0);
lean::inc(x_2146);
lean::dec(x_2143);
x_2149 = lean::cnstr_get(x_2144, 0);
lean::inc(x_2149);
x_2151 = lean::cnstr_get(x_2144, 1);
lean::inc(x_2151);
lean::dec(x_2144);
lean::inc(x_2);
x_2155 = l_Lean_Elaborator_toPexpr___main(x_2151, x_1, x_2, x_3);
if (lean::obj_tag(x_2155) == 0)
{
obj* x_2162; obj* x_2164; obj* x_2165; 
lean::dec(x_2146);
lean::dec(x_2149);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2118);
x_2162 = lean::cnstr_get(x_2155, 0);
if (lean::is_exclusive(x_2155)) {
 x_2164 = x_2155;
} else {
 lean::inc(x_2162);
 lean::dec(x_2155);
 x_2164 = lean::box(0);
}
if (lean::is_scalar(x_2164)) {
 x_2165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2165 = x_2164;
}
lean::cnstr_set(x_2165, 0, x_2162);
return x_2165;
}
else
{
obj* x_2166; obj* x_2169; obj* x_2171; obj* x_2174; obj* x_2178; 
x_2166 = lean::cnstr_get(x_2155, 0);
lean::inc(x_2166);
lean::dec(x_2155);
x_2169 = lean::cnstr_get(x_2166, 0);
lean::inc(x_2169);
x_2171 = lean::cnstr_get(x_2166, 1);
lean::inc(x_2171);
lean::dec(x_2166);
x_2174 = lean::cnstr_get(x_2118, 3);
lean::inc(x_2174);
lean::dec(x_2118);
lean::inc(x_2);
x_2178 = l_Lean_Elaborator_toPexpr___main(x_2174, x_1, x_2, x_2171);
if (lean::obj_tag(x_2178) == 0)
{
obj* x_2185; obj* x_2187; obj* x_2188; 
lean::dec(x_2169);
lean::dec(x_2146);
lean::dec(x_2149);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2185 = lean::cnstr_get(x_2178, 0);
if (lean::is_exclusive(x_2178)) {
 x_2187 = x_2178;
} else {
 lean::inc(x_2185);
 lean::dec(x_2178);
 x_2187 = lean::box(0);
}
if (lean::is_scalar(x_2187)) {
 x_2188 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2188 = x_2187;
}
lean::cnstr_set(x_2188, 0, x_2185);
return x_2188;
}
else
{
obj* x_2189; obj* x_2192; obj* x_2194; obj* x_2196; obj* x_2197; uint8 x_2198; obj* x_2199; obj* x_2200; 
x_2189 = lean::cnstr_get(x_2178, 0);
lean::inc(x_2189);
lean::dec(x_2178);
x_2192 = lean::cnstr_get(x_2189, 0);
x_2194 = lean::cnstr_get(x_2189, 1);
if (lean::is_exclusive(x_2189)) {
 x_2196 = x_2189;
} else {
 lean::inc(x_2192);
 lean::inc(x_2194);
 lean::dec(x_2189);
 x_2196 = lean::box(0);
}
x_2197 = l_Lean_Elaborator_mangleIdent(x_2149);
x_2198 = lean::unbox(x_2146);
x_2199 = lean_expr_mk_pi(x_2197, x_2198, x_2169, x_2192);
if (lean::is_scalar(x_2196)) {
 x_2200 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2200 = x_2196;
}
lean::cnstr_set(x_2200, 0, x_2199);
lean::cnstr_set(x_2200, 1, x_2194);
x_15 = x_2200;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2202; obj* x_2203; obj* x_2207; obj* x_2208; 
lean::dec(x_10);
x_2202 = l_Lean_Parser_Term_lambda_HasView;
x_2203 = lean::cnstr_get(x_2202, 0);
lean::inc(x_2203);
lean::dec(x_2202);
lean::inc(x_0);
x_2207 = lean::apply_1(x_2203, x_0);
x_2208 = lean::cnstr_get(x_2207, 1);
lean::inc(x_2208);
if (lean::obj_tag(x_2208) == 0)
{
obj* x_2213; obj* x_2214; obj* x_2216; 
lean::dec(x_2208);
lean::dec(x_2207);
lean::inc(x_0);
x_2213 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2213, 0, x_0);
x_2214 = l_Lean_Elaborator_toPexpr___main___closed__46;
lean::inc(x_2);
x_2216 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2213, x_2214, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2213);
if (lean::obj_tag(x_2216) == 0)
{
obj* x_2222; obj* x_2224; obj* x_2225; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2222 = lean::cnstr_get(x_2216, 0);
if (lean::is_exclusive(x_2216)) {
 x_2224 = x_2216;
} else {
 lean::inc(x_2222);
 lean::dec(x_2216);
 x_2224 = lean::box(0);
}
if (lean::is_scalar(x_2224)) {
 x_2225 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2225 = x_2224;
}
lean::cnstr_set(x_2225, 0, x_2222);
return x_2225;
}
else
{
obj* x_2226; 
x_2226 = lean::cnstr_get(x_2216, 0);
lean::inc(x_2226);
lean::dec(x_2216);
x_15 = x_2226;
goto lbl_16;
}
}
else
{
obj* x_2229; obj* x_2232; obj* x_2233; obj* x_2235; obj* x_2238; obj* x_2240; obj* x_2244; 
x_2229 = lean::cnstr_get(x_2208, 0);
lean::inc(x_2229);
lean::dec(x_2208);
x_2232 = l_Lean_Parser_Term_simpleBinder_View_toBinderInfo___main(x_2229);
x_2233 = lean::cnstr_get(x_2232, 1);
lean::inc(x_2233);
x_2235 = lean::cnstr_get(x_2232, 0);
lean::inc(x_2235);
lean::dec(x_2232);
x_2238 = lean::cnstr_get(x_2233, 0);
lean::inc(x_2238);
x_2240 = lean::cnstr_get(x_2233, 1);
lean::inc(x_2240);
lean::dec(x_2233);
lean::inc(x_2);
x_2244 = l_Lean_Elaborator_toPexpr___main(x_2240, x_1, x_2, x_3);
if (lean::obj_tag(x_2244) == 0)
{
obj* x_2251; obj* x_2253; obj* x_2254; 
lean::dec(x_8);
lean::dec(x_2235);
lean::dec(x_0);
lean::dec(x_2238);
lean::dec(x_2);
lean::dec(x_2207);
x_2251 = lean::cnstr_get(x_2244, 0);
if (lean::is_exclusive(x_2244)) {
 x_2253 = x_2244;
} else {
 lean::inc(x_2251);
 lean::dec(x_2244);
 x_2253 = lean::box(0);
}
if (lean::is_scalar(x_2253)) {
 x_2254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2254 = x_2253;
}
lean::cnstr_set(x_2254, 0, x_2251);
return x_2254;
}
else
{
obj* x_2255; obj* x_2258; obj* x_2260; obj* x_2263; obj* x_2267; 
x_2255 = lean::cnstr_get(x_2244, 0);
lean::inc(x_2255);
lean::dec(x_2244);
x_2258 = lean::cnstr_get(x_2255, 0);
lean::inc(x_2258);
x_2260 = lean::cnstr_get(x_2255, 1);
lean::inc(x_2260);
lean::dec(x_2255);
x_2263 = lean::cnstr_get(x_2207, 3);
lean::inc(x_2263);
lean::dec(x_2207);
lean::inc(x_2);
x_2267 = l_Lean_Elaborator_toPexpr___main(x_2263, x_1, x_2, x_2260);
if (lean::obj_tag(x_2267) == 0)
{
obj* x_2274; obj* x_2276; obj* x_2277; 
lean::dec(x_8);
lean::dec(x_2235);
lean::dec(x_0);
lean::dec(x_2238);
lean::dec(x_2);
lean::dec(x_2258);
x_2274 = lean::cnstr_get(x_2267, 0);
if (lean::is_exclusive(x_2267)) {
 x_2276 = x_2267;
} else {
 lean::inc(x_2274);
 lean::dec(x_2267);
 x_2276 = lean::box(0);
}
if (lean::is_scalar(x_2276)) {
 x_2277 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2277 = x_2276;
}
lean::cnstr_set(x_2277, 0, x_2274);
return x_2277;
}
else
{
obj* x_2278; obj* x_2281; obj* x_2283; obj* x_2285; obj* x_2286; uint8 x_2287; obj* x_2288; obj* x_2289; 
x_2278 = lean::cnstr_get(x_2267, 0);
lean::inc(x_2278);
lean::dec(x_2267);
x_2281 = lean::cnstr_get(x_2278, 0);
x_2283 = lean::cnstr_get(x_2278, 1);
if (lean::is_exclusive(x_2278)) {
 x_2285 = x_2278;
} else {
 lean::inc(x_2281);
 lean::inc(x_2283);
 lean::dec(x_2278);
 x_2285 = lean::box(0);
}
x_2286 = l_Lean_Elaborator_mangleIdent(x_2238);
x_2287 = lean::unbox(x_2235);
x_2288 = lean_expr_mk_lambda(x_2286, x_2287, x_2258, x_2281);
if (lean::is_scalar(x_2285)) {
 x_2289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2289 = x_2285;
}
lean::cnstr_set(x_2289, 0, x_2288);
lean::cnstr_set(x_2289, 1, x_2283);
x_15 = x_2289;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_2292; obj* x_2293; obj* x_2297; obj* x_2298; obj* x_2301; 
lean::dec(x_8);
lean::dec(x_10);
x_2292 = l_Lean_Parser_Term_app_HasView;
x_2293 = lean::cnstr_get(x_2292, 0);
lean::inc(x_2293);
lean::dec(x_2292);
lean::inc(x_0);
x_2297 = lean::apply_1(x_2293, x_0);
x_2298 = lean::cnstr_get(x_2297, 0);
lean::inc(x_2298);
lean::inc(x_2);
x_2301 = l_Lean_Elaborator_toPexpr___main(x_2298, x_1, x_2, x_3);
if (lean::obj_tag(x_2301) == 0)
{
obj* x_2305; obj* x_2307; obj* x_2308; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2297);
x_2305 = lean::cnstr_get(x_2301, 0);
if (lean::is_exclusive(x_2301)) {
 x_2307 = x_2301;
} else {
 lean::inc(x_2305);
 lean::dec(x_2301);
 x_2307 = lean::box(0);
}
if (lean::is_scalar(x_2307)) {
 x_2308 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2308 = x_2307;
}
lean::cnstr_set(x_2308, 0, x_2305);
return x_2308;
}
else
{
obj* x_2309; obj* x_2312; obj* x_2314; obj* x_2317; obj* x_2321; 
x_2309 = lean::cnstr_get(x_2301, 0);
lean::inc(x_2309);
lean::dec(x_2301);
x_2312 = lean::cnstr_get(x_2309, 0);
lean::inc(x_2312);
x_2314 = lean::cnstr_get(x_2309, 1);
lean::inc(x_2314);
lean::dec(x_2309);
x_2317 = lean::cnstr_get(x_2297, 1);
lean::inc(x_2317);
lean::dec(x_2297);
lean::inc(x_2);
x_2321 = l_Lean_Elaborator_toPexpr___main(x_2317, x_1, x_2, x_2314);
if (lean::obj_tag(x_2321) == 0)
{
obj* x_2325; obj* x_2327; obj* x_2328; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_2312);
x_2325 = lean::cnstr_get(x_2321, 0);
if (lean::is_exclusive(x_2321)) {
 x_2327 = x_2321;
} else {
 lean::inc(x_2325);
 lean::dec(x_2321);
 x_2327 = lean::box(0);
}
if (lean::is_scalar(x_2327)) {
 x_2328 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2328 = x_2327;
}
lean::cnstr_set(x_2328, 0, x_2325);
return x_2328;
}
else
{
obj* x_2329; obj* x_2331; obj* x_2332; obj* x_2334; obj* x_2336; obj* x_2337; 
x_2329 = lean::cnstr_get(x_2321, 0);
if (lean::is_exclusive(x_2321)) {
 lean::cnstr_set(x_2321, 0, lean::box(0));
 x_2331 = x_2321;
} else {
 lean::inc(x_2329);
 lean::dec(x_2321);
 x_2331 = lean::box(0);
}
x_2332 = lean::cnstr_get(x_2329, 0);
x_2334 = lean::cnstr_get(x_2329, 1);
if (lean::is_exclusive(x_2329)) {
 lean::cnstr_set(x_2329, 0, lean::box(0));
 lean::cnstr_set(x_2329, 1, lean::box(0));
 x_2336 = x_2329;
} else {
 lean::inc(x_2332);
 lean::inc(x_2334);
 lean::dec(x_2329);
 x_2336 = lean::box(0);
}
x_2337 = lean_expr_mk_app(x_2312, x_2332);
if (x_20 == 0)
{
obj* x_2338; 
x_2338 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2338) == 0)
{
obj* x_2341; obj* x_2342; 
lean::dec(x_2);
if (lean::is_scalar(x_2336)) {
 x_2341 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2341 = x_2336;
}
lean::cnstr_set(x_2341, 0, x_2337);
lean::cnstr_set(x_2341, 1, x_2334);
if (lean::is_scalar(x_2331)) {
 x_2342 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2342 = x_2331;
}
lean::cnstr_set(x_2342, 0, x_2341);
return x_2342;
}
else
{
obj* x_2343; obj* x_2346; obj* x_2349; obj* x_2352; obj* x_2353; obj* x_2355; obj* x_2356; obj* x_2357; obj* x_2358; obj* x_2361; obj* x_2362; obj* x_2363; obj* x_2364; obj* x_2365; 
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
x_2355 = lean::box(0);
x_2356 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2357 = l_Lean_KVMap_setNat(x_2355, x_2356, x_2353);
x_2358 = lean::cnstr_get(x_2352, 0);
lean::inc(x_2358);
lean::dec(x_2352);
x_2361 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2362 = l_Lean_KVMap_setNat(x_2357, x_2361, x_2358);
x_2363 = lean_expr_mk_mdata(x_2362, x_2337);
if (lean::is_scalar(x_2336)) {
 x_2364 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2364 = x_2336;
}
lean::cnstr_set(x_2364, 0, x_2363);
lean::cnstr_set(x_2364, 1, x_2334);
if (lean::is_scalar(x_2331)) {
 x_2365 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2365 = x_2331;
}
lean::cnstr_set(x_2365, 0, x_2364);
return x_2365;
}
}
else
{
obj* x_2368; obj* x_2369; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2336)) {
 x_2368 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2368 = x_2336;
}
lean::cnstr_set(x_2368, 0, x_2337);
lean::cnstr_set(x_2368, 1, x_2334);
if (lean::is_scalar(x_2331)) {
 x_2369 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2369 = x_2331;
}
lean::cnstr_set(x_2369, 0, x_2368);
return x_2369;
}
}
}
}
}
else
{
obj* x_2371; obj* x_2372; obj* x_2376; obj* x_2377; 
lean::dec(x_10);
x_2371 = l_Lean_Parser_identUnivs_HasView;
x_2372 = lean::cnstr_get(x_2371, 0);
lean::inc(x_2372);
lean::dec(x_2371);
lean::inc(x_0);
x_2376 = lean::apply_1(x_2372, x_0);
x_2377 = lean::cnstr_get(x_2376, 1);
lean::inc(x_2377);
if (lean::obj_tag(x_2377) == 0)
{
obj* x_2379; obj* x_2383; obj* x_2384; obj* x_2385; obj* x_2386; obj* x_2389; obj* x_2390; obj* x_2391; obj* x_2392; obj* x_2393; obj* x_2394; uint8 x_2395; 
x_2379 = lean::cnstr_get(x_2376, 0);
lean::inc(x_2379);
lean::dec(x_2376);
lean::inc(x_2379);
x_2383 = l_Lean_Elaborator_mangleIdent(x_2379);
x_2384 = lean::box(0);
x_2385 = lean_expr_mk_const(x_2383, x_2384);
x_2386 = lean::cnstr_get(x_2379, 3);
lean::inc(x_2386);
lean::dec(x_2379);
x_2389 = lean::mk_nat_obj(0ul);
x_2390 = l_List_enumFrom___main___rarg(x_2389, x_2386);
x_2391 = l_Lean_Elaborator_toPexpr___main___closed__47;
x_2392 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__20(x_2391, x_2390);
x_2393 = lean_expr_mk_mdata(x_2392, x_2385);
x_2394 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2395 = lean_name_dec_eq(x_8, x_2394);
lean::dec(x_8);
if (x_2395 == 0)
{
obj* x_2397; 
x_2397 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2397) == 0)
{
obj* x_2400; obj* x_2401; 
lean::dec(x_2);
x_2400 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2400, 0, x_2393);
lean::cnstr_set(x_2400, 1, x_3);
x_2401 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2401, 0, x_2400);
return x_2401;
}
else
{
obj* x_2402; obj* x_2405; obj* x_2408; obj* x_2411; obj* x_2412; obj* x_2414; obj* x_2415; obj* x_2416; obj* x_2419; obj* x_2420; obj* x_2421; obj* x_2422; obj* x_2423; 
x_2402 = lean::cnstr_get(x_2397, 0);
lean::inc(x_2402);
lean::dec(x_2397);
x_2405 = lean::cnstr_get(x_2, 0);
lean::inc(x_2405);
lean::dec(x_2);
x_2408 = lean::cnstr_get(x_2405, 2);
lean::inc(x_2408);
lean::dec(x_2405);
x_2411 = l_Lean_FileMap_toPosition(x_2408, x_2402);
x_2412 = lean::cnstr_get(x_2411, 1);
lean::inc(x_2412);
x_2414 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2415 = l_Lean_KVMap_setNat(x_2384, x_2414, x_2412);
x_2416 = lean::cnstr_get(x_2411, 0);
lean::inc(x_2416);
lean::dec(x_2411);
x_2419 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2420 = l_Lean_KVMap_setNat(x_2415, x_2419, x_2416);
x_2421 = lean_expr_mk_mdata(x_2420, x_2393);
x_2422 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2422, 0, x_2421);
lean::cnstr_set(x_2422, 1, x_3);
x_2423 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2423, 0, x_2422);
return x_2423;
}
}
else
{
obj* x_2426; obj* x_2427; 
lean::dec(x_0);
lean::dec(x_2);
x_2426 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2426, 0, x_2393);
lean::cnstr_set(x_2426, 1, x_3);
x_2427 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2427, 0, x_2426);
return x_2427;
}
}
else
{
obj* x_2428; obj* x_2431; obj* x_2434; obj* x_2438; 
x_2428 = lean::cnstr_get(x_2376, 0);
lean::inc(x_2428);
lean::dec(x_2376);
x_2431 = lean::cnstr_get(x_2377, 0);
lean::inc(x_2431);
lean::dec(x_2377);
x_2434 = lean::cnstr_get(x_2431, 1);
lean::inc(x_2434);
lean::dec(x_2431);
lean::inc(x_2);
x_2438 = l_List_mmap___main___at_Lean_Elaborator_toPexpr___main___spec__21(x_2434, x_1, x_2, x_3);
if (lean::obj_tag(x_2438) == 0)
{
obj* x_2443; obj* x_2445; obj* x_2446; 
lean::dec(x_2428);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2443 = lean::cnstr_get(x_2438, 0);
if (lean::is_exclusive(x_2438)) {
 x_2445 = x_2438;
} else {
 lean::inc(x_2443);
 lean::dec(x_2438);
 x_2445 = lean::box(0);
}
if (lean::is_scalar(x_2445)) {
 x_2446 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2446 = x_2445;
}
lean::cnstr_set(x_2446, 0, x_2443);
return x_2446;
}
else
{
obj* x_2447; obj* x_2449; obj* x_2450; obj* x_2452; obj* x_2454; obj* x_2456; obj* x_2457; obj* x_2458; obj* x_2461; obj* x_2462; obj* x_2463; obj* x_2464; obj* x_2465; obj* x_2466; uint8 x_2467; 
x_2447 = lean::cnstr_get(x_2438, 0);
if (lean::is_exclusive(x_2438)) {
 lean::cnstr_set(x_2438, 0, lean::box(0));
 x_2449 = x_2438;
} else {
 lean::inc(x_2447);
 lean::dec(x_2438);
 x_2449 = lean::box(0);
}
x_2450 = lean::cnstr_get(x_2447, 0);
x_2452 = lean::cnstr_get(x_2447, 1);
if (lean::is_exclusive(x_2447)) {
 lean::cnstr_set(x_2447, 0, lean::box(0));
 lean::cnstr_set(x_2447, 1, lean::box(0));
 x_2454 = x_2447;
} else {
 lean::inc(x_2450);
 lean::inc(x_2452);
 lean::dec(x_2447);
 x_2454 = lean::box(0);
}
lean::inc(x_2428);
x_2456 = l_Lean_Elaborator_mangleIdent(x_2428);
x_2457 = lean_expr_mk_const(x_2456, x_2450);
x_2458 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2458);
lean::dec(x_2428);
x_2461 = lean::mk_nat_obj(0ul);
x_2462 = l_List_enumFrom___main___rarg(x_2461, x_2458);
x_2463 = l_Lean_Elaborator_toPexpr___main___closed__48;
x_2464 = l_List_foldl___main___at_Lean_Elaborator_toPexpr___main___spec__22(x_2463, x_2462);
x_2465 = lean_expr_mk_mdata(x_2464, x_2457);
x_2466 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2467 = lean_name_dec_eq(x_8, x_2466);
lean::dec(x_8);
if (x_2467 == 0)
{
obj* x_2469; obj* x_2470; 
x_2469 = lean::box(0);
x_2470 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2470) == 0)
{
obj* x_2473; obj* x_2474; 
lean::dec(x_2);
if (lean::is_scalar(x_2454)) {
 x_2473 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2473 = x_2454;
}
lean::cnstr_set(x_2473, 0, x_2465);
lean::cnstr_set(x_2473, 1, x_2452);
if (lean::is_scalar(x_2449)) {
 x_2474 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2474 = x_2449;
}
lean::cnstr_set(x_2474, 0, x_2473);
return x_2474;
}
else
{
obj* x_2475; obj* x_2478; obj* x_2481; obj* x_2484; obj* x_2485; obj* x_2487; obj* x_2488; obj* x_2489; obj* x_2492; obj* x_2493; obj* x_2494; obj* x_2495; obj* x_2496; 
x_2475 = lean::cnstr_get(x_2470, 0);
lean::inc(x_2475);
lean::dec(x_2470);
x_2478 = lean::cnstr_get(x_2, 0);
lean::inc(x_2478);
lean::dec(x_2);
x_2481 = lean::cnstr_get(x_2478, 2);
lean::inc(x_2481);
lean::dec(x_2478);
x_2484 = l_Lean_FileMap_toPosition(x_2481, x_2475);
x_2485 = lean::cnstr_get(x_2484, 1);
lean::inc(x_2485);
x_2487 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2488 = l_Lean_KVMap_setNat(x_2469, x_2487, x_2485);
x_2489 = lean::cnstr_get(x_2484, 0);
lean::inc(x_2489);
lean::dec(x_2484);
x_2492 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2493 = l_Lean_KVMap_setNat(x_2488, x_2492, x_2489);
x_2494 = lean_expr_mk_mdata(x_2493, x_2465);
if (lean::is_scalar(x_2454)) {
 x_2495 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2495 = x_2454;
}
lean::cnstr_set(x_2495, 0, x_2494);
lean::cnstr_set(x_2495, 1, x_2452);
if (lean::is_scalar(x_2449)) {
 x_2496 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2496 = x_2449;
}
lean::cnstr_set(x_2496, 0, x_2495);
return x_2496;
}
}
else
{
obj* x_2499; obj* x_2500; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2454)) {
 x_2499 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2499 = x_2454;
}
lean::cnstr_set(x_2499, 0, x_2465);
lean::cnstr_set(x_2499, 1, x_2452);
if (lean::is_scalar(x_2449)) {
 x_2500 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2500 = x_2449;
}
lean::cnstr_set(x_2500, 0, x_2499);
return x_2500;
}
}
}
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_2504; obj* x_2506; obj* x_2507; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
x_2504 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_2506 = x_13;
} else {
 lean::inc(x_2504);
 lean::dec(x_13);
 x_2506 = lean::box(0);
}
if (lean::is_scalar(x_2506)) {
 x_2507 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_2507 = x_2506;
}
lean::cnstr_set(x_2507, 0, x_2504);
return x_2507;
}
else
{
obj* x_2508; obj* x_2510; obj* x_2511; obj* x_2513; obj* x_2515; obj* x_2516; uint8 x_2517; 
x_2508 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_2510 = x_13;
} else {
 lean::inc(x_2508);
 lean::dec(x_13);
 x_2510 = lean::box(0);
}
x_2511 = lean::cnstr_get(x_2508, 0);
x_2513 = lean::cnstr_get(x_2508, 1);
if (lean::is_exclusive(x_2508)) {
 lean::cnstr_set(x_2508, 0, lean::box(0));
 lean::cnstr_set(x_2508, 1, lean::box(0));
 x_2515 = x_2508;
} else {
 lean::inc(x_2511);
 lean::inc(x_2513);
 lean::dec(x_2508);
 x_2515 = lean::box(0);
}
x_2516 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2517 = lean_name_dec_eq(x_8, x_2516);
lean::dec(x_8);
if (x_2517 == 0)
{
obj* x_2519; 
x_2519 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2519) == 0)
{
obj* x_2522; obj* x_2523; 
lean::dec(x_2);
if (lean::is_scalar(x_2515)) {
 x_2522 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2522 = x_2515;
}
lean::cnstr_set(x_2522, 0, x_2511);
lean::cnstr_set(x_2522, 1, x_2513);
if (lean::is_scalar(x_2510)) {
 x_2523 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2523 = x_2510;
}
lean::cnstr_set(x_2523, 0, x_2522);
return x_2523;
}
else
{
obj* x_2524; obj* x_2527; obj* x_2530; obj* x_2533; obj* x_2534; obj* x_2536; obj* x_2537; obj* x_2538; obj* x_2539; obj* x_2542; obj* x_2543; obj* x_2544; obj* x_2545; obj* x_2546; 
x_2524 = lean::cnstr_get(x_2519, 0);
lean::inc(x_2524);
lean::dec(x_2519);
x_2527 = lean::cnstr_get(x_2, 0);
lean::inc(x_2527);
lean::dec(x_2);
x_2530 = lean::cnstr_get(x_2527, 2);
lean::inc(x_2530);
lean::dec(x_2527);
x_2533 = l_Lean_FileMap_toPosition(x_2530, x_2524);
x_2534 = lean::cnstr_get(x_2533, 1);
lean::inc(x_2534);
x_2536 = lean::box(0);
x_2537 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2538 = l_Lean_KVMap_setNat(x_2536, x_2537, x_2534);
x_2539 = lean::cnstr_get(x_2533, 0);
lean::inc(x_2539);
lean::dec(x_2533);
x_2542 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2543 = l_Lean_KVMap_setNat(x_2538, x_2542, x_2539);
x_2544 = lean_expr_mk_mdata(x_2543, x_2511);
if (lean::is_scalar(x_2515)) {
 x_2545 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2545 = x_2515;
}
lean::cnstr_set(x_2545, 0, x_2544);
lean::cnstr_set(x_2545, 1, x_2513);
if (lean::is_scalar(x_2510)) {
 x_2546 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2546 = x_2510;
}
lean::cnstr_set(x_2546, 0, x_2545);
return x_2546;
}
}
else
{
obj* x_2549; obj* x_2550; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2515)) {
 x_2549 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2549 = x_2515;
}
lean::cnstr_set(x_2549, 0, x_2511);
lean::cnstr_set(x_2549, 1, x_2513);
if (lean::is_scalar(x_2510)) {
 x_2550 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_2550 = x_2510;
}
lean::cnstr_set(x_2550, 0, x_2549);
return x_2550;
}
}
}
lbl_16:
{
obj* x_2551; obj* x_2553; obj* x_2555; obj* x_2556; uint8 x_2557; 
x_2551 = lean::cnstr_get(x_15, 0);
x_2553 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_2555 = x_15;
} else {
 lean::inc(x_2551);
 lean::inc(x_2553);
 lean::dec(x_15);
 x_2555 = lean::box(0);
}
x_2556 = l_Lean_Elaborator_toPexpr___main___closed__2;
x_2557 = lean_name_dec_eq(x_8, x_2556);
lean::dec(x_8);
if (x_2557 == 0)
{
obj* x_2559; 
x_2559 = l_Lean_Parser_Syntax_getPos(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_2559) == 0)
{
obj* x_2562; obj* x_2563; 
lean::dec(x_2);
if (lean::is_scalar(x_2555)) {
 x_2562 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2562 = x_2555;
}
lean::cnstr_set(x_2562, 0, x_2551);
lean::cnstr_set(x_2562, 1, x_2553);
x_2563 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2563, 0, x_2562);
return x_2563;
}
else
{
obj* x_2564; obj* x_2567; obj* x_2570; obj* x_2573; obj* x_2574; obj* x_2576; obj* x_2577; obj* x_2578; obj* x_2579; obj* x_2582; obj* x_2583; obj* x_2584; obj* x_2585; obj* x_2586; 
x_2564 = lean::cnstr_get(x_2559, 0);
lean::inc(x_2564);
lean::dec(x_2559);
x_2567 = lean::cnstr_get(x_2, 0);
lean::inc(x_2567);
lean::dec(x_2);
x_2570 = lean::cnstr_get(x_2567, 2);
lean::inc(x_2570);
lean::dec(x_2567);
x_2573 = l_Lean_FileMap_toPosition(x_2570, x_2564);
x_2574 = lean::cnstr_get(x_2573, 1);
lean::inc(x_2574);
x_2576 = lean::box(0);
x_2577 = l_Lean_Elaborator_toPexpr___main___closed__3;
x_2578 = l_Lean_KVMap_setNat(x_2576, x_2577, x_2574);
x_2579 = lean::cnstr_get(x_2573, 0);
lean::inc(x_2579);
lean::dec(x_2573);
x_2582 = l_Lean_Elaborator_toPexpr___main___closed__4;
x_2583 = l_Lean_KVMap_setNat(x_2578, x_2582, x_2579);
x_2584 = lean_expr_mk_mdata(x_2583, x_2551);
if (lean::is_scalar(x_2555)) {
 x_2585 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2585 = x_2555;
}
lean::cnstr_set(x_2585, 0, x_2584);
lean::cnstr_set(x_2585, 1, x_2553);
x_2586 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2586, 0, x_2585);
return x_2586;
}
}
else
{
obj* x_2589; obj* x_2590; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_2555)) {
 x_2589 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_2589 = x_2555;
}
lean::cnstr_set(x_2589, 0, x_2551);
lean::cnstr_set(x_2589, 1, x_2553);
x_2590 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2590, 0, x_2589);
return x_2590;
}
}
}
default:
{
obj* x_2591; 
x_2591 = lean::box(0);
x_4 = x_2591;
goto lbl_5;
}
}
lbl_5:
{
obj* x_2594; obj* x_2595; obj* x_2596; obj* x_2597; obj* x_2598; obj* x_2599; obj* x_2601; 
lean::dec(x_4);
lean::inc(x_0);
x_2594 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2594, 0, x_0);
x_2595 = l_Lean_Parser_Syntax_toFormat___main(x_0);
x_2596 = l_Lean_Options_empty;
x_2597 = l_Lean_Format_pretty(x_2595, x_2596);
x_2598 = l_Lean_Elaborator_toPexpr___main___closed__1;
x_2599 = lean::string_append(x_2598, x_2597);
lean::dec(x_2597);
x_2601 = l_Lean_Expander_error___at_Lean_Elaborator_currentScope___spec__1___rarg(x_2594, x_2599, x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2594);
return x_2601;
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
x_179 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__3___boxed), 13, 9);
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
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elaborator_Declaration_elaborate___lambda__5___boxed), 14, 10);
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
