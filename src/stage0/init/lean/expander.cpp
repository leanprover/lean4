// Lean compiler output
// Module: init.lean.expander
// Imports: init.lean.parser.module init.lean.expr
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
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mixfix_transform___closed__5;
obj* l_RBNode_setBlack___main___rarg(obj*);
extern obj* l_Lean_Parser_Term_arrow;
obj* l_Lean_Expander_getOptType___main(obj*);
obj* l_Lean_Expander_sorry_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_ExpanderState_new;
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1(obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_sorry_transform(obj*, obj*);
obj* l_Lean_Expander_getOptType___main___closed__1;
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_flipScopes___main(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__5;
obj* l_Lean_Expander_coeBinderBracketedBinder___closed__1;
obj* l_Lean_Expander_expandBracketedBinder___main(obj*, obj*);
obj* l_Lean_Expander_Declaration_transform___boxed(obj*, obj*);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(obj*, obj*);
extern obj* l_Lean_Parser_Term_hole_HasView;
obj* l_Lean_Expander_depArrow_transform(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___boxed(obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_binderDefault_HasView;
obj* l_Lean_Expander_assume_transform___closed__1;
extern obj* l_Lean_Parser_command_reserveMixfix;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(uint8, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
obj* l_Lean_Expander_mkSimpleBinder(obj*, uint8, obj*);
obj* l_Lean_Expander_mixfix_transform___closed__6;
obj* l_Lean_Expander_expandBracketedBinder___main___closed__5;
obj* l_Lean_Expander_binderIdentToIdent___boxed(obj*);
extern obj* l_Lean_Parser_Term_let;
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig(obj*);
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__7;
extern obj* l_Lean_Parser_Term_assume_HasView;
obj* l_Lean_Expander_assume_transform___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_mixfix;
obj* l_Lean_Expander_paren_transform(obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer___lambda__1(obj*, obj*);
obj* l_Lean_Expander_Declaration_transform___closed__1;
extern obj* l_Lean_Parser_command_reserveMixfix_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(uint8, obj*, obj*);
obj* l_Lean_Expander_let_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__1;
obj* l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___boxed(obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView;
obj* l_Lean_Expander_coeBinderBracketedBinder(obj*);
obj* l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Expander_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__2(obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(obj*, obj*);
extern obj* l_Lean_Parser_command_variables;
obj* l_Lean_Expander_arrow_transform(obj*, obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig___boxed(obj*);
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_Parser_TermParserM_Alternative;
obj* l_Lean_Expander_mkSimpleBinder___closed__2;
obj* l_Lean_Expander_if_transform___boxed(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_expander_2__expandCore___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_expandBracketedBinder___main___closed__2;
obj* l_Lean_Expander_depArrow_transform___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_expander_2__expandCore___main___closed__1;
obj* l_Lean_Expander_mkSimpleBinder___closed__5;
obj* l_Lean_Expander_Level_leading_transform(obj*, obj*);
obj* l_Lean_Expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_Lean_Expander_TransformM_Monad;
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1(obj*);
extern obj* l_Lean_Parser_Term_bracketedBinders;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(uint8, obj*, obj*);
obj* l___private_init_lean_expander_1__popStxArg(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(obj*, obj*, obj*);
obj* l_Lean_Expander_variable_transform___closed__1;
obj* l_ExceptT_MonadExcept___rarg(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(uint8, obj*, obj*);
extern obj* l_Lean_Parser_command_mixfix_HasView;
obj* l_Lean_Expander_axiom_transform___closed__1;
obj* l_Lean_Expander_expandBracketedBinder___main___closed__3;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_reserveNotation_HasView;
extern obj* l_Id_Monad;
obj* l_Lean_Expander_coeSimpleBinderBinders(obj*);
extern obj* l_Lean_Parser_command_axiom_HasView;
obj* l_Lean_Expander_paren_transform___closed__1;
obj* l_Lean_Expander_TransformM_MonadReader;
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
obj* l_Lean_Expander_mixfixToNotationSpec___closed__6;
obj* l_coe___at_Lean_Expander_depArrow_transform___spec__1(obj*);
obj* l_Lean_Expander_error___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l___private_init_lean_expander_2__expandCore(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(obj*);
extern obj* l_Lean_Parser_Term_depArrow;
extern obj* l_Lean_Parser_command_introRule_HasView;
extern obj* l_Lean_Parser_command_universes_HasView;
obj* l_Lean_Expander_coeBracketedBinderMixedBinder(obj*);
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_variable_HasView;
obj* l_Lean_Expander_coeNameIdent(obj*);
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2(obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Expander_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_coeIdentsBindersExt___rarg(obj*, obj*);
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
obj* l_List_join___main___rarg(obj*);
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(obj*);
obj* l_Lean_Expander_binderIdentToIdent___main___closed__1;
extern obj* l_Lean_Parser_command_axiom;
obj* l_Lean_Expander_mkScope(obj*, obj*);
obj* l_Lean_Expander_Level_leading_transform___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(obj*, obj*);
obj* l_Lean_Expander_coeMixedBindersBindersExt(obj*);
extern obj* l_Lean_Parser_Term_if;
obj* l_Lean_Expander_lambda_transform___closed__1;
obj* l_Lean_Expander_assume_transform(obj*, obj*);
obj* l_Lean_Expander_reserveMixfix_transform___closed__1;
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___boxed(obj*);
extern obj* l_Lean_Parser_command_universes;
obj* l_Lean_Expander_error(obj*, obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Expander_getOptType___boxed(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(obj*, obj*);
obj* l_Lean_Expander_universes_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_let_transform(obj*, obj*);
obj* l_Lean_Expander_expandBinders(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(obj*);
obj* l_Lean_Expander_variable_transform(obj*, obj*);
obj* l_Lean_Expander_mixfix_transform___closed__1;
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_introRule_transform(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(uint8, obj*, obj*);
extern obj* l_Lean_Parser_Term_depArrow_HasView;
obj* l_Lean_Expander_Subtype_transform(obj*, obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
obj* l_Lean_Expander_builtinTransformers;
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1(obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__2;
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
extern obj* l_Lean_Parser_noKind;
extern obj* l_Lean_Parser_Term_lambda_HasView;
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
extern obj* l_Lean_Parser_Term_paren;
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2(obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_Subtype_transform___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
extern obj* l_Lean_Parser_Term_binderIdent_HasView;
obj* l_Lean_Expander_mkNotationTransformer(obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_arrow_transform___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Expander_mkSimpleBinder___closed__1;
obj* l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__2(obj*, obj*);
obj* l_Lean_Expander_pi_transform(obj*, obj*);
extern obj* l_Lean_Parser_Term_sorry;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Expander_coeIdentBinderId(obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_Subtype;
obj* l_Lean_Expander_binderIdentToIdent___main___boxed(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(uint8, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_mkSimpleBinder___closed__6;
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_identUnivs;
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7___boxed(obj*, obj*);
obj* l_Lean_Expander_ExpanderConfig_HasLift___boxed(obj*);
extern obj* l_Lean_Parser_command_Declaration;
extern obj* l_Lean_Parser_Term_Subtype_HasView;
obj* l_Lean_Expander_ExpanderConfig_HasLift(obj*);
obj* l_Lean_Expander_globId(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_variable;
obj* l_Lean_Expander_expandBracketedBinder___main___closed__4;
obj* l_Lean_Expander_if_transform___closed__2;
obj* l_Lean_Expander_expandBracketedBinder___main___closed__1;
extern obj* l_Lean_Parser_Level_leading;
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___boxed(obj*);
extern obj* l_Lean_Parser_command_notation_HasView;
obj* l_Lean_Expander_axiom_transform(obj*, obj*);
extern obj* l_Lean_Parser_Term_app_HasView;
obj* l_Lean_Expander_mixfix_transform___closed__3;
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_expander_1__popStxArg___closed__1;
extern obj* l_Lean_Parser_Term_assume;
obj* l_Lean_Expander_coeIdentIdentUnivs(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_noExpansion___boxed(obj*);
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkScope___boxed(obj*, obj*);
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___rarg(obj*, obj*);
obj* l_Lean_Expander_paren_transform___closed__2;
obj* l_Lean_Expander_binderIdentToIdent(obj*);
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkSimpleBinder___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_if_transform___closed__1;
obj* l_String_trim(obj*);
obj* l_Lean_Expander_arrow_transform___closed__1;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate;
obj* l_Lean_Expander_lambda_transform(obj*, obj*);
obj* l_Lean_Expander_coeBindersExtBinders(obj*);
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___boxed(obj*);
obj* l_Lean_Expander_universes_transform(obj*, obj*);
obj* l_Lean_Expander_getOptType___main___boxed(obj*);
obj* l_Lean_Expander_coeBinderBracketedBinder___closed__2;
obj* l_Lean_Expander_getOptType(obj*);
extern obj* l_Lean_Parser_TermParserM_Monad;
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Expander_sorry_transform___closed__1;
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_bracketedBinders_HasView;
extern obj* l_Lean_Parser_command_universe_HasView;
obj* l_Lean_Expander_if_transform___closed__3;
obj* l_Lean_Expander_reserveMixfix_transform(obj*, obj*);
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1(obj*);
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Term_anonymousConstructor_HasView;
obj* l_Lean_Expander_TransformM_MonadExcept;
obj* l_Lean_Expander_let_transform___closed__1;
obj* l_Lean_Expander_Declaration_transform___closed__2;
obj* l_Lean_Expander_mkSimpleBinder___closed__3;
obj* l_Lean_Expander_introRule_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1(obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(uint8, obj*, obj*);
obj* l_Lean_Expander_depArrow_transform___closed__1;
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
obj* l_Lean_Expander_pi_transform___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Expander_Subtype_transform___boxed(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3___boxed(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(obj*, obj*);
obj* l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(obj*, obj*);
extern obj* l_Lean_Parser_Term_arrow_HasView;
obj* l_Lean_Expander_mkSimpleBinder___closed__7;
obj* l_ExceptT_Monad___rarg(obj*);
obj* l_Lean_Expander_variables_transform(obj*, obj*);
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(obj*, obj*);
extern obj* l_Lean_Parser_Term_paren_HasView;
extern obj* l_Lean_Parser_Term_lambda;
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_mixfix_transform___closed__2;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView;
obj* l_Lean_Expander_paren_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_expandBracketedBinder___main___closed__6;
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___boxed(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(obj*, obj*);
obj* l_Lean_Expander_variable_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_axiom_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_coeIdentsBindersExt___boxed(obj*);
obj* l_Lean_Expander_Declaration_transform(obj*, obj*);
obj* l_Lean_Expander_coeMixedBindersBindersExt___rarg(obj*, obj*);
obj* l_Lean_Expander_Declaration_transform___closed__3;
obj* l_Lean_Expander_mixfix_transform(obj*, obj*);
extern obj* l_Lean_Parser_Term_pi;
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1;
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___rarg(obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_Lean_Expander_error___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(obj*);
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__4;
obj* l_List_map___main___at_Lean_Expander_universes_transform___spec__1(obj*);
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27;
extern obj* l_Lean_Parser_TermParserM_MonadExcept;
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1;
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(obj*, obj*);
extern obj* l_Lean_Parser_Term_match_HasView;
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec(obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
extern obj* l_Lean_Parser_command_Declaration_HasView;
obj* l_Lean_Expander_mkSimpleBinder___closed__4;
obj* l_Lean_Expander_noExpansion___closed__1;
obj* l_Lean_Expander_binderIdentToIdent___main(obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Expander_coeIdentsBindersExt(obj*);
extern obj* l_Lean_Parser_Term_if_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19___boxed(obj*, obj*, obj*);
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_NotationSpec_precedence_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(uint8, obj*, obj*);
extern obj* l_Lean_Parser_Term_binders_HasView;
extern obj* l_Lean_Parser_Term_let_HasView;
obj* l_Lean_Expander_mixfixToNotationSpec___closed__3;
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_introRule;
extern obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___boxed(obj*);
extern obj* l_Lean_Parser_Term_pi_HasView;
obj* l_Lean_Expander_expandBracketedBinder(obj*, obj*);
obj* l_Lean_Expander_coeMixedBindersBindersExt___boxed(obj*);
obj* l_Lean_Expander_noExpansion(obj*);
obj* l_Lean_Expander_bracketedBinders_transform(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_paren_transform___spec__1(obj*);
obj* l_Lean_Expander_expand(obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Expander_if_transform(obj*, obj*);
obj* l_coe___at_Lean_Expander_mkNotationTransformer___spec__2(obj*);
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2;
obj* l_Lean_Expander_mixfix_transform___closed__4;
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_transformerConfigCoeFrontendConfig(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Expander_TransformM_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_TransformM_MonadReader() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_Monad___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_TransformM_MonadExcept() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_Id_Monad;
x_1 = l_ExceptT_MonadExcept___rarg(x_0);
x_2 = l_ReaderT_MonadExcept___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_noExpansion___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Expander_noExpansion(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_noExpansion___closed__1;
return x_1;
}
}
obj* l_Lean_Expander_noExpansion___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_noExpansion(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_1, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::mk_nat_obj(0ul);
x_16 = l_Lean_FileMap_toPosition(x_11, x_15);
x_17 = 2;
x_18 = l_String_splitAux___main___closed__1;
x_19 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set(x_19, 2, x_14);
lean::cnstr_set(x_19, 3, x_18);
lean::cnstr_set(x_19, 4, x_3);
lean::cnstr_set_scalar(x_19, sizeof(void*)*5, x_17);
x_20 = x_19;
x_21 = lean::apply_2(x_5, lean::box(0), x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_2, 0);
x_23 = l_Lean_Parser_Syntax_getPos(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::mk_nat_obj(0ul);
x_25 = l_Lean_FileMap_toPosition(x_11, x_24);
x_26 = 2;
x_27 = l_String_splitAux___main___closed__1;
x_28 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_28, 0, x_9);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_14);
lean::cnstr_set(x_28, 3, x_27);
lean::cnstr_set(x_28, 4, x_3);
lean::cnstr_set_scalar(x_28, sizeof(void*)*5, x_26);
x_29 = x_28;
x_30 = lean::apply_2(x_5, lean::box(0), x_29);
return x_30;
}
else
{
obj* x_31; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
lean::dec(x_23);
x_34 = l_Lean_FileMap_toPosition(x_11, x_31);
x_35 = 2;
x_36 = l_String_splitAux___main___closed__1;
x_37 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_37, 0, x_9);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set(x_37, 2, x_14);
lean::cnstr_set(x_37, 3, x_36);
lean::cnstr_set(x_37, 4, x_3);
lean::cnstr_set_scalar(x_37, sizeof(void*)*5, x_35);
x_38 = x_37;
x_39 = lean::apply_2(x_5, lean::box(0), x_38);
return x_39;
}
}
}
}
obj* l_Lean_Expander_error___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_5);
lean::closure_set(x_10, 3, x_6);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_1, x_10);
return x_11;
}
}
obj* l_Lean_Expander_error(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Expander_error___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_error___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Expander_error___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Expander_error___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Expander_error___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_error(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_coeNameIdent(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = l_Lean_Name_toString___closed__1;
lean::inc(x_0);
x_4 = l_Lean_Name_toStringWithSep___main(x_2, x_0);
x_5 = l_Lean_Parser_Substring_ofString(x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
return x_7;
}
}
obj* l_Lean_Expander_globId(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = l_Lean_Parser_identUnivs_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_Lean_Name_toString___closed__1;
lean::inc(x_0);
x_8 = l_Lean_Name_toStringWithSep___main(x_6, x_0);
x_9 = l_Lean_Parser_Substring_ofString(x_8);
x_10 = lean::box(0);
lean::inc(x_0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_0);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_10);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_5);
x_15 = lean::apply_1(x_2, x_14);
return x_15;
}
}
obj* l_Lean_Expander_coeIdentIdentUnivs(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Expander_coeIdentBinderId(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___rarg), 2, 0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(obj* x_0, obj* x_1) {
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
x_10 = lean::apply_1(x_0, x_4);
x_11 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(x_0, x_6);
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
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Expander_coeIdentsBindersExt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Expander_coeIdentsBindersExt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_coeIdentsBindersExt___rarg), 2, 0);
return x_1;
}
}
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_coeIdentsBindersExt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_coeIdentsBindersExt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_coeBracketedBinderMixedBinder(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___rarg), 2, 0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(obj* x_0, obj* x_1) {
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
x_10 = lean::apply_1(x_0, x_4);
x_11 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(x_0, x_6);
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
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Expander_coeMixedBindersBindersExt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::box(0);
x_3 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(x_0, x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Expander_coeMixedBindersBindersExt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_coeMixedBindersBindersExt___rarg), 2, 0);
return x_1;
}
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_coeMixedBindersBindersExt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_coeMixedBindersBindersExt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_coeBindersExtBinders(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Expander_coeSimpleBinderBinders(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Expander_coeBinderBracketedBinder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_coeBinderBracketedBinder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(")");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_coeBinderBracketedBinder(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_9 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::mk_nat_obj(0ul);
x_11 = l_Lean_FileMap_toPosition(x_6, x_10);
x_12 = 2;
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set(x_14, 3, x_13);
lean::cnstr_set(x_14, 4, x_1);
lean::cnstr_set_scalar(x_14, sizeof(void*)*5, x_12);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_0, 0);
x_18 = l_Lean_Parser_Syntax_getPos(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::mk_nat_obj(0ul);
x_20 = l_Lean_FileMap_toPosition(x_6, x_19);
x_21 = 2;
x_22 = l_String_splitAux___main___closed__1;
x_23 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_9);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_23, 4, x_1);
lean::cnstr_set_scalar(x_23, sizeof(void*)*5, x_21);
x_24 = x_23;
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_26 = lean::cnstr_get(x_18, 0);
lean::inc(x_26);
lean::dec(x_18);
x_29 = l_Lean_FileMap_toPosition(x_6, x_26);
x_30 = 2;
x_31 = l_String_splitAux___main___closed__1;
x_32 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_9);
lean::cnstr_set(x_32, 3, x_31);
lean::cnstr_set(x_32, 4, x_1);
lean::cnstr_set_scalar(x_32, sizeof(void*)*5, x_30);
x_33 = x_32;
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* _init_l___private_init_lean_expander_1__popStxArg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mkNotationTransformer: unreachable");
return x_0;
}
}
obj* l___private_init_lean_expander_1__popStxArg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_4);
x_7 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_8 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_6, x_7, x_0, x_1);
lean::dec(x_0);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 3);
lean::inc(x_21);
lean::dec(x_0);
x_24 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_14);
lean::cnstr_set(x_24, 2, x_19);
lean::cnstr_set(x_24, 3, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Lean_FileMap_toPosition(x_5, x_9);
x_11 = 2;
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_1);
lean::cnstr_set_scalar(x_13, sizeof(void*)*5, x_11);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_0, 0);
x_17 = l_Lean_Parser_Syntax_getPos(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Lean_FileMap_toPosition(x_5, x_18);
x_20 = 2;
x_21 = l_String_splitAux___main___closed__1;
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_3);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set(x_22, 2, x_8);
lean::cnstr_set(x_22, 3, x_21);
lean::cnstr_set(x_22, 4, x_1);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_20);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = l_Lean_FileMap_toPosition(x_5, x_25);
x_29 = 2;
x_30 = l_String_splitAux___main___closed__1;
x_31 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_31, 0, x_3);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_8);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set(x_31, 4, x_1);
lean::cnstr_set_scalar(x_31, sizeof(void*)*5, x_29);
x_32 = x_31;
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_coe___at_Lean_Expander_mkNotationTransformer___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(obj* x_0) {
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
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_4);
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
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mkNotationTransformer: unimplemented");
return x_0;
}
}
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xce\xbb");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(",");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
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
x_21 = l___private_init_lean_expander_1__popStxArg___closed__1;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_21, x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_23) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_33 = x_23;
} else {
 lean::inc(x_31);
 lean::dec(x_23);
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
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_9, 1);
lean::inc(x_38);
lean::dec(x_9);
if (lean::obj_tag(x_38) == 0)
{
obj* x_43; 
lean::dec(x_18);
lean::dec(x_20);
x_43 = lean::cnstr_get(x_35, 1);
lean::inc(x_43);
lean::dec(x_35);
x_1 = x_16;
x_2 = x_43;
goto _start;
}
else
{
obj* x_47; obj* x_49; 
x_47 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 x_49 = x_38;
} else {
 lean::inc(x_47);
 lean::dec(x_38);
 x_49 = lean::box(0);
}
switch (lean::obj_tag(x_47)) {
case 0:
{
obj* x_52; obj* x_56; 
lean::dec(x_20);
lean::dec(x_47);
x_52 = lean::cnstr_get(x_35, 1);
lean::inc(x_52);
lean::dec(x_35);
lean::inc(x_3);
x_56 = l___private_init_lean_expander_1__popStxArg(x_52, x_3);
if (lean::obj_tag(x_56) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_49);
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
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
obj* x_66; obj* x_69; obj* x_71; obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_66 = lean::cnstr_get(x_56, 0);
lean::inc(x_66);
lean::dec(x_56);
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_71, 2);
lean::inc(x_78);
lean::dec(x_71);
x_81 = l_Lean_Parser_Term_binderIdent_HasView;
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
lean::dec(x_81);
x_85 = lean::apply_1(x_82, x_69);
x_86 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_18;
}
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::box(0);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
if (lean::is_scalar(x_49)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_49;
}
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_92, 0, x_74);
lean::cnstr_set(x_92, 1, x_76);
lean::cnstr_set(x_92, 2, x_78);
lean::cnstr_set(x_92, 3, x_91);
x_1 = x_16;
x_2 = x_92;
goto _start;
}
}
case 1:
{
obj* x_97; obj* x_101; 
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_47);
x_97 = lean::cnstr_get(x_35, 1);
lean::inc(x_97);
lean::dec(x_35);
lean::inc(x_3);
x_101 = l___private_init_lean_expander_1__popStxArg(x_97, x_3);
if (lean::obj_tag(x_101) == 0)
{
obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_49);
x_106 = lean::cnstr_get(x_101, 0);
if (lean::is_exclusive(x_101)) {
 x_108 = x_101;
} else {
 lean::inc(x_106);
 lean::dec(x_101);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
return x_109;
}
else
{
obj* x_110; obj* x_113; obj* x_115; obj* x_118; obj* x_120; obj* x_122; obj* x_125; obj* x_126; obj* x_129; obj* x_130; obj* x_131; 
x_110 = lean::cnstr_get(x_101, 0);
lean::inc(x_110);
lean::dec(x_101);
x_113 = lean::cnstr_get(x_110, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::dec(x_110);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_115, 2);
lean::inc(x_122);
lean::dec(x_115);
x_125 = l_Lean_Parser_Term_binders_HasView;
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
lean::dec(x_125);
x_129 = lean::apply_1(x_126, x_113);
if (lean::is_scalar(x_49)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_49;
}
lean::cnstr_set(x_130, 0, x_129);
x_131 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_131, 0, x_118);
lean::cnstr_set(x_131, 1, x_120);
lean::cnstr_set(x_131, 2, x_122);
lean::cnstr_set(x_131, 3, x_130);
x_1 = x_16;
x_2 = x_131;
goto _start;
}
}
default:
{
obj* x_134; obj* x_137; 
lean::dec(x_49);
x_134 = lean::cnstr_get(x_47, 0);
lean::inc(x_134);
lean::dec(x_47);
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_140; obj* x_143; obj* x_147; 
lean::dec(x_20);
x_140 = lean::cnstr_get(x_35, 1);
lean::inc(x_140);
lean::dec(x_35);
x_143 = lean::cnstr_get(x_134, 0);
lean::inc(x_143);
lean::dec(x_134);
lean::inc(x_3);
x_147 = l___private_init_lean_expander_1__popStxArg(x_140, x_3);
if (lean::obj_tag(x_147) == 0)
{
obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_143);
x_153 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_155 = x_147;
} else {
 lean::inc(x_153);
 lean::dec(x_147);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
return x_156;
}
else
{
obj* x_157; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_173; obj* x_176; 
x_157 = lean::cnstr_get(x_147, 0);
lean::inc(x_157);
lean::dec(x_147);
x_160 = lean::cnstr_get(x_157, 0);
x_162 = lean::cnstr_get(x_157, 1);
if (lean::is_exclusive(x_157)) {
 x_164 = x_157;
} else {
 lean::inc(x_160);
 lean::inc(x_162);
 lean::dec(x_157);
 x_164 = lean::box(0);
}
x_165 = lean::cnstr_get(x_162, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_162, 1);
lean::inc(x_167);
if (lean::is_scalar(x_164)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_164;
}
lean::cnstr_set(x_169, 0, x_143);
lean::cnstr_set(x_169, 1, x_160);
x_170 = lean::cnstr_get(x_162, 2);
lean::inc(x_170);
if (lean::is_scalar(x_18)) {
 x_172 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_172 = x_18;
}
lean::cnstr_set(x_172, 0, x_169);
lean::cnstr_set(x_172, 1, x_170);
x_173 = lean::cnstr_get(x_162, 3);
lean::inc(x_173);
lean::dec(x_162);
x_176 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_176, 0, x_165);
lean::cnstr_set(x_176, 1, x_167);
lean::cnstr_set(x_176, 2, x_172);
lean::cnstr_set(x_176, 3, x_173);
x_1 = x_16;
x_2 = x_176;
goto _start;
}
}
else
{
obj* x_178; obj* x_181; 
x_178 = lean::cnstr_get(x_137, 0);
lean::inc(x_178);
lean::dec(x_137);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
lean::dec(x_178);
switch (lean::obj_tag(x_181)) {
case 0:
{
obj* x_186; obj* x_189; obj* x_193; 
lean::dec(x_181);
lean::dec(x_20);
x_186 = lean::cnstr_get(x_35, 1);
lean::inc(x_186);
lean::dec(x_35);
x_189 = lean::cnstr_get(x_134, 0);
lean::inc(x_189);
lean::dec(x_134);
lean::inc(x_3);
x_193 = l___private_init_lean_expander_1__popStxArg(x_186, x_3);
if (lean::obj_tag(x_193) == 0)
{
obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_189);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_199 = lean::cnstr_get(x_193, 0);
if (lean::is_exclusive(x_193)) {
 x_201 = x_193;
} else {
 lean::inc(x_199);
 lean::dec(x_193);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
return x_202;
}
else
{
obj* x_203; obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_216; obj* x_218; obj* x_219; obj* x_222; 
x_203 = lean::cnstr_get(x_193, 0);
lean::inc(x_203);
lean::dec(x_193);
x_206 = lean::cnstr_get(x_203, 0);
x_208 = lean::cnstr_get(x_203, 1);
if (lean::is_exclusive(x_203)) {
 x_210 = x_203;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_203);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_208, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_208, 1);
lean::inc(x_213);
if (lean::is_scalar(x_210)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_210;
}
lean::cnstr_set(x_215, 0, x_189);
lean::cnstr_set(x_215, 1, x_206);
x_216 = lean::cnstr_get(x_208, 2);
lean::inc(x_216);
if (lean::is_scalar(x_18)) {
 x_218 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_218 = x_18;
}
lean::cnstr_set(x_218, 0, x_215);
lean::cnstr_set(x_218, 1, x_216);
x_219 = lean::cnstr_get(x_208, 3);
lean::inc(x_219);
lean::dec(x_208);
x_222 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_222, 0, x_211);
lean::cnstr_set(x_222, 1, x_213);
lean::cnstr_set(x_222, 2, x_218);
lean::cnstr_set(x_222, 3, x_219);
x_1 = x_16;
x_2 = x_222;
goto _start;
}
}
case 2:
{
obj* x_224; obj* x_227; obj* x_230; obj* x_234; 
x_224 = lean::cnstr_get(x_35, 1);
lean::inc(x_224);
lean::dec(x_35);
x_227 = lean::cnstr_get(x_134, 0);
lean::inc(x_227);
lean::dec(x_134);
x_230 = lean::cnstr_get(x_181, 0);
lean::inc(x_230);
lean::dec(x_181);
lean::inc(x_3);
x_234 = l___private_init_lean_expander_1__popStxArg(x_224, x_3);
if (lean::obj_tag(x_234) == 0)
{
obj* x_242; obj* x_244; obj* x_245; 
lean::dec(x_230);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_227);
lean::dec(x_18);
lean::dec(x_20);
x_242 = lean::cnstr_get(x_234, 0);
if (lean::is_exclusive(x_234)) {
 x_244 = x_234;
} else {
 lean::inc(x_242);
 lean::dec(x_234);
 x_244 = lean::box(0);
}
if (lean::is_scalar(x_244)) {
 x_245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_245 = x_244;
}
lean::cnstr_set(x_245, 0, x_242);
return x_245;
}
else
{
obj* x_246; obj* x_249; obj* x_251; 
x_246 = lean::cnstr_get(x_234, 0);
lean::inc(x_246);
lean::dec(x_234);
x_249 = lean::cnstr_get(x_246, 1);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_249, 3);
lean::inc(x_251);
if (lean::obj_tag(x_251) == 0)
{
obj* x_258; 
lean::dec(x_246);
lean::dec(x_230);
lean::dec(x_227);
lean::dec(x_18);
lean::inc(x_3);
x_258 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_21, x_249, x_3);
lean::dec(x_249);
lean::dec(x_20);
if (lean::obj_tag(x_258) == 0)
{
obj* x_264; obj* x_266; obj* x_267; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_264 = lean::cnstr_get(x_258, 0);
if (lean::is_exclusive(x_258)) {
 x_266 = x_258;
} else {
 lean::inc(x_264);
 lean::dec(x_258);
 x_266 = lean::box(0);
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_264);
return x_267;
}
else
{
obj* x_268; obj* x_271; 
x_268 = lean::cnstr_get(x_258, 0);
lean::inc(x_268);
lean::dec(x_258);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
lean::dec(x_268);
x_1 = x_16;
x_2 = x_271;
goto _start;
}
}
else
{
obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_286; obj* x_288; obj* x_289; obj* x_292; obj* x_293; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_303; obj* x_304; obj* x_305; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; 
lean::dec(x_20);
x_276 = lean::cnstr_get(x_246, 0);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_release(x_246, 1);
 x_278 = x_246;
} else {
 lean::inc(x_276);
 lean::dec(x_246);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_249, 0);
x_281 = lean::cnstr_get(x_249, 1);
x_283 = lean::cnstr_get(x_249, 2);
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 3);
 x_285 = x_249;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::dec(x_249);
 x_285 = lean::box(0);
}
x_286 = lean::cnstr_get(x_251, 0);
lean::inc(x_286);
x_288 = l_Lean_Parser_Term_lambda_HasView;
x_289 = lean::cnstr_get(x_288, 1);
lean::inc(x_289);
lean::dec(x_288);
x_292 = lean::box(0);
x_293 = lean::cnstr_get(x_230, 3);
lean::inc(x_293);
x_295 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_296 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_296 = x_18;
}
lean::cnstr_set(x_296, 0, x_293);
lean::cnstr_set(x_296, 1, x_295);
x_297 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_296);
x_298 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_292);
x_299 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_299, 0, x_298);
x_300 = lean::cnstr_get(x_230, 5);
lean::inc(x_300);
lean::dec(x_230);
x_303 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_304 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_305 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_305, 0, x_303);
lean::cnstr_set(x_305, 1, x_299);
lean::cnstr_set(x_305, 2, x_304);
lean::cnstr_set(x_305, 3, x_300);
lean::inc(x_289);
x_307 = lean::apply_1(x_289, x_305);
x_308 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_308, 0, x_303);
lean::cnstr_set(x_308, 1, x_286);
lean::cnstr_set(x_308, 2, x_304);
lean::cnstr_set(x_308, 3, x_276);
x_309 = lean::apply_1(x_289, x_308);
x_310 = l_Lean_Parser_Term_app_HasView;
x_311 = lean::cnstr_get(x_310, 1);
lean::inc(x_311);
lean::dec(x_310);
x_314 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_314, 0, x_307);
lean::cnstr_set(x_314, 1, x_309);
x_315 = lean::apply_1(x_311, x_314);
if (lean::is_scalar(x_278)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_278;
}
lean::cnstr_set(x_316, 0, x_227);
lean::cnstr_set(x_316, 1, x_315);
x_317 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_283);
if (lean::is_scalar(x_285)) {
 x_318 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_318 = x_285;
}
lean::cnstr_set(x_318, 0, x_279);
lean::cnstr_set(x_318, 1, x_281);
lean::cnstr_set(x_318, 2, x_317);
lean::cnstr_set(x_318, 3, x_251);
x_1 = x_16;
x_2 = x_318;
goto _start;
}
}
}
default:
{
obj* x_323; obj* x_326; obj* x_328; 
lean::dec(x_181);
lean::dec(x_18);
lean::dec(x_134);
x_323 = lean::cnstr_get(x_35, 1);
lean::inc(x_323);
lean::dec(x_35);
x_326 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
lean::inc(x_3);
x_328 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_326, x_323, x_3);
lean::dec(x_323);
lean::dec(x_20);
if (lean::obj_tag(x_328) == 0)
{
obj* x_334; obj* x_336; obj* x_337; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_334 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_336 = x_328;
} else {
 lean::inc(x_334);
 lean::dec(x_328);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_334);
return x_337;
}
else
{
obj* x_338; obj* x_341; 
x_338 = lean::cnstr_get(x_328, 0);
lean::inc(x_338);
lean::dec(x_328);
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
lean::dec(x_338);
x_1 = x_16;
x_2 = x_341;
goto _start;
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
obj* x_346; obj* x_348; obj* x_350; 
lean::dec(x_13);
x_346 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_348 = x_1;
} else {
 lean::inc(x_346);
 lean::dec(x_1);
 x_348 = lean::box(0);
}
lean::inc(x_3);
x_350 = l___private_init_lean_expander_1__popStxArg(x_2, x_3);
if (lean::obj_tag(x_350) == 0)
{
obj* x_356; obj* x_358; obj* x_359; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_348);
lean::dec(x_346);
x_356 = lean::cnstr_get(x_350, 0);
if (lean::is_exclusive(x_350)) {
 x_358 = x_350;
} else {
 lean::inc(x_356);
 lean::dec(x_350);
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
obj* x_360; obj* x_363; 
x_360 = lean::cnstr_get(x_350, 0);
lean::inc(x_360);
lean::dec(x_350);
x_363 = lean::cnstr_get(x_9, 1);
lean::inc(x_363);
lean::dec(x_9);
if (lean::obj_tag(x_363) == 0)
{
obj* x_367; 
lean::dec(x_348);
x_367 = lean::cnstr_get(x_360, 1);
lean::inc(x_367);
lean::dec(x_360);
x_1 = x_346;
x_2 = x_367;
goto _start;
}
else
{
obj* x_371; obj* x_373; 
x_371 = lean::cnstr_get(x_363, 0);
if (lean::is_exclusive(x_363)) {
 lean::cnstr_set(x_363, 0, lean::box(0));
 x_373 = x_363;
} else {
 lean::inc(x_371);
 lean::dec(x_363);
 x_373 = lean::box(0);
}
switch (lean::obj_tag(x_371)) {
case 0:
{
obj* x_375; obj* x_379; 
lean::dec(x_371);
x_375 = lean::cnstr_get(x_360, 1);
lean::inc(x_375);
lean::dec(x_360);
lean::inc(x_3);
x_379 = l___private_init_lean_expander_1__popStxArg(x_375, x_3);
if (lean::obj_tag(x_379) == 0)
{
obj* x_385; obj* x_387; obj* x_388; 
lean::dec(x_373);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_348);
lean::dec(x_346);
x_385 = lean::cnstr_get(x_379, 0);
if (lean::is_exclusive(x_379)) {
 x_387 = x_379;
} else {
 lean::inc(x_385);
 lean::dec(x_379);
 x_387 = lean::box(0);
}
if (lean::is_scalar(x_387)) {
 x_388 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_388 = x_387;
}
lean::cnstr_set(x_388, 0, x_385);
return x_388;
}
else
{
obj* x_389; obj* x_392; obj* x_394; obj* x_397; obj* x_399; obj* x_401; obj* x_404; obj* x_405; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; 
x_389 = lean::cnstr_get(x_379, 0);
lean::inc(x_389);
lean::dec(x_379);
x_392 = lean::cnstr_get(x_389, 0);
lean::inc(x_392);
x_394 = lean::cnstr_get(x_389, 1);
lean::inc(x_394);
lean::dec(x_389);
x_397 = lean::cnstr_get(x_394, 0);
lean::inc(x_397);
x_399 = lean::cnstr_get(x_394, 1);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_394, 2);
lean::inc(x_401);
lean::dec(x_394);
x_404 = l_Lean_Parser_Term_binderIdent_HasView;
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
lean::dec(x_404);
x_408 = lean::apply_1(x_405, x_392);
x_409 = lean::box(0);
if (lean::is_scalar(x_348)) {
 x_410 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_410 = x_348;
}
lean::cnstr_set(x_410, 0, x_408);
lean::cnstr_set(x_410, 1, x_409);
x_411 = lean::box(0);
x_412 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_411);
x_413 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_413, 0, x_412);
if (lean::is_scalar(x_373)) {
 x_414 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_414 = x_373;
}
lean::cnstr_set(x_414, 0, x_413);
x_415 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_415, 0, x_397);
lean::cnstr_set(x_415, 1, x_399);
lean::cnstr_set(x_415, 2, x_401);
lean::cnstr_set(x_415, 3, x_414);
x_1 = x_346;
x_2 = x_415;
goto _start;
}
}
case 1:
{
obj* x_419; obj* x_423; 
lean::dec(x_348);
lean::dec(x_371);
x_419 = lean::cnstr_get(x_360, 1);
lean::inc(x_419);
lean::dec(x_360);
lean::inc(x_3);
x_423 = l___private_init_lean_expander_1__popStxArg(x_419, x_3);
if (lean::obj_tag(x_423) == 0)
{
obj* x_428; obj* x_430; obj* x_431; 
lean::dec(x_373);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_428 = lean::cnstr_get(x_423, 0);
if (lean::is_exclusive(x_423)) {
 x_430 = x_423;
} else {
 lean::inc(x_428);
 lean::dec(x_423);
 x_430 = lean::box(0);
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_428);
return x_431;
}
else
{
obj* x_432; obj* x_435; obj* x_437; obj* x_440; obj* x_442; obj* x_444; obj* x_447; obj* x_448; obj* x_451; obj* x_452; obj* x_453; 
x_432 = lean::cnstr_get(x_423, 0);
lean::inc(x_432);
lean::dec(x_423);
x_435 = lean::cnstr_get(x_432, 0);
lean::inc(x_435);
x_437 = lean::cnstr_get(x_432, 1);
lean::inc(x_437);
lean::dec(x_432);
x_440 = lean::cnstr_get(x_437, 0);
lean::inc(x_440);
x_442 = lean::cnstr_get(x_437, 1);
lean::inc(x_442);
x_444 = lean::cnstr_get(x_437, 2);
lean::inc(x_444);
lean::dec(x_437);
x_447 = l_Lean_Parser_Term_binders_HasView;
x_448 = lean::cnstr_get(x_447, 0);
lean::inc(x_448);
lean::dec(x_447);
x_451 = lean::apply_1(x_448, x_435);
if (lean::is_scalar(x_373)) {
 x_452 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_452 = x_373;
}
lean::cnstr_set(x_452, 0, x_451);
x_453 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_453, 0, x_440);
lean::cnstr_set(x_453, 1, x_442);
lean::cnstr_set(x_453, 2, x_444);
lean::cnstr_set(x_453, 3, x_452);
x_1 = x_346;
x_2 = x_453;
goto _start;
}
}
default:
{
obj* x_456; obj* x_459; 
lean::dec(x_373);
x_456 = lean::cnstr_get(x_371, 0);
lean::inc(x_456);
lean::dec(x_371);
x_459 = lean::cnstr_get(x_456, 1);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_461; obj* x_464; obj* x_468; 
x_461 = lean::cnstr_get(x_360, 1);
lean::inc(x_461);
lean::dec(x_360);
x_464 = lean::cnstr_get(x_456, 0);
lean::inc(x_464);
lean::dec(x_456);
lean::inc(x_3);
x_468 = l___private_init_lean_expander_1__popStxArg(x_461, x_3);
if (lean::obj_tag(x_468) == 0)
{
obj* x_474; obj* x_476; obj* x_477; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_464);
lean::dec(x_348);
lean::dec(x_346);
x_474 = lean::cnstr_get(x_468, 0);
if (lean::is_exclusive(x_468)) {
 x_476 = x_468;
} else {
 lean::inc(x_474);
 lean::dec(x_468);
 x_476 = lean::box(0);
}
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_474);
return x_477;
}
else
{
obj* x_478; obj* x_481; obj* x_483; obj* x_485; obj* x_486; obj* x_488; obj* x_490; obj* x_491; obj* x_493; obj* x_494; obj* x_497; 
x_478 = lean::cnstr_get(x_468, 0);
lean::inc(x_478);
lean::dec(x_468);
x_481 = lean::cnstr_get(x_478, 0);
x_483 = lean::cnstr_get(x_478, 1);
if (lean::is_exclusive(x_478)) {
 x_485 = x_478;
} else {
 lean::inc(x_481);
 lean::inc(x_483);
 lean::dec(x_478);
 x_485 = lean::box(0);
}
x_486 = lean::cnstr_get(x_483, 0);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_483, 1);
lean::inc(x_488);
if (lean::is_scalar(x_485)) {
 x_490 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_490 = x_485;
}
lean::cnstr_set(x_490, 0, x_464);
lean::cnstr_set(x_490, 1, x_481);
x_491 = lean::cnstr_get(x_483, 2);
lean::inc(x_491);
if (lean::is_scalar(x_348)) {
 x_493 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_493 = x_348;
}
lean::cnstr_set(x_493, 0, x_490);
lean::cnstr_set(x_493, 1, x_491);
x_494 = lean::cnstr_get(x_483, 3);
lean::inc(x_494);
lean::dec(x_483);
x_497 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_497, 0, x_486);
lean::cnstr_set(x_497, 1, x_488);
lean::cnstr_set(x_497, 2, x_493);
lean::cnstr_set(x_497, 3, x_494);
x_1 = x_346;
x_2 = x_497;
goto _start;
}
}
else
{
obj* x_499; obj* x_501; obj* x_502; 
x_499 = lean::cnstr_get(x_459, 0);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_set(x_459, 0, lean::box(0));
 x_501 = x_459;
} else {
 lean::inc(x_499);
 lean::dec(x_459);
 x_501 = lean::box(0);
}
x_502 = lean::cnstr_get(x_499, 1);
lean::inc(x_502);
lean::dec(x_499);
switch (lean::obj_tag(x_502)) {
case 0:
{
obj* x_507; obj* x_510; obj* x_514; 
lean::dec(x_501);
lean::dec(x_502);
x_507 = lean::cnstr_get(x_360, 1);
lean::inc(x_507);
lean::dec(x_360);
x_510 = lean::cnstr_get(x_456, 0);
lean::inc(x_510);
lean::dec(x_456);
lean::inc(x_3);
x_514 = l___private_init_lean_expander_1__popStxArg(x_507, x_3);
if (lean::obj_tag(x_514) == 0)
{
obj* x_520; obj* x_522; obj* x_523; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_510);
lean::dec(x_348);
lean::dec(x_346);
x_520 = lean::cnstr_get(x_514, 0);
if (lean::is_exclusive(x_514)) {
 x_522 = x_514;
} else {
 lean::inc(x_520);
 lean::dec(x_514);
 x_522 = lean::box(0);
}
if (lean::is_scalar(x_522)) {
 x_523 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_523 = x_522;
}
lean::cnstr_set(x_523, 0, x_520);
return x_523;
}
else
{
obj* x_524; obj* x_527; obj* x_529; obj* x_531; obj* x_532; obj* x_534; obj* x_536; obj* x_537; obj* x_539; obj* x_540; obj* x_543; 
x_524 = lean::cnstr_get(x_514, 0);
lean::inc(x_524);
lean::dec(x_514);
x_527 = lean::cnstr_get(x_524, 0);
x_529 = lean::cnstr_get(x_524, 1);
if (lean::is_exclusive(x_524)) {
 x_531 = x_524;
} else {
 lean::inc(x_527);
 lean::inc(x_529);
 lean::dec(x_524);
 x_531 = lean::box(0);
}
x_532 = lean::cnstr_get(x_529, 0);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_529, 1);
lean::inc(x_534);
if (lean::is_scalar(x_531)) {
 x_536 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_536 = x_531;
}
lean::cnstr_set(x_536, 0, x_510);
lean::cnstr_set(x_536, 1, x_527);
x_537 = lean::cnstr_get(x_529, 2);
lean::inc(x_537);
if (lean::is_scalar(x_348)) {
 x_539 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_539 = x_348;
}
lean::cnstr_set(x_539, 0, x_536);
lean::cnstr_set(x_539, 1, x_537);
x_540 = lean::cnstr_get(x_529, 3);
lean::inc(x_540);
lean::dec(x_529);
x_543 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_543, 0, x_532);
lean::cnstr_set(x_543, 1, x_534);
lean::cnstr_set(x_543, 2, x_539);
lean::cnstr_set(x_543, 3, x_540);
x_1 = x_346;
x_2 = x_543;
goto _start;
}
}
case 2:
{
obj* x_545; obj* x_548; obj* x_551; obj* x_555; 
x_545 = lean::cnstr_get(x_360, 1);
lean::inc(x_545);
lean::dec(x_360);
x_548 = lean::cnstr_get(x_456, 0);
lean::inc(x_548);
lean::dec(x_456);
x_551 = lean::cnstr_get(x_502, 0);
lean::inc(x_551);
lean::dec(x_502);
lean::inc(x_3);
x_555 = l___private_init_lean_expander_1__popStxArg(x_545, x_3);
if (lean::obj_tag(x_555) == 0)
{
obj* x_563; obj* x_565; obj* x_566; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_501);
lean::dec(x_348);
lean::dec(x_346);
lean::dec(x_548);
lean::dec(x_551);
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
obj* x_567; obj* x_570; obj* x_572; 
x_567 = lean::cnstr_get(x_555, 0);
lean::inc(x_567);
lean::dec(x_555);
x_570 = lean::cnstr_get(x_567, 1);
lean::inc(x_570);
x_572 = lean::cnstr_get(x_570, 3);
lean::inc(x_572);
if (lean::obj_tag(x_572) == 0)
{
obj* x_579; obj* x_580; obj* x_582; 
lean::dec(x_348);
lean::dec(x_548);
lean::dec(x_551);
lean::dec(x_567);
lean::inc(x_0);
if (lean::is_scalar(x_501)) {
 x_579 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_579 = x_501;
}
lean::cnstr_set(x_579, 0, x_0);
x_580 = l___private_init_lean_expander_1__popStxArg___closed__1;
lean::inc(x_3);
x_582 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_579, x_580, x_570, x_3);
lean::dec(x_570);
lean::dec(x_579);
if (lean::obj_tag(x_582) == 0)
{
obj* x_588; obj* x_590; obj* x_591; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_588 = lean::cnstr_get(x_582, 0);
if (lean::is_exclusive(x_582)) {
 x_590 = x_582;
} else {
 lean::inc(x_588);
 lean::dec(x_582);
 x_590 = lean::box(0);
}
if (lean::is_scalar(x_590)) {
 x_591 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_591 = x_590;
}
lean::cnstr_set(x_591, 0, x_588);
return x_591;
}
else
{
obj* x_592; obj* x_595; 
x_592 = lean::cnstr_get(x_582, 0);
lean::inc(x_592);
lean::dec(x_582);
x_595 = lean::cnstr_get(x_592, 1);
lean::inc(x_595);
lean::dec(x_592);
x_1 = x_346;
x_2 = x_595;
goto _start;
}
}
else
{
obj* x_600; obj* x_602; obj* x_603; obj* x_605; obj* x_607; obj* x_609; obj* x_610; obj* x_612; obj* x_613; obj* x_616; obj* x_617; obj* x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_627; obj* x_628; obj* x_629; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_638; obj* x_639; obj* x_640; obj* x_641; obj* x_642; 
lean::dec(x_501);
x_600 = lean::cnstr_get(x_567, 0);
if (lean::is_exclusive(x_567)) {
 lean::cnstr_release(x_567, 1);
 x_602 = x_567;
} else {
 lean::inc(x_600);
 lean::dec(x_567);
 x_602 = lean::box(0);
}
x_603 = lean::cnstr_get(x_570, 0);
x_605 = lean::cnstr_get(x_570, 1);
x_607 = lean::cnstr_get(x_570, 2);
if (lean::is_exclusive(x_570)) {
 lean::cnstr_release(x_570, 3);
 x_609 = x_570;
} else {
 lean::inc(x_603);
 lean::inc(x_605);
 lean::inc(x_607);
 lean::dec(x_570);
 x_609 = lean::box(0);
}
x_610 = lean::cnstr_get(x_572, 0);
lean::inc(x_610);
x_612 = l_Lean_Parser_Term_lambda_HasView;
x_613 = lean::cnstr_get(x_612, 1);
lean::inc(x_613);
lean::dec(x_612);
x_616 = lean::box(0);
x_617 = lean::cnstr_get(x_551, 3);
lean::inc(x_617);
x_619 = lean::box(0);
if (lean::is_scalar(x_348)) {
 x_620 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_620 = x_348;
}
lean::cnstr_set(x_620, 0, x_617);
lean::cnstr_set(x_620, 1, x_619);
x_621 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_620);
x_622 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_622, 0, x_621);
lean::cnstr_set(x_622, 1, x_616);
x_623 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_623, 0, x_622);
x_624 = lean::cnstr_get(x_551, 5);
lean::inc(x_624);
lean::dec(x_551);
x_627 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_628 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_629 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_629, 0, x_627);
lean::cnstr_set(x_629, 1, x_623);
lean::cnstr_set(x_629, 2, x_628);
lean::cnstr_set(x_629, 3, x_624);
lean::inc(x_613);
x_631 = lean::apply_1(x_613, x_629);
x_632 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_632, 0, x_627);
lean::cnstr_set(x_632, 1, x_610);
lean::cnstr_set(x_632, 2, x_628);
lean::cnstr_set(x_632, 3, x_600);
x_633 = lean::apply_1(x_613, x_632);
x_634 = l_Lean_Parser_Term_app_HasView;
x_635 = lean::cnstr_get(x_634, 1);
lean::inc(x_635);
lean::dec(x_634);
x_638 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_638, 0, x_631);
lean::cnstr_set(x_638, 1, x_633);
x_639 = lean::apply_1(x_635, x_638);
if (lean::is_scalar(x_602)) {
 x_640 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_640 = x_602;
}
lean::cnstr_set(x_640, 0, x_548);
lean::cnstr_set(x_640, 1, x_639);
x_641 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_641, 0, x_640);
lean::cnstr_set(x_641, 1, x_607);
if (lean::is_scalar(x_609)) {
 x_642 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_642 = x_609;
}
lean::cnstr_set(x_642, 0, x_603);
lean::cnstr_set(x_642, 1, x_605);
lean::cnstr_set(x_642, 2, x_641);
lean::cnstr_set(x_642, 3, x_572);
x_1 = x_346;
x_2 = x_642;
goto _start;
}
}
}
default:
{
obj* x_647; obj* x_651; obj* x_652; obj* x_654; 
lean::dec(x_456);
lean::dec(x_502);
lean::dec(x_348);
x_647 = lean::cnstr_get(x_360, 1);
lean::inc(x_647);
lean::dec(x_360);
lean::inc(x_0);
if (lean::is_scalar(x_501)) {
 x_651 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_651 = x_501;
}
lean::cnstr_set(x_651, 0, x_0);
x_652 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
lean::inc(x_3);
x_654 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_651, x_652, x_647, x_3);
lean::dec(x_647);
lean::dec(x_651);
if (lean::obj_tag(x_654) == 0)
{
obj* x_660; obj* x_662; obj* x_663; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_660 = lean::cnstr_get(x_654, 0);
if (lean::is_exclusive(x_654)) {
 x_662 = x_654;
} else {
 lean::inc(x_660);
 lean::dec(x_654);
 x_662 = lean::box(0);
}
if (lean::is_scalar(x_662)) {
 x_663 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_663 = x_662;
}
lean::cnstr_set(x_663, 0, x_660);
return x_663;
}
else
{
obj* x_664; obj* x_667; 
x_664 = lean::cnstr_get(x_654, 0);
lean::inc(x_664);
lean::dec(x_654);
x_667 = lean::cnstr_get(x_664, 1);
lean::inc(x_667);
lean::dec(x_664);
x_1 = x_346;
x_2 = x_667;
goto _start;
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
}
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
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
x_7 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_4);
x_8 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_12 = x_2;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_10);
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
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Parser_Syntax_isOfKind___main(x_0, x_1);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_Lean_Parser_identUnivs_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean_name_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_13 == 0)
{
lean::dec(x_10);
x_1 = x_5;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_5);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_10);
return x_18;
}
}
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
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
x_21 = l___private_init_lean_expander_1__popStxArg___closed__1;
lean::inc(x_3);
x_23 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_21, x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_23) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_33 = x_23;
} else {
 lean::inc(x_31);
 lean::dec(x_23);
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
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_9, 1);
lean::inc(x_38);
lean::dec(x_9);
if (lean::obj_tag(x_38) == 0)
{
obj* x_43; 
lean::dec(x_18);
lean::dec(x_20);
x_43 = lean::cnstr_get(x_35, 1);
lean::inc(x_43);
lean::dec(x_35);
x_1 = x_16;
x_2 = x_43;
goto _start;
}
else
{
obj* x_47; obj* x_49; 
x_47 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 x_49 = x_38;
} else {
 lean::inc(x_47);
 lean::dec(x_38);
 x_49 = lean::box(0);
}
switch (lean::obj_tag(x_47)) {
case 0:
{
obj* x_52; obj* x_56; 
lean::dec(x_20);
lean::dec(x_47);
x_52 = lean::cnstr_get(x_35, 1);
lean::inc(x_52);
lean::dec(x_35);
lean::inc(x_3);
x_56 = l___private_init_lean_expander_1__popStxArg(x_52, x_3);
if (lean::obj_tag(x_56) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_49);
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
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
obj* x_66; obj* x_69; obj* x_71; obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_66 = lean::cnstr_get(x_56, 0);
lean::inc(x_66);
lean::dec(x_56);
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_71, 2);
lean::inc(x_78);
lean::dec(x_71);
x_81 = l_Lean_Parser_Term_binderIdent_HasView;
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
lean::dec(x_81);
x_85 = lean::apply_1(x_82, x_69);
x_86 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_18;
}
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::box(0);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
if (lean::is_scalar(x_49)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_49;
}
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_92, 0, x_74);
lean::cnstr_set(x_92, 1, x_76);
lean::cnstr_set(x_92, 2, x_78);
lean::cnstr_set(x_92, 3, x_91);
x_1 = x_16;
x_2 = x_92;
goto _start;
}
}
case 1:
{
obj* x_97; obj* x_101; 
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_47);
x_97 = lean::cnstr_get(x_35, 1);
lean::inc(x_97);
lean::dec(x_35);
lean::inc(x_3);
x_101 = l___private_init_lean_expander_1__popStxArg(x_97, x_3);
if (lean::obj_tag(x_101) == 0)
{
obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_49);
x_106 = lean::cnstr_get(x_101, 0);
if (lean::is_exclusive(x_101)) {
 x_108 = x_101;
} else {
 lean::inc(x_106);
 lean::dec(x_101);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
return x_109;
}
else
{
obj* x_110; obj* x_113; obj* x_115; obj* x_118; obj* x_120; obj* x_122; obj* x_125; obj* x_126; obj* x_129; obj* x_130; obj* x_131; 
x_110 = lean::cnstr_get(x_101, 0);
lean::inc(x_110);
lean::dec(x_101);
x_113 = lean::cnstr_get(x_110, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::dec(x_110);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_115, 2);
lean::inc(x_122);
lean::dec(x_115);
x_125 = l_Lean_Parser_Term_binders_HasView;
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
lean::dec(x_125);
x_129 = lean::apply_1(x_126, x_113);
if (lean::is_scalar(x_49)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_49;
}
lean::cnstr_set(x_130, 0, x_129);
x_131 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_131, 0, x_118);
lean::cnstr_set(x_131, 1, x_120);
lean::cnstr_set(x_131, 2, x_122);
lean::cnstr_set(x_131, 3, x_130);
x_1 = x_16;
x_2 = x_131;
goto _start;
}
}
default:
{
obj* x_134; obj* x_137; 
lean::dec(x_49);
x_134 = lean::cnstr_get(x_47, 0);
lean::inc(x_134);
lean::dec(x_47);
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_140; obj* x_143; obj* x_147; 
lean::dec(x_20);
x_140 = lean::cnstr_get(x_35, 1);
lean::inc(x_140);
lean::dec(x_35);
x_143 = lean::cnstr_get(x_134, 0);
lean::inc(x_143);
lean::dec(x_134);
lean::inc(x_3);
x_147 = l___private_init_lean_expander_1__popStxArg(x_140, x_3);
if (lean::obj_tag(x_147) == 0)
{
obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_143);
x_153 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_155 = x_147;
} else {
 lean::inc(x_153);
 lean::dec(x_147);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
return x_156;
}
else
{
obj* x_157; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_173; obj* x_176; 
x_157 = lean::cnstr_get(x_147, 0);
lean::inc(x_157);
lean::dec(x_147);
x_160 = lean::cnstr_get(x_157, 0);
x_162 = lean::cnstr_get(x_157, 1);
if (lean::is_exclusive(x_157)) {
 x_164 = x_157;
} else {
 lean::inc(x_160);
 lean::inc(x_162);
 lean::dec(x_157);
 x_164 = lean::box(0);
}
x_165 = lean::cnstr_get(x_162, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_162, 1);
lean::inc(x_167);
if (lean::is_scalar(x_164)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_164;
}
lean::cnstr_set(x_169, 0, x_143);
lean::cnstr_set(x_169, 1, x_160);
x_170 = lean::cnstr_get(x_162, 2);
lean::inc(x_170);
if (lean::is_scalar(x_18)) {
 x_172 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_172 = x_18;
}
lean::cnstr_set(x_172, 0, x_169);
lean::cnstr_set(x_172, 1, x_170);
x_173 = lean::cnstr_get(x_162, 3);
lean::inc(x_173);
lean::dec(x_162);
x_176 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_176, 0, x_165);
lean::cnstr_set(x_176, 1, x_167);
lean::cnstr_set(x_176, 2, x_172);
lean::cnstr_set(x_176, 3, x_173);
x_1 = x_16;
x_2 = x_176;
goto _start;
}
}
else
{
obj* x_178; obj* x_181; 
x_178 = lean::cnstr_get(x_137, 0);
lean::inc(x_178);
lean::dec(x_137);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
lean::dec(x_178);
switch (lean::obj_tag(x_181)) {
case 0:
{
obj* x_186; obj* x_189; obj* x_193; 
lean::dec(x_181);
lean::dec(x_20);
x_186 = lean::cnstr_get(x_35, 1);
lean::inc(x_186);
lean::dec(x_35);
x_189 = lean::cnstr_get(x_134, 0);
lean::inc(x_189);
lean::dec(x_134);
lean::inc(x_3);
x_193 = l___private_init_lean_expander_1__popStxArg(x_186, x_3);
if (lean::obj_tag(x_193) == 0)
{
obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_189);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_199 = lean::cnstr_get(x_193, 0);
if (lean::is_exclusive(x_193)) {
 x_201 = x_193;
} else {
 lean::inc(x_199);
 lean::dec(x_193);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
return x_202;
}
else
{
obj* x_203; obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_216; obj* x_218; obj* x_219; obj* x_222; 
x_203 = lean::cnstr_get(x_193, 0);
lean::inc(x_203);
lean::dec(x_193);
x_206 = lean::cnstr_get(x_203, 0);
x_208 = lean::cnstr_get(x_203, 1);
if (lean::is_exclusive(x_203)) {
 x_210 = x_203;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_203);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_208, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_208, 1);
lean::inc(x_213);
if (lean::is_scalar(x_210)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_210;
}
lean::cnstr_set(x_215, 0, x_189);
lean::cnstr_set(x_215, 1, x_206);
x_216 = lean::cnstr_get(x_208, 2);
lean::inc(x_216);
if (lean::is_scalar(x_18)) {
 x_218 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_218 = x_18;
}
lean::cnstr_set(x_218, 0, x_215);
lean::cnstr_set(x_218, 1, x_216);
x_219 = lean::cnstr_get(x_208, 3);
lean::inc(x_219);
lean::dec(x_208);
x_222 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_222, 0, x_211);
lean::cnstr_set(x_222, 1, x_213);
lean::cnstr_set(x_222, 2, x_218);
lean::cnstr_set(x_222, 3, x_219);
x_1 = x_16;
x_2 = x_222;
goto _start;
}
}
case 2:
{
obj* x_224; obj* x_227; obj* x_230; obj* x_234; 
x_224 = lean::cnstr_get(x_35, 1);
lean::inc(x_224);
lean::dec(x_35);
x_227 = lean::cnstr_get(x_134, 0);
lean::inc(x_227);
lean::dec(x_134);
x_230 = lean::cnstr_get(x_181, 0);
lean::inc(x_230);
lean::dec(x_181);
lean::inc(x_3);
x_234 = l___private_init_lean_expander_1__popStxArg(x_224, x_3);
if (lean::obj_tag(x_234) == 0)
{
obj* x_242; obj* x_244; obj* x_245; 
lean::dec(x_230);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_227);
lean::dec(x_18);
lean::dec(x_20);
x_242 = lean::cnstr_get(x_234, 0);
if (lean::is_exclusive(x_234)) {
 x_244 = x_234;
} else {
 lean::inc(x_242);
 lean::dec(x_234);
 x_244 = lean::box(0);
}
if (lean::is_scalar(x_244)) {
 x_245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_245 = x_244;
}
lean::cnstr_set(x_245, 0, x_242);
return x_245;
}
else
{
obj* x_246; obj* x_249; obj* x_251; 
x_246 = lean::cnstr_get(x_234, 0);
lean::inc(x_246);
lean::dec(x_234);
x_249 = lean::cnstr_get(x_246, 1);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_249, 3);
lean::inc(x_251);
if (lean::obj_tag(x_251) == 0)
{
obj* x_258; 
lean::dec(x_246);
lean::dec(x_230);
lean::dec(x_227);
lean::dec(x_18);
lean::inc(x_3);
x_258 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_21, x_249, x_3);
lean::dec(x_249);
lean::dec(x_20);
if (lean::obj_tag(x_258) == 0)
{
obj* x_264; obj* x_266; obj* x_267; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_264 = lean::cnstr_get(x_258, 0);
if (lean::is_exclusive(x_258)) {
 x_266 = x_258;
} else {
 lean::inc(x_264);
 lean::dec(x_258);
 x_266 = lean::box(0);
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_264);
return x_267;
}
else
{
obj* x_268; obj* x_271; 
x_268 = lean::cnstr_get(x_258, 0);
lean::inc(x_268);
lean::dec(x_258);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
lean::dec(x_268);
x_1 = x_16;
x_2 = x_271;
goto _start;
}
}
else
{
obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_286; obj* x_288; obj* x_289; obj* x_292; obj* x_293; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_303; obj* x_304; obj* x_305; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; 
lean::dec(x_20);
x_276 = lean::cnstr_get(x_246, 0);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_release(x_246, 1);
 x_278 = x_246;
} else {
 lean::inc(x_276);
 lean::dec(x_246);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_249, 0);
x_281 = lean::cnstr_get(x_249, 1);
x_283 = lean::cnstr_get(x_249, 2);
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 3);
 x_285 = x_249;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::dec(x_249);
 x_285 = lean::box(0);
}
x_286 = lean::cnstr_get(x_251, 0);
lean::inc(x_286);
x_288 = l_Lean_Parser_Term_lambda_HasView;
x_289 = lean::cnstr_get(x_288, 1);
lean::inc(x_289);
lean::dec(x_288);
x_292 = lean::box(0);
x_293 = lean::cnstr_get(x_230, 3);
lean::inc(x_293);
x_295 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_296 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_296 = x_18;
}
lean::cnstr_set(x_296, 0, x_293);
lean::cnstr_set(x_296, 1, x_295);
x_297 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_296);
x_298 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_292);
x_299 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_299, 0, x_298);
x_300 = lean::cnstr_get(x_230, 5);
lean::inc(x_300);
lean::dec(x_230);
x_303 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_304 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_305 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_305, 0, x_303);
lean::cnstr_set(x_305, 1, x_299);
lean::cnstr_set(x_305, 2, x_304);
lean::cnstr_set(x_305, 3, x_300);
lean::inc(x_289);
x_307 = lean::apply_1(x_289, x_305);
x_308 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_308, 0, x_303);
lean::cnstr_set(x_308, 1, x_286);
lean::cnstr_set(x_308, 2, x_304);
lean::cnstr_set(x_308, 3, x_276);
x_309 = lean::apply_1(x_289, x_308);
x_310 = l_Lean_Parser_Term_app_HasView;
x_311 = lean::cnstr_get(x_310, 1);
lean::inc(x_311);
lean::dec(x_310);
x_314 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_314, 0, x_307);
lean::cnstr_set(x_314, 1, x_309);
x_315 = lean::apply_1(x_311, x_314);
if (lean::is_scalar(x_278)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_278;
}
lean::cnstr_set(x_316, 0, x_227);
lean::cnstr_set(x_316, 1, x_315);
x_317 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_283);
if (lean::is_scalar(x_285)) {
 x_318 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_318 = x_285;
}
lean::cnstr_set(x_318, 0, x_279);
lean::cnstr_set(x_318, 1, x_281);
lean::cnstr_set(x_318, 2, x_317);
lean::cnstr_set(x_318, 3, x_251);
x_1 = x_16;
x_2 = x_318;
goto _start;
}
}
}
default:
{
obj* x_323; obj* x_326; obj* x_328; 
lean::dec(x_181);
lean::dec(x_18);
lean::dec(x_134);
x_323 = lean::cnstr_get(x_35, 1);
lean::inc(x_323);
lean::dec(x_35);
x_326 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
lean::inc(x_3);
x_328 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_20, x_326, x_323, x_3);
lean::dec(x_323);
lean::dec(x_20);
if (lean::obj_tag(x_328) == 0)
{
obj* x_334; obj* x_336; obj* x_337; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_334 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_336 = x_328;
} else {
 lean::inc(x_334);
 lean::dec(x_328);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_334);
return x_337;
}
else
{
obj* x_338; obj* x_341; 
x_338 = lean::cnstr_get(x_328, 0);
lean::inc(x_338);
lean::dec(x_328);
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
lean::dec(x_338);
x_1 = x_16;
x_2 = x_341;
goto _start;
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
obj* x_346; obj* x_348; obj* x_350; 
lean::dec(x_13);
x_346 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_348 = x_1;
} else {
 lean::inc(x_346);
 lean::dec(x_1);
 x_348 = lean::box(0);
}
lean::inc(x_3);
x_350 = l___private_init_lean_expander_1__popStxArg(x_2, x_3);
if (lean::obj_tag(x_350) == 0)
{
obj* x_356; obj* x_358; obj* x_359; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_348);
lean::dec(x_346);
x_356 = lean::cnstr_get(x_350, 0);
if (lean::is_exclusive(x_350)) {
 x_358 = x_350;
} else {
 lean::inc(x_356);
 lean::dec(x_350);
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
obj* x_360; obj* x_363; 
x_360 = lean::cnstr_get(x_350, 0);
lean::inc(x_360);
lean::dec(x_350);
x_363 = lean::cnstr_get(x_9, 1);
lean::inc(x_363);
lean::dec(x_9);
if (lean::obj_tag(x_363) == 0)
{
obj* x_367; 
lean::dec(x_348);
x_367 = lean::cnstr_get(x_360, 1);
lean::inc(x_367);
lean::dec(x_360);
x_1 = x_346;
x_2 = x_367;
goto _start;
}
else
{
obj* x_371; obj* x_373; 
x_371 = lean::cnstr_get(x_363, 0);
if (lean::is_exclusive(x_363)) {
 lean::cnstr_set(x_363, 0, lean::box(0));
 x_373 = x_363;
} else {
 lean::inc(x_371);
 lean::dec(x_363);
 x_373 = lean::box(0);
}
switch (lean::obj_tag(x_371)) {
case 0:
{
obj* x_375; obj* x_379; 
lean::dec(x_371);
x_375 = lean::cnstr_get(x_360, 1);
lean::inc(x_375);
lean::dec(x_360);
lean::inc(x_3);
x_379 = l___private_init_lean_expander_1__popStxArg(x_375, x_3);
if (lean::obj_tag(x_379) == 0)
{
obj* x_385; obj* x_387; obj* x_388; 
lean::dec(x_373);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_348);
lean::dec(x_346);
x_385 = lean::cnstr_get(x_379, 0);
if (lean::is_exclusive(x_379)) {
 x_387 = x_379;
} else {
 lean::inc(x_385);
 lean::dec(x_379);
 x_387 = lean::box(0);
}
if (lean::is_scalar(x_387)) {
 x_388 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_388 = x_387;
}
lean::cnstr_set(x_388, 0, x_385);
return x_388;
}
else
{
obj* x_389; obj* x_392; obj* x_394; obj* x_397; obj* x_399; obj* x_401; obj* x_404; obj* x_405; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; 
x_389 = lean::cnstr_get(x_379, 0);
lean::inc(x_389);
lean::dec(x_379);
x_392 = lean::cnstr_get(x_389, 0);
lean::inc(x_392);
x_394 = lean::cnstr_get(x_389, 1);
lean::inc(x_394);
lean::dec(x_389);
x_397 = lean::cnstr_get(x_394, 0);
lean::inc(x_397);
x_399 = lean::cnstr_get(x_394, 1);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_394, 2);
lean::inc(x_401);
lean::dec(x_394);
x_404 = l_Lean_Parser_Term_binderIdent_HasView;
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
lean::dec(x_404);
x_408 = lean::apply_1(x_405, x_392);
x_409 = lean::box(0);
if (lean::is_scalar(x_348)) {
 x_410 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_410 = x_348;
}
lean::cnstr_set(x_410, 0, x_408);
lean::cnstr_set(x_410, 1, x_409);
x_411 = lean::box(0);
x_412 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_411);
x_413 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_413, 0, x_412);
if (lean::is_scalar(x_373)) {
 x_414 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_414 = x_373;
}
lean::cnstr_set(x_414, 0, x_413);
x_415 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_415, 0, x_397);
lean::cnstr_set(x_415, 1, x_399);
lean::cnstr_set(x_415, 2, x_401);
lean::cnstr_set(x_415, 3, x_414);
x_1 = x_346;
x_2 = x_415;
goto _start;
}
}
case 1:
{
obj* x_419; obj* x_423; 
lean::dec(x_348);
lean::dec(x_371);
x_419 = lean::cnstr_get(x_360, 1);
lean::inc(x_419);
lean::dec(x_360);
lean::inc(x_3);
x_423 = l___private_init_lean_expander_1__popStxArg(x_419, x_3);
if (lean::obj_tag(x_423) == 0)
{
obj* x_428; obj* x_430; obj* x_431; 
lean::dec(x_373);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_428 = lean::cnstr_get(x_423, 0);
if (lean::is_exclusive(x_423)) {
 x_430 = x_423;
} else {
 lean::inc(x_428);
 lean::dec(x_423);
 x_430 = lean::box(0);
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_428);
return x_431;
}
else
{
obj* x_432; obj* x_435; obj* x_437; obj* x_440; obj* x_442; obj* x_444; obj* x_447; obj* x_448; obj* x_451; obj* x_452; obj* x_453; 
x_432 = lean::cnstr_get(x_423, 0);
lean::inc(x_432);
lean::dec(x_423);
x_435 = lean::cnstr_get(x_432, 0);
lean::inc(x_435);
x_437 = lean::cnstr_get(x_432, 1);
lean::inc(x_437);
lean::dec(x_432);
x_440 = lean::cnstr_get(x_437, 0);
lean::inc(x_440);
x_442 = lean::cnstr_get(x_437, 1);
lean::inc(x_442);
x_444 = lean::cnstr_get(x_437, 2);
lean::inc(x_444);
lean::dec(x_437);
x_447 = l_Lean_Parser_Term_binders_HasView;
x_448 = lean::cnstr_get(x_447, 0);
lean::inc(x_448);
lean::dec(x_447);
x_451 = lean::apply_1(x_448, x_435);
if (lean::is_scalar(x_373)) {
 x_452 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_452 = x_373;
}
lean::cnstr_set(x_452, 0, x_451);
x_453 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_453, 0, x_440);
lean::cnstr_set(x_453, 1, x_442);
lean::cnstr_set(x_453, 2, x_444);
lean::cnstr_set(x_453, 3, x_452);
x_1 = x_346;
x_2 = x_453;
goto _start;
}
}
default:
{
obj* x_456; obj* x_459; 
lean::dec(x_373);
x_456 = lean::cnstr_get(x_371, 0);
lean::inc(x_456);
lean::dec(x_371);
x_459 = lean::cnstr_get(x_456, 1);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_461; obj* x_464; obj* x_468; 
x_461 = lean::cnstr_get(x_360, 1);
lean::inc(x_461);
lean::dec(x_360);
x_464 = lean::cnstr_get(x_456, 0);
lean::inc(x_464);
lean::dec(x_456);
lean::inc(x_3);
x_468 = l___private_init_lean_expander_1__popStxArg(x_461, x_3);
if (lean::obj_tag(x_468) == 0)
{
obj* x_474; obj* x_476; obj* x_477; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_464);
lean::dec(x_348);
lean::dec(x_346);
x_474 = lean::cnstr_get(x_468, 0);
if (lean::is_exclusive(x_468)) {
 x_476 = x_468;
} else {
 lean::inc(x_474);
 lean::dec(x_468);
 x_476 = lean::box(0);
}
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_474);
return x_477;
}
else
{
obj* x_478; obj* x_481; obj* x_483; obj* x_485; obj* x_486; obj* x_488; obj* x_490; obj* x_491; obj* x_493; obj* x_494; obj* x_497; 
x_478 = lean::cnstr_get(x_468, 0);
lean::inc(x_478);
lean::dec(x_468);
x_481 = lean::cnstr_get(x_478, 0);
x_483 = lean::cnstr_get(x_478, 1);
if (lean::is_exclusive(x_478)) {
 x_485 = x_478;
} else {
 lean::inc(x_481);
 lean::inc(x_483);
 lean::dec(x_478);
 x_485 = lean::box(0);
}
x_486 = lean::cnstr_get(x_483, 0);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_483, 1);
lean::inc(x_488);
if (lean::is_scalar(x_485)) {
 x_490 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_490 = x_485;
}
lean::cnstr_set(x_490, 0, x_464);
lean::cnstr_set(x_490, 1, x_481);
x_491 = lean::cnstr_get(x_483, 2);
lean::inc(x_491);
if (lean::is_scalar(x_348)) {
 x_493 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_493 = x_348;
}
lean::cnstr_set(x_493, 0, x_490);
lean::cnstr_set(x_493, 1, x_491);
x_494 = lean::cnstr_get(x_483, 3);
lean::inc(x_494);
lean::dec(x_483);
x_497 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_497, 0, x_486);
lean::cnstr_set(x_497, 1, x_488);
lean::cnstr_set(x_497, 2, x_493);
lean::cnstr_set(x_497, 3, x_494);
x_1 = x_346;
x_2 = x_497;
goto _start;
}
}
else
{
obj* x_499; obj* x_501; obj* x_502; 
x_499 = lean::cnstr_get(x_459, 0);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_set(x_459, 0, lean::box(0));
 x_501 = x_459;
} else {
 lean::inc(x_499);
 lean::dec(x_459);
 x_501 = lean::box(0);
}
x_502 = lean::cnstr_get(x_499, 1);
lean::inc(x_502);
lean::dec(x_499);
switch (lean::obj_tag(x_502)) {
case 0:
{
obj* x_507; obj* x_510; obj* x_514; 
lean::dec(x_501);
lean::dec(x_502);
x_507 = lean::cnstr_get(x_360, 1);
lean::inc(x_507);
lean::dec(x_360);
x_510 = lean::cnstr_get(x_456, 0);
lean::inc(x_510);
lean::dec(x_456);
lean::inc(x_3);
x_514 = l___private_init_lean_expander_1__popStxArg(x_507, x_3);
if (lean::obj_tag(x_514) == 0)
{
obj* x_520; obj* x_522; obj* x_523; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_510);
lean::dec(x_348);
lean::dec(x_346);
x_520 = lean::cnstr_get(x_514, 0);
if (lean::is_exclusive(x_514)) {
 x_522 = x_514;
} else {
 lean::inc(x_520);
 lean::dec(x_514);
 x_522 = lean::box(0);
}
if (lean::is_scalar(x_522)) {
 x_523 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_523 = x_522;
}
lean::cnstr_set(x_523, 0, x_520);
return x_523;
}
else
{
obj* x_524; obj* x_527; obj* x_529; obj* x_531; obj* x_532; obj* x_534; obj* x_536; obj* x_537; obj* x_539; obj* x_540; obj* x_543; 
x_524 = lean::cnstr_get(x_514, 0);
lean::inc(x_524);
lean::dec(x_514);
x_527 = lean::cnstr_get(x_524, 0);
x_529 = lean::cnstr_get(x_524, 1);
if (lean::is_exclusive(x_524)) {
 x_531 = x_524;
} else {
 lean::inc(x_527);
 lean::inc(x_529);
 lean::dec(x_524);
 x_531 = lean::box(0);
}
x_532 = lean::cnstr_get(x_529, 0);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_529, 1);
lean::inc(x_534);
if (lean::is_scalar(x_531)) {
 x_536 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_536 = x_531;
}
lean::cnstr_set(x_536, 0, x_510);
lean::cnstr_set(x_536, 1, x_527);
x_537 = lean::cnstr_get(x_529, 2);
lean::inc(x_537);
if (lean::is_scalar(x_348)) {
 x_539 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_539 = x_348;
}
lean::cnstr_set(x_539, 0, x_536);
lean::cnstr_set(x_539, 1, x_537);
x_540 = lean::cnstr_get(x_529, 3);
lean::inc(x_540);
lean::dec(x_529);
x_543 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_543, 0, x_532);
lean::cnstr_set(x_543, 1, x_534);
lean::cnstr_set(x_543, 2, x_539);
lean::cnstr_set(x_543, 3, x_540);
x_1 = x_346;
x_2 = x_543;
goto _start;
}
}
case 2:
{
obj* x_545; obj* x_548; obj* x_551; obj* x_555; 
x_545 = lean::cnstr_get(x_360, 1);
lean::inc(x_545);
lean::dec(x_360);
x_548 = lean::cnstr_get(x_456, 0);
lean::inc(x_548);
lean::dec(x_456);
x_551 = lean::cnstr_get(x_502, 0);
lean::inc(x_551);
lean::dec(x_502);
lean::inc(x_3);
x_555 = l___private_init_lean_expander_1__popStxArg(x_545, x_3);
if (lean::obj_tag(x_555) == 0)
{
obj* x_563; obj* x_565; obj* x_566; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_501);
lean::dec(x_348);
lean::dec(x_346);
lean::dec(x_548);
lean::dec(x_551);
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
obj* x_567; obj* x_570; obj* x_572; 
x_567 = lean::cnstr_get(x_555, 0);
lean::inc(x_567);
lean::dec(x_555);
x_570 = lean::cnstr_get(x_567, 1);
lean::inc(x_570);
x_572 = lean::cnstr_get(x_570, 3);
lean::inc(x_572);
if (lean::obj_tag(x_572) == 0)
{
obj* x_579; obj* x_580; obj* x_582; 
lean::dec(x_348);
lean::dec(x_548);
lean::dec(x_551);
lean::dec(x_567);
lean::inc(x_0);
if (lean::is_scalar(x_501)) {
 x_579 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_579 = x_501;
}
lean::cnstr_set(x_579, 0, x_0);
x_580 = l___private_init_lean_expander_1__popStxArg___closed__1;
lean::inc(x_3);
x_582 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_579, x_580, x_570, x_3);
lean::dec(x_570);
lean::dec(x_579);
if (lean::obj_tag(x_582) == 0)
{
obj* x_588; obj* x_590; obj* x_591; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_588 = lean::cnstr_get(x_582, 0);
if (lean::is_exclusive(x_582)) {
 x_590 = x_582;
} else {
 lean::inc(x_588);
 lean::dec(x_582);
 x_590 = lean::box(0);
}
if (lean::is_scalar(x_590)) {
 x_591 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_591 = x_590;
}
lean::cnstr_set(x_591, 0, x_588);
return x_591;
}
else
{
obj* x_592; obj* x_595; 
x_592 = lean::cnstr_get(x_582, 0);
lean::inc(x_592);
lean::dec(x_582);
x_595 = lean::cnstr_get(x_592, 1);
lean::inc(x_595);
lean::dec(x_592);
x_1 = x_346;
x_2 = x_595;
goto _start;
}
}
else
{
obj* x_600; obj* x_602; obj* x_603; obj* x_605; obj* x_607; obj* x_609; obj* x_610; obj* x_612; obj* x_613; obj* x_616; obj* x_617; obj* x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_627; obj* x_628; obj* x_629; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_638; obj* x_639; obj* x_640; obj* x_641; obj* x_642; 
lean::dec(x_501);
x_600 = lean::cnstr_get(x_567, 0);
if (lean::is_exclusive(x_567)) {
 lean::cnstr_release(x_567, 1);
 x_602 = x_567;
} else {
 lean::inc(x_600);
 lean::dec(x_567);
 x_602 = lean::box(0);
}
x_603 = lean::cnstr_get(x_570, 0);
x_605 = lean::cnstr_get(x_570, 1);
x_607 = lean::cnstr_get(x_570, 2);
if (lean::is_exclusive(x_570)) {
 lean::cnstr_release(x_570, 3);
 x_609 = x_570;
} else {
 lean::inc(x_603);
 lean::inc(x_605);
 lean::inc(x_607);
 lean::dec(x_570);
 x_609 = lean::box(0);
}
x_610 = lean::cnstr_get(x_572, 0);
lean::inc(x_610);
x_612 = l_Lean_Parser_Term_lambda_HasView;
x_613 = lean::cnstr_get(x_612, 1);
lean::inc(x_613);
lean::dec(x_612);
x_616 = lean::box(0);
x_617 = lean::cnstr_get(x_551, 3);
lean::inc(x_617);
x_619 = lean::box(0);
if (lean::is_scalar(x_348)) {
 x_620 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_620 = x_348;
}
lean::cnstr_set(x_620, 0, x_617);
lean::cnstr_set(x_620, 1, x_619);
x_621 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_620);
x_622 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_622, 0, x_621);
lean::cnstr_set(x_622, 1, x_616);
x_623 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_623, 0, x_622);
x_624 = lean::cnstr_get(x_551, 5);
lean::inc(x_624);
lean::dec(x_551);
x_627 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_628 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_629 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_629, 0, x_627);
lean::cnstr_set(x_629, 1, x_623);
lean::cnstr_set(x_629, 2, x_628);
lean::cnstr_set(x_629, 3, x_624);
lean::inc(x_613);
x_631 = lean::apply_1(x_613, x_629);
x_632 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_632, 0, x_627);
lean::cnstr_set(x_632, 1, x_610);
lean::cnstr_set(x_632, 2, x_628);
lean::cnstr_set(x_632, 3, x_600);
x_633 = lean::apply_1(x_613, x_632);
x_634 = l_Lean_Parser_Term_app_HasView;
x_635 = lean::cnstr_get(x_634, 1);
lean::inc(x_635);
lean::dec(x_634);
x_638 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_638, 0, x_631);
lean::cnstr_set(x_638, 1, x_633);
x_639 = lean::apply_1(x_635, x_638);
if (lean::is_scalar(x_602)) {
 x_640 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_640 = x_602;
}
lean::cnstr_set(x_640, 0, x_548);
lean::cnstr_set(x_640, 1, x_639);
x_641 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_641, 0, x_640);
lean::cnstr_set(x_641, 1, x_607);
if (lean::is_scalar(x_609)) {
 x_642 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_642 = x_609;
}
lean::cnstr_set(x_642, 0, x_603);
lean::cnstr_set(x_642, 1, x_605);
lean::cnstr_set(x_642, 2, x_641);
lean::cnstr_set(x_642, 3, x_572);
x_1 = x_346;
x_2 = x_642;
goto _start;
}
}
}
default:
{
obj* x_647; obj* x_651; obj* x_652; obj* x_654; 
lean::dec(x_456);
lean::dec(x_502);
lean::dec(x_348);
x_647 = lean::cnstr_get(x_360, 1);
lean::inc(x_647);
lean::dec(x_360);
lean::inc(x_0);
if (lean::is_scalar(x_501)) {
 x_651 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_651 = x_501;
}
lean::cnstr_set(x_651, 0, x_0);
x_652 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
lean::inc(x_3);
x_654 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_651, x_652, x_647, x_3);
lean::dec(x_647);
lean::dec(x_651);
if (lean::obj_tag(x_654) == 0)
{
obj* x_660; obj* x_662; obj* x_663; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_346);
x_660 = lean::cnstr_get(x_654, 0);
if (lean::is_exclusive(x_654)) {
 x_662 = x_654;
} else {
 lean::inc(x_660);
 lean::dec(x_654);
 x_662 = lean::box(0);
}
if (lean::is_scalar(x_662)) {
 x_663 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_663 = x_662;
}
lean::cnstr_set(x_663, 0, x_660);
return x_663;
}
else
{
obj* x_664; obj* x_667; 
x_664 = lean::cnstr_get(x_654, 0);
lean::inc(x_664);
lean::dec(x_654);
x_667 = lean::cnstr_get(x_664, 1);
lean::inc(x_667);
lean::dec(x_664);
x_1 = x_346;
x_2 = x_667;
goto _start;
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
}
obj* l_Lean_Expander_mkNotationTransformer___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_identUnivs;
x_3 = l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(x_14, x_0);
lean::dec(x_14);
return x_17;
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_0);
x_22 = lean::box(0);
return x_22;
}
}
}
}
obj* l_Lean_Expander_mkNotationTransformer(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
x_7 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_8 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_6, x_7, x_2);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_23; obj* x_25; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
x_17 = lean::box(0);
lean::inc(x_1);
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_13);
lean::cnstr_set(x_19, 2, x_16);
lean::cnstr_set(x_19, 3, x_17);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::dec(x_23);
x_30 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(x_1, x_27, x_19, x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_20);
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
obj* x_37; obj* x_39; obj* x_40; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_43);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1), 2, 1);
lean::closure_set(x_47, 0, x_46);
x_48 = lean::cnstr_get(x_20, 4);
lean::inc(x_48);
lean::dec(x_20);
x_51 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_47, x_48);
if (lean::is_scalar(x_12)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_12;
}
lean::cnstr_set(x_52, 0, x_51);
if (lean::is_scalar(x_39)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_39;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
else
{
obj* x_55; obj* x_57; obj* x_59; 
lean::dec(x_12);
x_55 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 x_57 = x_25;
} else {
 lean::inc(x_55);
 lean::dec(x_25);
 x_57 = lean::box(0);
}
lean::inc(x_2);
x_59 = l___private_init_lean_expander_1__popStxArg(x_19, x_2);
if (lean::obj_tag(x_59) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_57);
lean::dec(x_20);
lean::dec(x_23);
lean::dec(x_55);
x_66 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_68 = x_59;
} else {
 lean::inc(x_66);
 lean::dec(x_59);
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
obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_89; obj* x_90; obj* x_93; 
x_70 = lean::cnstr_get(x_59, 0);
lean::inc(x_70);
lean::dec(x_59);
x_73 = lean::cnstr_get(x_70, 0);
x_75 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_77 = x_70;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 1);
lean::inc(x_80);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_55);
lean::cnstr_set(x_82, 1, x_73);
x_83 = lean::cnstr_get(x_75, 2);
lean::inc(x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_82);
lean::cnstr_set(x_85, 1, x_83);
x_86 = lean::cnstr_get(x_75, 3);
lean::inc(x_86);
lean::dec(x_75);
x_89 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_89, 0, x_78);
lean::cnstr_set(x_89, 1, x_80);
lean::cnstr_set(x_89, 2, x_85);
lean::cnstr_set(x_89, 3, x_86);
x_90 = lean::cnstr_get(x_23, 1);
lean::inc(x_90);
lean::dec(x_23);
x_93 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_1, x_90, x_89, x_2);
if (lean::obj_tag(x_93) == 0)
{
obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_57);
lean::dec(x_20);
x_96 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_98 = x_93;
} else {
 lean::inc(x_96);
 lean::dec(x_93);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_102; obj* x_103; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_114; obj* x_115; obj* x_116; 
x_100 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_102 = x_93;
} else {
 lean::inc(x_100);
 lean::dec(x_93);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = lean::cnstr_get(x_103, 2);
lean::inc(x_106);
lean::dec(x_103);
x_109 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_106);
x_110 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1), 2, 1);
lean::closure_set(x_110, 0, x_109);
x_111 = lean::cnstr_get(x_20, 4);
lean::inc(x_111);
lean::dec(x_20);
x_114 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_110, x_111);
if (lean::is_scalar(x_57)) {
 x_115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_115 = x_57;
}
lean::cnstr_set(x_115, 0, x_114);
if (lean::is_scalar(x_102)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_102;
}
lean::cnstr_set(x_116, 0, x_115);
return x_116;
}
}
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("b");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_7 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_9 = l_Lean_Parser_Substring_ofString(x_7);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_4);
lean::cnstr_set(x_10, 3, x_1);
lean::cnstr_set(x_10, 4, x_1);
return x_10;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("b");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_7 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_9 = l_Lean_Parser_Substring_ofString(x_7);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_4);
lean::cnstr_set(x_10, 3, x_1);
lean::cnstr_set(x_10, 4, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("b");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("b");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
return x_10;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid `infixr` Declaration, given precedence must greater than zero");
return x_0;
}
}
obj* l_Lean_Expander_mixfixToNotationSpec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_10; obj* x_11; 
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = l_Lean_Expander_mixfixToNotationSpec___closed__5;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_17 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_19 = x_5;
} else {
 lean::inc(x_17);
 lean::dec(x_5);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = l_Lean_Expander_mixfixToNotationSpec___closed__6;
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_36; 
lean::dec(x_2);
x_36 = lean::box(0);
x_3 = x_36;
goto lbl_4;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_37 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_39 = x_5;
} else {
 lean::inc(x_37);
 lean::dec(x_5);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_42 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_40);
x_43 = lean::mk_nat_obj(0ul);
x_44 = lean::nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_2);
lean::dec(x_37);
x_47 = lean::mk_nat_obj(1ul);
x_48 = lean::nat_sub(x_42, x_47);
lean::dec(x_42);
x_50 = l_Lean_Parser_number_View_ofNat(x_48);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_53);
if (lean::is_scalar(x_39)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_39;
}
lean::cnstr_set(x_56, 0, x_55);
x_3 = x_56;
goto lbl_4;
}
else
{
obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_42);
x_58 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_37);
if (lean::is_scalar(x_39)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_39;
}
lean::cnstr_set(x_63, 0, x_62);
x_64 = l_Lean_Expander_mixfixToNotationSpec___closed__7;
x_65 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_63, x_64, x_2);
lean::dec(x_63);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_1);
x_68 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_70 = x_65;
} else {
 lean::inc(x_68);
 lean::dec(x_65);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
return x_71;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_65, 0);
lean::inc(x_72);
lean::dec(x_65);
x_3 = x_72;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_5);
lean::dec(x_2);
x_77 = lean::box(0);
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_1);
lean::cnstr_set(x_79, 1, x_77);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
default:
{
obj* x_85; 
lean::dec(x_2);
x_85 = lean::box(0);
x_7 = x_85;
goto lbl_8;
}
}
lbl_4:
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_86 = lean::box(0);
x_87 = l_Lean_Expander_mixfixToNotationSpec___closed__1;
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_3);
x_89 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_1);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_86);
x_93 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_92);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
lbl_8:
{
obj* x_97; 
lean::dec(x_7);
x_97 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_98 = l_Lean_Expander_mixfixToNotationSpec___closed__3;
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_97);
x_101 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_100);
x_103 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
else
{
obj* x_104; obj* x_106; obj* x_107; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_104 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_106 = x_5;
} else {
 lean::inc(x_104);
 lean::dec(x_5);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
x_110 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_110, 0, x_107);
x_111 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_110);
if (lean::is_scalar(x_106)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_106;
}
lean::cnstr_set(x_113, 0, x_112);
x_114 = l_Lean_Expander_mixfixToNotationSpec___closed__1;
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_113);
x_116 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_116, 0, x_115);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_1);
lean::cnstr_set(x_118, 1, x_117);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_97);
x_120 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_119);
x_122 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_122, 0, x_121);
return x_122;
}
}
}
}
obj* l_Lean_Expander_mixfixToNotationSpec___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_mixfixToNotationSpec(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_identUnivs_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::mk_string("a");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string(".");
lean::inc(x_7);
x_10 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
lean::dec(x_8);
x_12 = l_Lean_Parser_Substring_ofString(x_10);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_7);
lean::cnstr_set(x_14, 3, x_13);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_identUnivs_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::mk_string("b");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string(".");
lean::inc(x_8);
x_11 = l_Lean_Name_toStringWithSep___main(x_9, x_8);
lean::dec(x_9);
x_13 = l_Lean_Parser_Substring_ofString(x_11);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_8);
lean::cnstr_set(x_14, 3, x_5);
lean::cnstr_set(x_14, 4, x_5);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("notation");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":=");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_identUnivs_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::mk_string("b");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string(".");
lean::inc(x_7);
x_10 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
lean::dec(x_8);
x_12 = l_Lean_Parser_Substring_ofString(x_10);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_7);
lean::cnstr_set(x_14, 3, x_13);
lean::cnstr_set(x_14, 4, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("`");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Expander_mixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_2 = l_Lean_Parser_command_mixfix_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_11 = x_13;
goto lbl_12;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::box(0);
x_20 = l_Lean_Expander_mixfix_transform___closed__6;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set(x_21, 3, x_19);
x_11 = x_21;
goto lbl_12;
}
lbl_12:
{
obj* x_22; 
x_22 = l_Lean_Expander_mixfixToNotationSpec(x_9, x_11, x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_6);
lean::dec(x_9);
x_25 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_27 = x_22;
} else {
 lean::inc(x_25);
 lean::dec(x_22);
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
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_38; 
x_29 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_31 = x_22;
} else {
 lean::inc(x_29);
 lean::dec(x_22);
 x_31 = lean::box(0);
}
x_32 = l_Lean_Parser_command_notation_HasView;
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::cnstr_get(x_6, 0);
lean::inc(x_36);
switch (lean::obj_tag(x_9)) {
case 0:
{
obj* x_42; obj* x_43; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_9);
lean::dec(x_31);
x_42 = l_Lean_Parser_Term_app_HasView;
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_46 = lean::cnstr_get(x_6, 4);
lean::inc(x_46);
lean::dec(x_6);
x_49 = l_Lean_Expander_mixfix_transform___closed__5;
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::apply_1(x_43, x_50);
x_52 = l_Lean_Expander_mixfix_transform___closed__3;
x_53 = l_Lean_Expander_mixfix_transform___closed__4;
x_54 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_54, 0, x_36);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set(x_54, 2, x_29);
lean::cnstr_set(x_54, 3, x_53);
lean::cnstr_set(x_54, 4, x_51);
x_55 = lean::apply_1(x_33, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
case 4:
{
obj* x_60; obj* x_61; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_9);
lean::dec(x_31);
x_60 = l_Lean_Parser_Term_app_HasView;
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::cnstr_get(x_6, 4);
lean::inc(x_64);
lean::dec(x_6);
x_67 = l_Lean_Expander_mixfix_transform___closed__1;
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::apply_1(x_61, x_68);
x_70 = l_Lean_Expander_mixfix_transform___closed__3;
x_71 = l_Lean_Expander_mixfix_transform___closed__4;
x_72 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_72, 0, x_36);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_29);
lean::cnstr_set(x_72, 3, x_71);
lean::cnstr_set(x_72, 4, x_69);
x_73 = lean::apply_1(x_33, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
default:
{
obj* x_77; 
lean::dec(x_9);
x_77 = lean::box(0);
x_38 = x_77;
goto lbl_39;
}
}
lbl_39:
{
obj* x_79; obj* x_80; obj* x_83; obj* x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_38);
x_79 = l_Lean_Parser_Term_app_HasView;
x_80 = lean::cnstr_get(x_79, 1);
lean::inc(x_80);
lean::dec(x_79);
x_83 = lean::cnstr_get(x_6, 4);
lean::inc(x_83);
lean::dec(x_6);
x_86 = l_Lean_Expander_mixfix_transform___closed__1;
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set(x_87, 1, x_86);
lean::inc(x_80);
x_89 = lean::apply_1(x_80, x_87);
x_90 = l_Lean_Expander_mixfix_transform___closed__2;
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::apply_1(x_80, x_91);
x_93 = l_Lean_Expander_mixfix_transform___closed__3;
x_94 = l_Lean_Expander_mixfix_transform___closed__4;
x_95 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_95, 0, x_36);
lean::cnstr_set(x_95, 1, x_93);
lean::cnstr_set(x_95, 2, x_29);
lean::cnstr_set(x_95, 3, x_94);
lean::cnstr_set(x_95, 4, x_92);
x_96 = lean::apply_1(x_33, x_95);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
if (lean::is_scalar(x_31)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_31;
}
lean::cnstr_set(x_98, 0, x_97);
return x_98;
}
}
}
}
}
obj* _init_l_Lean_Expander_reserveMixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reserve");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_reserveMixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_12; 
x_2 = l_Lean_Parser_command_reserveMixfix_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_Lean_Expander_mixfixToNotationSpec(x_7, x_9, x_1);
lean::dec(x_7);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_16 = x_12;
} else {
 lean::inc(x_14);
 lean::dec(x_12);
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
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
x_21 = l_Lean_Parser_command_reserveNotation_HasView;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_25 = l_Lean_Expander_reserveMixfix_transform___closed__1;
x_26 = l_Lean_Expander_mixfix_transform___closed__3;
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set(x_27, 2, x_18);
x_28 = lean::apply_1(x_22, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_20)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_20;
}
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("}");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x83");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x84");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("[");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("]");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_mkSimpleBinder(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
switch (x_1) {
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Lean_Expander_mkSimpleBinder___closed__2;
x_4 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_5 = l_Lean_Expander_mkSimpleBinder___closed__3;
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_4);
lean::cnstr_set(x_6, 3, x_2);
lean::cnstr_set(x_6, 4, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
case 2:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = l_Lean_Expander_mkSimpleBinder___closed__4;
x_9 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_10 = l_Lean_Expander_mkSimpleBinder___closed__5;
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_11, 3, x_2);
lean::cnstr_set(x_11, 4, x_10);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
case 3:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = l_Lean_Expander_mkSimpleBinder___closed__6;
x_14 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_15 = l_Lean_Expander_mkSimpleBinder___closed__7;
x_16 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_0);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_2);
lean::cnstr_set(x_16, 4, x_15);
x_17 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
default:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_19 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_20 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_21 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_0);
lean::cnstr_set(x_21, 2, x_19);
lean::cnstr_set(x_21, 3, x_2);
lean::cnstr_set(x_21, 4, x_20);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
}
}
obj* l_Lean_Expander_mkSimpleBinder___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_Lean_Expander_mkSimpleBinder(x_0, x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Expander_binderIdentToIdent___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
return x_10;
}
}
obj* l_Lean_Expander_binderIdentToIdent___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = l_Lean_Expander_binderIdentToIdent___main___closed__1;
return x_3;
}
}
}
obj* l_Lean_Expander_binderIdentToIdent___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_binderIdentToIdent___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_binderIdentToIdent(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_binderIdentToIdent___main(x_0);
return x_1;
}
}
obj* l_Lean_Expander_binderIdentToIdent___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_binderIdentToIdent(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Expander_getOptType___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = l_Lean_Parser_Term_hole_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = lean::mk_string("_");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::apply_1(x_1, x_9);
return x_10;
}
}
obj* l_Lean_Expander_getOptType___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Expander_getOptType___main___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Lean_Expander_getOptType___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_getOptType___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Expander_getOptType(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_getOptType___main(x_0);
return x_1;
}
}
obj* l_Lean_Expander_getOptType___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_getOptType(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 0;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 0;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 0;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 0;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 1;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 1;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 1;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 1;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 2;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 2;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 2;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_9 = l_Lean_Expander_binderIdentToIdent___main(x_4);
lean::dec(x_4);
x_11 = 2;
lean::inc(x_0);
x_13 = l_Lean_Expander_mkSimpleBinder(x_9, x_11, x_0);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_Lean_Expander_mkSimpleBinder(x_10, x_0, x_1);
x_14 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("optParam");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("autoParam");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected auto Param after Type annotation");
return x_0;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected anonymous Constructor");
return x_0;
}
}
obj* l_Lean_Expander_expandBracketedBinder___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = l_Lean_Expander_getOptType___main(x_16);
x_19 = lean::cnstr_get(x_13, 2);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_26; obj* x_27; 
lean::dec(x_16);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_26 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(x_18, x_23);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
lean::dec(x_19);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_47; obj* x_48; 
lean::dec(x_16);
lean::dec(x_1);
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
lean::dec(x_28);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_18);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_43 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_42, x_41);
x_44 = lean::cnstr_get(x_13, 0);
lean::inc(x_44);
lean::dec(x_13);
x_47 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(x_43, x_44);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_16) == 0)
{
obj* x_51; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_1);
x_51 = lean::cnstr_get(x_28, 0);
lean::inc(x_51);
lean::dec(x_28);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_60 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_59, x_58);
x_61 = lean::cnstr_get(x_13, 0);
lean::inc(x_61);
lean::dec(x_13);
x_64 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(x_60, x_61);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_66 = x_16;
} else {
 lean::dec(x_16);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Parser_Term_binderDefault_HasView;
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
lean::dec(x_67);
x_71 = lean::apply_1(x_68, x_28);
if (lean::is_scalar(x_66)) {
 x_72 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_72 = x_66;
}
lean::cnstr_set(x_72, 0, x_71);
x_73 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_74 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_72, x_73, x_1);
lean::dec(x_72);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_13);
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
obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_88; 
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_13, 0);
lean::inc(x_84);
lean::dec(x_13);
x_87 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_81, x_84);
if (lean::is_scalar(x_83)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_83;
}
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
}
}
}
}
}
case 1:
{
obj* x_89; obj* x_92; obj* x_95; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_0, 0);
lean::inc(x_89);
lean::dec(x_0);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
x_97 = l_Lean_Expander_getOptType___main(x_95);
x_98 = lean::cnstr_get(x_92, 2);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_102; obj* x_105; obj* x_106; 
lean::dec(x_1);
lean::dec(x_95);
x_102 = lean::cnstr_get(x_92, 0);
lean::inc(x_102);
lean::dec(x_92);
x_105 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(x_97, x_102);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
return x_106;
}
else
{
obj* x_107; 
x_107 = lean::cnstr_get(x_98, 0);
lean::inc(x_107);
lean::dec(x_98);
if (lean::obj_tag(x_107) == 0)
{
obj* x_112; obj* x_115; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_1);
lean::dec(x_95);
x_112 = lean::cnstr_get(x_107, 0);
lean::inc(x_112);
lean::dec(x_107);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
x_118 = lean::box(0);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set(x_119, 1, x_118);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_97);
lean::cnstr_set(x_120, 1, x_119);
x_121 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_122 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_121, x_120);
x_123 = lean::cnstr_get(x_92, 0);
lean::inc(x_123);
lean::dec(x_92);
x_126 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(x_122, x_123);
x_127 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
else
{
lean::dec(x_97);
if (lean::obj_tag(x_95) == 0)
{
obj* x_130; obj* x_133; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_143; obj* x_144; 
lean::dec(x_1);
x_130 = lean::cnstr_get(x_107, 0);
lean::inc(x_130);
lean::dec(x_107);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
x_136 = lean::box(0);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_133);
lean::cnstr_set(x_137, 1, x_136);
x_138 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_139 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_138, x_137);
x_140 = lean::cnstr_get(x_92, 0);
lean::inc(x_140);
lean::dec(x_92);
x_143 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(x_139, x_140);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_143);
return x_144;
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_145 = x_95;
} else {
 lean::dec(x_95);
 x_145 = lean::box(0);
}
x_146 = l_Lean_Parser_Term_binderDefault_HasView;
x_147 = lean::cnstr_get(x_146, 1);
lean::inc(x_147);
lean::dec(x_146);
x_150 = lean::apply_1(x_147, x_107);
if (lean::is_scalar(x_145)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_145;
}
lean::cnstr_set(x_151, 0, x_150);
x_152 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_153 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_151, x_152, x_1);
lean::dec(x_151);
if (lean::obj_tag(x_153) == 0)
{
obj* x_156; obj* x_158; obj* x_159; 
lean::dec(x_92);
x_156 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 x_158 = x_153;
} else {
 lean::inc(x_156);
 lean::dec(x_153);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_156);
return x_159;
}
else
{
obj* x_160; obj* x_162; obj* x_163; obj* x_166; obj* x_167; 
x_160 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 x_162 = x_153;
} else {
 lean::inc(x_160);
 lean::dec(x_153);
 x_162 = lean::box(0);
}
x_163 = lean::cnstr_get(x_92, 0);
lean::inc(x_163);
lean::dec(x_92);
x_166 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_160, x_163);
if (lean::is_scalar(x_162)) {
 x_167 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_167 = x_162;
}
lean::cnstr_set(x_167, 0, x_166);
return x_167;
}
}
}
}
}
case 2:
{
obj* x_168; obj* x_171; obj* x_174; obj* x_176; obj* x_177; 
x_168 = lean::cnstr_get(x_0, 0);
lean::inc(x_168);
lean::dec(x_0);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
lean::dec(x_168);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
x_176 = l_Lean_Expander_getOptType___main(x_174);
x_177 = lean::cnstr_get(x_171, 2);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_181; obj* x_184; obj* x_185; 
lean::dec(x_174);
lean::dec(x_1);
x_181 = lean::cnstr_get(x_171, 0);
lean::inc(x_181);
lean::dec(x_171);
x_184 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(x_176, x_181);
x_185 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_185, 0, x_184);
return x_185;
}
else
{
obj* x_186; 
x_186 = lean::cnstr_get(x_177, 0);
lean::inc(x_186);
lean::dec(x_177);
if (lean::obj_tag(x_186) == 0)
{
obj* x_191; obj* x_194; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_205; obj* x_206; 
lean::dec(x_174);
lean::dec(x_1);
x_191 = lean::cnstr_get(x_186, 0);
lean::inc(x_191);
lean::dec(x_186);
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
lean::dec(x_191);
x_197 = lean::box(0);
x_198 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_198, 0, x_194);
lean::cnstr_set(x_198, 1, x_197);
x_199 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_199, 0, x_176);
lean::cnstr_set(x_199, 1, x_198);
x_200 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_201 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_200, x_199);
x_202 = lean::cnstr_get(x_171, 0);
lean::inc(x_202);
lean::dec(x_171);
x_205 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(x_201, x_202);
x_206 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_206, 0, x_205);
return x_206;
}
else
{
lean::dec(x_176);
if (lean::obj_tag(x_174) == 0)
{
obj* x_209; obj* x_212; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_222; obj* x_223; 
lean::dec(x_1);
x_209 = lean::cnstr_get(x_186, 0);
lean::inc(x_209);
lean::dec(x_186);
x_212 = lean::cnstr_get(x_209, 1);
lean::inc(x_212);
lean::dec(x_209);
x_215 = lean::box(0);
x_216 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_215);
x_217 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_218 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_217, x_216);
x_219 = lean::cnstr_get(x_171, 0);
lean::inc(x_219);
lean::dec(x_171);
x_222 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(x_218, x_219);
x_223 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_223, 0, x_222);
return x_223;
}
else
{
obj* x_224; obj* x_225; obj* x_226; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 x_224 = x_174;
} else {
 lean::dec(x_174);
 x_224 = lean::box(0);
}
x_225 = l_Lean_Parser_Term_binderDefault_HasView;
x_226 = lean::cnstr_get(x_225, 1);
lean::inc(x_226);
lean::dec(x_225);
x_229 = lean::apply_1(x_226, x_186);
if (lean::is_scalar(x_224)) {
 x_230 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_230 = x_224;
}
lean::cnstr_set(x_230, 0, x_229);
x_231 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_232 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_230, x_231, x_1);
lean::dec(x_230);
if (lean::obj_tag(x_232) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_171);
x_235 = lean::cnstr_get(x_232, 0);
if (lean::is_exclusive(x_232)) {
 x_237 = x_232;
} else {
 lean::inc(x_235);
 lean::dec(x_232);
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
obj* x_239; obj* x_241; obj* x_242; obj* x_245; obj* x_246; 
x_239 = lean::cnstr_get(x_232, 0);
if (lean::is_exclusive(x_232)) {
 x_241 = x_232;
} else {
 lean::inc(x_239);
 lean::dec(x_232);
 x_241 = lean::box(0);
}
x_242 = lean::cnstr_get(x_171, 0);
lean::inc(x_242);
lean::dec(x_171);
x_245 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_239, x_242);
if (lean::is_scalar(x_241)) {
 x_246 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_246 = x_241;
}
lean::cnstr_set(x_246, 0, x_245);
return x_246;
}
}
}
}
}
case 3:
{
obj* x_247; obj* x_250; 
x_247 = lean::cnstr_get(x_0, 0);
lean::inc(x_247);
lean::dec(x_0);
x_250 = lean::cnstr_get(x_247, 1);
lean::inc(x_250);
lean::dec(x_247);
if (lean::obj_tag(x_250) == 0)
{
obj* x_253; obj* x_256; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_265; obj* x_266; obj* x_267; obj* x_268; uint8 x_269; obj* x_270; obj* x_271; 
x_253 = lean::cnstr_get(x_250, 0);
lean::inc(x_253);
lean::dec(x_250);
x_256 = lean::cnstr_get(x_253, 0);
lean::inc(x_256);
x_258 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_258, 0, x_256);
x_259 = lean::box(0);
x_260 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_260, 0, x_258);
lean::cnstr_set(x_260, 1, x_259);
x_261 = lean::box(0);
x_262 = lean::cnstr_get(x_253, 2);
lean::inc(x_262);
lean::dec(x_253);
x_265 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_266 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_262);
x_267 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_267, 0, x_266);
x_268 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_268, 0, x_260);
lean::cnstr_set(x_268, 1, x_267);
lean::cnstr_set(x_268, 2, x_261);
x_269 = 3;
x_270 = lean::box(x_269);
x_271 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_268);
x_2 = x_271;
goto lbl_3;
}
else
{
obj* x_272; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; uint8 x_281; obj* x_282; obj* x_283; 
x_272 = lean::cnstr_get(x_250, 0);
lean::inc(x_272);
lean::dec(x_250);
x_275 = lean::box(0);
x_276 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_277 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_272);
x_278 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_278, 0, x_277);
x_279 = l_Lean_Expander_expandBracketedBinder___main___closed__5;
x_280 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_280, 1, x_278);
lean::cnstr_set(x_280, 2, x_275);
x_281 = 3;
x_282 = lean::box(x_281);
x_283 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_283, 0, x_282);
lean::cnstr_set(x_283, 1, x_280);
x_2 = x_283;
goto lbl_3;
}
}
default:
{
obj* x_284; obj* x_287; obj* x_288; obj* x_291; obj* x_292; obj* x_293; obj* x_295; 
x_284 = lean::cnstr_get(x_0, 0);
lean::inc(x_284);
lean::dec(x_0);
x_287 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_288 = lean::cnstr_get(x_287, 1);
lean::inc(x_288);
lean::dec(x_287);
x_291 = lean::apply_1(x_288, x_284);
x_292 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_292, 0, x_291);
x_293 = l_Lean_Expander_expandBracketedBinder___main___closed__6;
lean::inc(x_1);
x_295 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_292, x_293, x_1);
lean::dec(x_292);
if (lean::obj_tag(x_295) == 0)
{
obj* x_298; obj* x_300; obj* x_301; 
lean::dec(x_1);
x_298 = lean::cnstr_get(x_295, 0);
if (lean::is_exclusive(x_295)) {
 x_300 = x_295;
} else {
 lean::inc(x_298);
 lean::dec(x_295);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
return x_301;
}
else
{
obj* x_302; obj* x_304; obj* x_305; obj* x_307; obj* x_310; obj* x_312; obj* x_313; 
x_302 = lean::cnstr_get(x_295, 0);
if (lean::is_exclusive(x_295)) {
 lean::cnstr_set(x_295, 0, lean::box(0));
 x_304 = x_295;
} else {
 lean::inc(x_302);
 lean::dec(x_295);
 x_304 = lean::box(0);
}
x_305 = lean::cnstr_get(x_302, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_302, 1);
lean::inc(x_307);
lean::dec(x_302);
x_310 = lean::cnstr_get(x_307, 1);
lean::inc(x_310);
x_312 = l_Lean_Expander_getOptType___main(x_310);
x_313 = lean::cnstr_get(x_307, 2);
lean::inc(x_313);
if (lean::obj_tag(x_313) == 0)
{
obj* x_317; uint8 x_320; obj* x_321; obj* x_322; 
lean::dec(x_1);
lean::dec(x_310);
x_317 = lean::cnstr_get(x_307, 0);
lean::inc(x_317);
lean::dec(x_307);
x_320 = lean::unbox(x_305);
x_321 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_320, x_312, x_317);
if (lean::is_scalar(x_304)) {
 x_322 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_322 = x_304;
}
lean::cnstr_set(x_322, 0, x_321);
return x_322;
}
else
{
obj* x_323; 
x_323 = lean::cnstr_get(x_313, 0);
lean::inc(x_323);
lean::dec(x_313);
if (lean::obj_tag(x_323) == 0)
{
obj* x_328; obj* x_331; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; uint8 x_342; obj* x_343; obj* x_344; 
lean::dec(x_1);
lean::dec(x_310);
x_328 = lean::cnstr_get(x_323, 0);
lean::inc(x_328);
lean::dec(x_323);
x_331 = lean::cnstr_get(x_328, 1);
lean::inc(x_331);
lean::dec(x_328);
x_334 = lean::box(0);
x_335 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_335, 0, x_331);
lean::cnstr_set(x_335, 1, x_334);
x_336 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_336, 0, x_312);
lean::cnstr_set(x_336, 1, x_335);
x_337 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_338 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_337, x_336);
x_339 = lean::cnstr_get(x_307, 0);
lean::inc(x_339);
lean::dec(x_307);
x_342 = lean::unbox(x_305);
x_343 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_342, x_338, x_339);
if (lean::is_scalar(x_304)) {
 x_344 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_344 = x_304;
}
lean::cnstr_set(x_344, 0, x_343);
return x_344;
}
else
{
lean::dec(x_312);
if (lean::obj_tag(x_310) == 0)
{
obj* x_347; obj* x_350; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; uint8 x_360; obj* x_361; obj* x_362; 
lean::dec(x_1);
x_347 = lean::cnstr_get(x_323, 0);
lean::inc(x_347);
lean::dec(x_323);
x_350 = lean::cnstr_get(x_347, 1);
lean::inc(x_350);
lean::dec(x_347);
x_353 = lean::box(0);
x_354 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_354, 0, x_350);
lean::cnstr_set(x_354, 1, x_353);
x_355 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_356 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_355, x_354);
x_357 = lean::cnstr_get(x_307, 0);
lean::inc(x_357);
lean::dec(x_307);
x_360 = lean::unbox(x_305);
x_361 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_360, x_356, x_357);
if (lean::is_scalar(x_304)) {
 x_362 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_362 = x_304;
}
lean::cnstr_set(x_362, 0, x_361);
return x_362;
}
else
{
obj* x_364; obj* x_365; obj* x_366; obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
lean::dec(x_304);
if (lean::is_exclusive(x_310)) {
 lean::cnstr_release(x_310, 0);
 x_364 = x_310;
} else {
 lean::dec(x_310);
 x_364 = lean::box(0);
}
x_365 = l_Lean_Parser_Term_binderDefault_HasView;
x_366 = lean::cnstr_get(x_365, 1);
lean::inc(x_366);
lean::dec(x_365);
x_369 = lean::apply_1(x_366, x_323);
if (lean::is_scalar(x_364)) {
 x_370 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_370 = x_364;
}
lean::cnstr_set(x_370, 0, x_369);
x_371 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_372 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_370, x_371, x_1);
lean::dec(x_370);
if (lean::obj_tag(x_372) == 0)
{
obj* x_376; obj* x_378; obj* x_379; 
lean::dec(x_305);
lean::dec(x_307);
x_376 = lean::cnstr_get(x_372, 0);
if (lean::is_exclusive(x_372)) {
 x_378 = x_372;
} else {
 lean::inc(x_376);
 lean::dec(x_372);
 x_378 = lean::box(0);
}
if (lean::is_scalar(x_378)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_378;
}
lean::cnstr_set(x_379, 0, x_376);
return x_379;
}
else
{
obj* x_380; obj* x_382; obj* x_383; uint8 x_386; obj* x_387; obj* x_388; 
x_380 = lean::cnstr_get(x_372, 0);
if (lean::is_exclusive(x_372)) {
 x_382 = x_372;
} else {
 lean::inc(x_380);
 lean::dec(x_372);
 x_382 = lean::box(0);
}
x_383 = lean::cnstr_get(x_307, 0);
lean::inc(x_383);
lean::dec(x_307);
x_386 = lean::unbox(x_305);
x_387 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_386, x_380, x_383);
if (lean::is_scalar(x_382)) {
 x_388 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_388 = x_382;
}
lean::cnstr_set(x_388, 0, x_387);
return x_388;
}
}
}
}
}
}
}
lbl_3:
{
obj* x_389; obj* x_391; obj* x_394; obj* x_396; obj* x_397; 
x_389 = lean::cnstr_get(x_2, 0);
lean::inc(x_389);
x_391 = lean::cnstr_get(x_2, 1);
lean::inc(x_391);
lean::dec(x_2);
x_394 = lean::cnstr_get(x_391, 1);
lean::inc(x_394);
x_396 = l_Lean_Expander_getOptType___main(x_394);
x_397 = lean::cnstr_get(x_391, 2);
lean::inc(x_397);
if (lean::obj_tag(x_397) == 0)
{
obj* x_401; uint8 x_404; obj* x_405; obj* x_406; 
lean::dec(x_394);
lean::dec(x_1);
x_401 = lean::cnstr_get(x_391, 0);
lean::inc(x_401);
lean::dec(x_391);
x_404 = lean::unbox(x_389);
x_405 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_404, x_396, x_401);
x_406 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_406, 0, x_405);
return x_406;
}
else
{
obj* x_407; 
x_407 = lean::cnstr_get(x_397, 0);
lean::inc(x_407);
lean::dec(x_397);
if (lean::obj_tag(x_407) == 0)
{
obj* x_412; obj* x_415; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; uint8 x_426; obj* x_427; obj* x_428; 
lean::dec(x_394);
lean::dec(x_1);
x_412 = lean::cnstr_get(x_407, 0);
lean::inc(x_412);
lean::dec(x_407);
x_415 = lean::cnstr_get(x_412, 1);
lean::inc(x_415);
lean::dec(x_412);
x_418 = lean::box(0);
x_419 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_419, 0, x_415);
lean::cnstr_set(x_419, 1, x_418);
x_420 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_420, 0, x_396);
lean::cnstr_set(x_420, 1, x_419);
x_421 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_422 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_421, x_420);
x_423 = lean::cnstr_get(x_391, 0);
lean::inc(x_423);
lean::dec(x_391);
x_426 = lean::unbox(x_389);
x_427 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_426, x_422, x_423);
x_428 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_428, 0, x_427);
return x_428;
}
else
{
lean::dec(x_396);
if (lean::obj_tag(x_394) == 0)
{
obj* x_431; obj* x_434; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_444; obj* x_445; obj* x_446; 
lean::dec(x_1);
x_431 = lean::cnstr_get(x_407, 0);
lean::inc(x_431);
lean::dec(x_407);
x_434 = lean::cnstr_get(x_431, 1);
lean::inc(x_434);
lean::dec(x_431);
x_437 = lean::box(0);
x_438 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_438, 0, x_434);
lean::cnstr_set(x_438, 1, x_437);
x_439 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_440 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_439, x_438);
x_441 = lean::cnstr_get(x_391, 0);
lean::inc(x_441);
lean::dec(x_391);
x_444 = lean::unbox(x_389);
x_445 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_444, x_440, x_441);
x_446 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_446, 0, x_445);
return x_446;
}
else
{
obj* x_447; obj* x_448; obj* x_449; obj* x_452; obj* x_453; obj* x_454; obj* x_455; 
if (lean::is_exclusive(x_394)) {
 lean::cnstr_release(x_394, 0);
 x_447 = x_394;
} else {
 lean::dec(x_394);
 x_447 = lean::box(0);
}
x_448 = l_Lean_Parser_Term_binderDefault_HasView;
x_449 = lean::cnstr_get(x_448, 1);
lean::inc(x_449);
lean::dec(x_448);
x_452 = lean::apply_1(x_449, x_407);
if (lean::is_scalar(x_447)) {
 x_453 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_453 = x_447;
}
lean::cnstr_set(x_453, 0, x_452);
x_454 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_455 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_453, x_454, x_1);
lean::dec(x_453);
if (lean::obj_tag(x_455) == 0)
{
obj* x_459; obj* x_461; obj* x_462; 
lean::dec(x_391);
lean::dec(x_389);
x_459 = lean::cnstr_get(x_455, 0);
if (lean::is_exclusive(x_455)) {
 x_461 = x_455;
} else {
 lean::inc(x_459);
 lean::dec(x_455);
 x_461 = lean::box(0);
}
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_459);
return x_462;
}
else
{
obj* x_463; obj* x_465; obj* x_466; uint8 x_469; obj* x_470; obj* x_471; 
x_463 = lean::cnstr_get(x_455, 0);
if (lean::is_exclusive(x_455)) {
 x_465 = x_455;
} else {
 lean::inc(x_463);
 lean::dec(x_455);
 x_465 = lean::box(0);
}
x_466 = lean::cnstr_get(x_391, 0);
lean::inc(x_466);
lean::dec(x_391);
x_469 = lean::unbox(x_389);
x_470 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_469, x_463, x_466);
if (lean::is_scalar(x_465)) {
 x_471 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_471 = x_465;
}
lean::cnstr_set(x_471, 0, x_470);
return x_471;
}
}
}
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_3, x_1, x_2);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Expander_expandBracketedBinder(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_expandBracketedBinder___main(x_0, x_1);
return x_2;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_0, x_1, x_2, x_8);
x_12 = l_Lean_Expander_binderIdentToIdent___main(x_7);
x_13 = 0;
x_14 = l_Lean_Expander_mkSimpleBinder(x_12, x_13, x_1);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_11);
return x_16;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_0, x_1, x_2, x_8);
x_12 = l_Lean_Expander_binderIdentToIdent___main(x_7);
x_13 = 0;
x_14 = l_Lean_Expander_mkSimpleBinder(x_12, x_13, x_1);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_11);
return x_16;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_0, x_1, x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
x_13 = lean::apply_2(x_0, x_12, x_11);
return x_13;
}
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = l_Lean_Parser_identUnivs_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_3);
x_16 = lean::apply_1(x_12, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_3);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" with ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = l_Lean_Parser_Term_hole_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::mk_string("_");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::apply_1(x_12, x_19);
x_21 = 0;
x_22 = l_Lean_Expander_mkSimpleBinder(x_10, x_21, x_20);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; 
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
lean::inc(x_3);
lean::inc(x_0);
x_14 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_0, x_1, x_9, x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_21 = x_14;
} else {
 lean::inc(x_19);
 lean::dec(x_14);
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
if (lean::obj_tag(x_7) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_29; 
x_23 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_25 = x_14;
} else {
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
lean::dec(x_7);
switch (lean::obj_tag(x_26)) {
case 4:
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_3);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
x_35 = lean::box(0);
x_36 = lean::box(0);
x_37 = l_Lean_Parser_Term_match_HasView;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_41 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_32);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_35);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_36);
x_48 = l_Lean_Expander_mixfix_transform___closed__4;
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set(x_49, 2, x_23);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_35);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_36);
x_52 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_53 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2;
x_54 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_55 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_35);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set(x_55, 4, x_35);
lean::cnstr_set(x_55, 5, x_51);
x_56 = lean::apply_1(x_38, x_55);
x_57 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
x_58 = lean::apply_2(x_0, x_57, x_56);
if (lean::is_scalar(x_25)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_25;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
default:
{
obj* x_62; 
lean::dec(x_11);
lean::dec(x_25);
x_62 = lean::box(0);
x_29 = x_62;
goto lbl_30;
}
}
lbl_30:
{
obj* x_64; 
lean::dec(x_29);
x_64 = l_Lean_Expander_expandBracketedBinder___main(x_26, x_3);
if (lean::obj_tag(x_64) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_0);
lean::dec(x_23);
x_67 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_69 = x_64;
} else {
 lean::inc(x_67);
 lean::dec(x_64);
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
obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
x_71 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_73 = x_64;
} else {
 lean::inc(x_71);
 lean::dec(x_64);
 x_73 = lean::box(0);
}
x_74 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_0, x_23, x_71);
lean::dec(x_23);
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_74);
return x_76;
}
}
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_11);
lean::dec(x_3);
x_79 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_81 = x_14;
} else {
 lean::inc(x_79);
 lean::dec(x_14);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_7, 0);
lean::inc(x_82);
lean::dec(x_7);
x_85 = l_Lean_Expander_binderIdentToIdent___main(x_82);
lean::dec(x_82);
x_87 = 0;
x_88 = l_Lean_Expander_getOptType___main___closed__1;
x_89 = l_Lean_Expander_mkSimpleBinder(x_85, x_87, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::apply_2(x_0, x_90, x_79);
if (lean::is_scalar(x_81)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_81;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
}
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_0, x_1, x_2, x_8);
x_12 = l_Lean_Expander_binderIdentToIdent___main(x_7);
x_13 = 0;
x_14 = l_Lean_Expander_mkSimpleBinder(x_12, x_13, x_1);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_11);
return x_16;
}
}
}
obj* l_Lean_Expander_expandBinders(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_13 = l_Lean_Expander_getOptType___main___closed__1;
x_14 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_0, x_13, x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_21 = x_7;
} else {
 lean::inc(x_19);
 lean::dec(x_7);
 x_21 = lean::box(0);
}
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_26; obj* x_29; obj* x_32; obj* x_35; obj* x_36; 
lean::dec(x_3);
x_23 = lean::cnstr_get(x_19, 0);
lean::inc(x_23);
lean::dec(x_19);
x_26 = lean::cnstr_get(x_4, 0);
lean::inc(x_26);
lean::dec(x_4);
x_29 = lean::cnstr_get(x_23, 1);
lean::inc(x_29);
lean::dec(x_23);
x_32 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_0, x_29, x_2, x_26);
lean::dec(x_26);
lean::dec(x_2);
if (lean::is_scalar(x_21)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_21;
}
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_41; 
x_37 = lean::cnstr_get(x_19, 0);
lean::inc(x_37);
lean::dec(x_19);
lean::inc(x_0);
x_41 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_0, x_2, x_37, x_3);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_4);
lean::dec(x_21);
lean::dec(x_0);
x_45 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_45);
 lean::dec(x_41);
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
obj* x_49; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_60; 
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_4, 0);
lean::inc(x_52);
lean::dec(x_4);
x_55 = l_Lean_Expander_getOptType___main___closed__1;
x_56 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_0, x_55, x_49, x_52);
lean::dec(x_52);
lean::dec(x_49);
if (lean::is_scalar(x_21)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_21;
}
lean::cnstr_set(x_59, 0, x_56);
if (lean::is_scalar(x_51)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_51;
}
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
obj* x_64; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_64 = l_Lean_Expander_noExpansion(x_3);
lean::dec(x_3);
return x_64;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
lean::inc(x_1);
x_10 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
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
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
lean::dec(x_10);
x_21 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_8);
lean::dec(x_18);
x_24 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_26 = x_21;
} else {
 lean::inc(x_24);
 lean::dec(x_21);
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
obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_30 = x_21;
} else {
 lean::inc(x_28);
 lean::dec(x_21);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_8;
}
lean::cnstr_set(x_31, 0, x_18);
lean::cnstr_set(x_31, 1, x_28);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
obj* l_Lean_Expander_bracketedBinders_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_6, x_1);
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
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_15 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
lean::dec(x_2);
x_21 = l_List_join___main___rarg(x_15);
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::apply_1(x_18, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
else
{
obj* x_27; 
lean::dec(x_5);
x_27 = l_Lean_Expander_noExpansion(x_1);
lean::dec(x_1);
return x_27;
}
}
}
obj* l_Lean_Expander_lambda_transform___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = l_Lean_Parser_Term_lambda_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_7 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_7);
lean::cnstr_set(x_8, 3, x_1);
x_9 = lean::apply_1(x_3, x_8);
return x_9;
}
}
obj* _init_l_Lean_Expander_lambda_transform___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_lambda_transform___lambda__1), 2, 0);
return x_0;
}
}
obj* l_Lean_Expander_lambda_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_2 = l_Lean_Parser_Term_lambda_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 3);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_Lean_Expander_lambda_transform___closed__1;
x_13 = l_Lean_Expander_expandBinders(x_12, x_7, x_9, x_1);
return x_13;
}
}
obj* l_Lean_Expander_pi_transform___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_Lean_Parser_Term_pi_HasView;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_10);
lean::cnstr_set(x_11, 3, x_2);
x_12 = lean::apply_1(x_4, x_11);
return x_12;
}
}
obj* l_Lean_Expander_pi_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
x_2 = l_Lean_Parser_Term_pi_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_pi_transform___lambda__1), 3, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 3);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_Lean_Expander_expandBinders(x_8, x_9, x_11, x_1);
return x_14;
}
}
obj* l_coe___at_Lean_Expander_depArrow_transform___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(obj* x_0) {
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
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_4);
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
obj* _init_l_Lean_Expander_depArrow_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xce\xa0");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Expander_depArrow_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_2 = l_Lean_Parser_Term_depArrow_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_Lean_Parser_Term_pi_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_6, 2);
lean::inc(x_20);
lean::dec(x_6);
x_23 = l_Lean_Expander_depArrow_transform___closed__1;
x_24 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_20);
x_26 = lean::apply_1(x_8, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
obj* l_Lean_Expander_depArrow_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_depArrow_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_arrow_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("a");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
return x_10;
}
}
obj* l_Lean_Expander_arrow_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_2 = l_Lean_Parser_Term_arrow_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_Lean_Parser_Term_pi_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_14 = l_Lean_Expander_arrow_transform___closed__1;
x_15 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_16 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set(x_17, 2, x_15);
lean::cnstr_set(x_17, 3, x_11);
lean::cnstr_set(x_17, 4, x_16);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_6, 2);
lean::inc(x_20);
lean::dec(x_6);
x_23 = l_Lean_Expander_depArrow_transform___closed__1;
x_24 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_20);
x_26 = lean::apply_1(x_8, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
obj* l_Lean_Expander_arrow_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_arrow_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_paren_transform___spec__1(obj* x_0) {
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
x_10 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_4);
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
obj* _init_l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Prod");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("mk");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_Lean_Expander_globId(x_4);
return x_5;
}
}
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
} else {
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
lean::inc(x_2);
x_11 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_2, lean::box(0));
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_12 = x_2;
} else {
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
x_17 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_16, x_15);
return x_17;
}
}
}
obj* l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(obj* x_0) {
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
obj* x_2; obj* x_3; 
x_2 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_0, lean::box(0));
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
}
obj* _init_l_Lean_Expander_paren_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Unit");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("unit");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_Lean_Expander_globId(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* _init_l_Lean_Expander_paren_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("typedExpr");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* l_Lean_Expander_paren_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; 
x_2 = l_Lean_Parser_Term_paren_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
x_10 = l_Lean_Expander_paren_transform___closed__1;
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
if (lean::is_scalar(x_13)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_13;
}
lean::cnstr_set(x_19, 0, x_16);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_22; obj* x_24; 
lean::dec(x_13);
x_22 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_24 = x_14;
} else {
 lean::inc(x_22);
 lean::dec(x_14);
 x_24 = lean::box(0);
}
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_24);
x_26 = lean::cnstr_get(x_11, 0);
lean::inc(x_26);
lean::dec(x_11);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_32);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_26);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_39 = lean::cnstr_get(x_11, 0);
lean::inc(x_39);
lean::dec(x_11);
x_42 = lean::cnstr_get(x_22, 0);
lean::inc(x_42);
lean::dec(x_22);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_39);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_45);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_Lean_Expander_paren_transform___closed__2;
x_52 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_51, x_50);
if (lean::is_scalar(x_24)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_24;
}
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_paren_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_paren_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("this");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
return x_10;
}
}
obj* l_Lean_Expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; 
x_2 = l_Lean_Parser_Term_assume_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = l_Lean_Parser_Term_lambda_HasView;
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_6, 3);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_23 = l_Lean_Expander_assume_transform___closed__1;
x_24 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_25 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_26 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set(x_26, 4, x_25);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_30 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_31 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_30);
lean::cnstr_set(x_31, 3, x_13);
x_32 = lean::apply_1(x_10, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_35 = lean::cnstr_get(x_9, 1);
lean::inc(x_35);
lean::dec(x_9);
x_38 = lean::cnstr_get(x_6, 3);
lean::inc(x_38);
lean::dec(x_6);
x_41 = lean::cnstr_get(x_7, 0);
lean::inc(x_41);
lean::dec(x_7);
x_44 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_45 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_41);
lean::cnstr_set(x_46, 2, x_45);
lean::cnstr_set(x_46, 3, x_38);
x_47 = lean::apply_1(x_35, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
}
obj* l_Lean_Expander_assume_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_assume_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ite");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Not");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("dite");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* l_Lean_Expander_if_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; 
x_2 = l_Lean_Parser_Term_if_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 4);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 6);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_Lean_Expander_if_transform___closed__1;
x_21 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_20, x_19);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_24 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_26 = x_7;
} else {
 lean::inc(x_24);
 lean::dec(x_7);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_6, 2);
lean::inc(x_27);
x_29 = l_Lean_Parser_Term_lambda_HasView;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_36 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_37 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_38 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
lean::inc(x_27);
lean::inc(x_33);
x_41 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set(x_41, 1, x_33);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_27);
lean::cnstr_set(x_41, 4, x_38);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::cnstr_get(x_6, 4);
lean::inc(x_44);
x_46 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_47 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_43);
lean::cnstr_set(x_48, 2, x_47);
lean::cnstr_set(x_48, 3, x_44);
lean::inc(x_30);
x_50 = lean::apply_1(x_30, x_48);
x_51 = lean::box(0);
lean::inc(x_27);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_27);
lean::cnstr_set(x_53, 1, x_51);
x_54 = l_Lean_Expander_if_transform___closed__2;
x_55 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_54, x_53);
x_56 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_56, 0, x_36);
lean::cnstr_set(x_56, 1, x_33);
lean::cnstr_set(x_56, 2, x_37);
lean::cnstr_set(x_56, 3, x_55);
lean::cnstr_set(x_56, 4, x_38);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::cnstr_get(x_6, 6);
lean::inc(x_59);
lean::dec(x_6);
x_62 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_62, 0, x_46);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_47);
lean::cnstr_set(x_62, 3, x_59);
x_63 = lean::apply_1(x_30, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_51);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_50);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_27);
lean::cnstr_set(x_66, 1, x_65);
x_67 = l_Lean_Expander_if_transform___closed__3;
x_68 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_67, x_66);
if (lean::is_scalar(x_26)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_26;
}
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
obj* l_Lean_Expander_if_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_if_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_let_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_Term_hole_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::mk_string("_");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::apply_1(x_7, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
obj* l_Lean_Expander_let_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_Lean_Parser_Term_let_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_10 = x_6;
} else {
 lean::inc(x_8);
 lean::dec(x_6);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_15 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_17 = x_8;
} else {
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
x_23 = l_Lean_Expander_let_transform___closed__1;
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_11);
lean::cnstr_set(x_24, 2, x_23);
if (lean::is_scalar(x_10)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_10;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::cnstr_get(x_5, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_5, 3);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_5, 4);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_5, 5);
lean::inc(x_32);
lean::dec(x_5);
x_35 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_25);
lean::cnstr_set(x_35, 2, x_26);
lean::cnstr_set(x_35, 3, x_28);
lean::cnstr_set(x_35, 4, x_30);
lean::cnstr_set(x_35, 5, x_32);
x_36 = lean::apply_1(x_18, x_35);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
else
{
obj* x_43; 
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_5);
x_43 = l_Lean_Expander_noExpansion(x_1);
return x_43;
}
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_44 = lean::cnstr_get(x_8, 0);
x_46 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 1);
 x_48 = x_8;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_8);
 x_48 = lean::box(0);
}
x_49 = lean::box(0);
x_50 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_11);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::cnstr_get(x_2, 1);
lean::inc(x_55);
lean::dec(x_2);
x_58 = lean::cnstr_get(x_5, 0);
lean::inc(x_58);
x_60 = l_Lean_Parser_Term_pi_HasView;
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
lean::dec(x_60);
x_64 = l_Lean_Expander_getOptType___main(x_46);
lean::dec(x_46);
x_66 = l_Lean_Expander_depArrow_transform___closed__1;
x_67 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::inc(x_54);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_54);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_64);
x_70 = lean::apply_1(x_61, x_69);
x_71 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
if (lean::is_scalar(x_48)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_48;
}
lean::cnstr_set(x_74, 0, x_44);
lean::cnstr_set(x_74, 1, x_49);
lean::cnstr_set(x_74, 2, x_73);
if (lean::is_scalar(x_10)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_10;
}
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::cnstr_get(x_5, 2);
lean::inc(x_76);
x_78 = l_Lean_Parser_Term_lambda_HasView;
x_79 = lean::cnstr_get(x_78, 1);
lean::inc(x_79);
lean::dec(x_78);
x_82 = lean::cnstr_get(x_5, 3);
lean::inc(x_82);
x_84 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_54);
lean::cnstr_set(x_85, 2, x_67);
lean::cnstr_set(x_85, 3, x_82);
x_86 = lean::apply_1(x_79, x_85);
x_87 = lean::cnstr_get(x_5, 4);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_5, 5);
lean::inc(x_89);
lean::dec(x_5);
x_92 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_92, 0, x_58);
lean::cnstr_set(x_92, 1, x_75);
lean::cnstr_set(x_92, 2, x_76);
lean::cnstr_set(x_92, 3, x_86);
lean::cnstr_set(x_92, 4, x_87);
lean::cnstr_set(x_92, 5, x_89);
x_93 = lean::apply_1(x_55, x_92);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
else
{
obj* x_96; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_96 = lean::cnstr_get(x_6, 0);
lean::inc(x_96);
lean::dec(x_6);
x_99 = l_Lean_Parser_Term_match_HasView;
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
lean::dec(x_99);
x_103 = lean::box(0);
x_104 = lean::cnstr_get(x_5, 3);
lean::inc(x_104);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_103);
x_107 = lean::box(0);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_107);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_96);
lean::cnstr_set(x_109, 1, x_103);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_107);
x_111 = lean::cnstr_get(x_5, 5);
lean::inc(x_111);
lean::dec(x_5);
x_114 = l_Lean_Expander_mixfix_transform___closed__4;
x_115 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_115, 0, x_110);
lean::cnstr_set(x_115, 1, x_114);
lean::cnstr_set(x_115, 2, x_111);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_103);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_107);
x_118 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_119 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_120 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_108);
lean::cnstr_set(x_120, 2, x_103);
lean::cnstr_set(x_120, 3, x_119);
lean::cnstr_set(x_120, 4, x_103);
lean::cnstr_set(x_120, 5, x_117);
x_121 = lean::apply_1(x_100, x_120);
x_122 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_122, 0, x_121);
x_123 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
return x_123;
}
}
}
obj* l_Lean_Expander_let_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_let_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_axiom_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Expander_axiom_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = l_Lean_Parser_command_axiom_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_17 = x_6;
} else {
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::box(0);
x_22 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_18);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
lean::dec(x_2);
x_30 = l_Lean_Parser_Term_pi_HasView;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::cnstr_get(x_15, 1);
lean::inc(x_34);
lean::dec(x_15);
x_37 = l_Lean_Expander_depArrow_transform___closed__1;
x_38 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_26);
lean::cnstr_set(x_39, 2, x_38);
lean::cnstr_set(x_39, 3, x_34);
x_40 = lean::apply_1(x_31, x_39);
x_41 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_Lean_Expander_axiom_transform___closed__1;
if (lean::is_scalar(x_17)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_17;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
if (lean::is_scalar(x_14)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_14;
}
lean::cnstr_set(x_45, 0, x_10);
lean::cnstr_set(x_45, 1, x_12);
lean::cnstr_set(x_45, 2, x_44);
x_46 = lean::apply_1(x_27, x_45);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
else
{
obj* x_52; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_8);
x_52 = l_Lean_Expander_noExpansion(x_1);
return x_52;
}
}
}
obj* l_Lean_Expander_axiom_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_axiom_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_Declaration_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::box(0);
x_1 = lean::mk_string("class");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
x_13 = lean::mk_string("@[");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::mk_string("]");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_3);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set(x_24, 2, x_22);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
obj* _init_l_Lean_Expander_Declaration_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::mk_string("class");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_Lean_Parser_Substring_ofString(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* _init_l_Lean_Expander_Declaration_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure");
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
obj* l_Lean_Expander_Declaration_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_Lean_Parser_command_Declaration_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
switch (lean::obj_tag(x_6)) {
case 4:
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_10 = x_6;
} else {
 lean::inc(x_8);
 lean::dec(x_6);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; 
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_10);
x_16 = l_Lean_Expander_noExpansion(x_1);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_34; obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_49; obj* x_50; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_17 = x_11;
} else {
 lean::dec(x_11);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_8, 1);
x_20 = lean::cnstr_get(x_8, 2);
x_22 = lean::cnstr_get(x_8, 3);
x_24 = lean::cnstr_get(x_8, 4);
x_26 = lean::cnstr_get(x_8, 5);
x_28 = lean::cnstr_get(x_8, 6);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_8);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_2, 1);
lean::inc(x_36);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_31, 0);
lean::inc(x_39);
x_41 = lean::box(0);
x_42 = lean::cnstr_get(x_31, 2);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_31, 3);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_31, 4);
lean::inc(x_46);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_49 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_49 = x_30;
}
lean::cnstr_set(x_49, 0, x_41);
lean::cnstr_set(x_49, 1, x_18);
lean::cnstr_set(x_49, 2, x_20);
lean::cnstr_set(x_49, 3, x_22);
lean::cnstr_set(x_49, 4, x_24);
lean::cnstr_set(x_49, 5, x_26);
lean::cnstr_set(x_49, 6, x_28);
if (lean::is_scalar(x_10)) {
 x_50 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_50 = x_10;
}
lean::cnstr_set(x_50, 0, x_49);
if (lean::obj_tag(x_34) == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = l_Lean_Expander_Declaration_transform___closed__1;
x_52 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_52, 0, x_39);
lean::cnstr_set(x_52, 1, x_51);
lean::cnstr_set(x_52, 2, x_42);
lean::cnstr_set(x_52, 3, x_44);
lean::cnstr_set(x_52, 4, x_46);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
x_54 = lean::apply_1(x_36, x_53);
if (lean::is_scalar(x_17)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_17;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
else
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_57 = lean::cnstr_get(x_34, 0);
if (lean::is_exclusive(x_34)) {
 x_59 = x_34;
} else {
 lean::inc(x_57);
 lean::dec(x_34);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
x_64 = l_Lean_Expander_Declaration_transform___closed__2;
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_62);
x_66 = lean::cnstr_get(x_57, 2);
lean::inc(x_66);
lean::dec(x_57);
x_69 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_69, 0, x_60);
lean::cnstr_set(x_69, 1, x_65);
lean::cnstr_set(x_69, 2, x_66);
if (lean::is_scalar(x_59)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_59;
}
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_71, 0, x_39);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set(x_71, 2, x_42);
lean::cnstr_set(x_71, 3, x_44);
lean::cnstr_set(x_71, 4, x_46);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_50);
x_73 = lean::apply_1(x_36, x_72);
if (lean::is_scalar(x_17)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_17;
}
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
case 5:
{
obj* x_76; obj* x_78; obj* x_79; 
x_76 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_78 = x_6;
} else {
 lean::inc(x_76);
 lean::dec(x_6);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_85; 
lean::dec(x_5);
lean::dec(x_78);
lean::dec(x_79);
lean::dec(x_76);
x_85 = l_Lean_Expander_noExpansion(x_1);
return x_85;
}
else
{
obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_105; obj* x_107; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_79);
x_87 = lean::cnstr_get(x_76, 1);
x_89 = lean::cnstr_get(x_76, 2);
x_91 = lean::cnstr_get(x_76, 3);
x_93 = lean::cnstr_get(x_76, 4);
x_95 = lean::cnstr_get(x_76, 5);
x_97 = lean::cnstr_get(x_76, 6);
x_99 = lean::cnstr_get(x_76, 7);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 x_101 = x_76;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::inc(x_95);
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_76);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_5, 0);
lean::inc(x_102);
lean::dec(x_5);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 1);
lean::inc(x_107);
lean::dec(x_2);
x_110 = lean::cnstr_get(x_102, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_102, 2);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_102, 3);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_102, 4);
lean::inc(x_116);
lean::dec(x_102);
x_119 = l_Lean_Expander_Declaration_transform___closed__3;
if (lean::is_scalar(x_101)) {
 x_120 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_120 = x_101;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_87);
lean::cnstr_set(x_120, 2, x_89);
lean::cnstr_set(x_120, 3, x_91);
lean::cnstr_set(x_120, 4, x_93);
lean::cnstr_set(x_120, 5, x_95);
lean::cnstr_set(x_120, 6, x_97);
lean::cnstr_set(x_120, 7, x_99);
if (lean::is_scalar(x_78)) {
 x_121 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_121 = x_78;
}
lean::cnstr_set(x_121, 0, x_120);
if (lean::obj_tag(x_105) == 0)
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_122 = l_Lean_Expander_Declaration_transform___closed__1;
x_123 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_123, 0, x_110);
lean::cnstr_set(x_123, 1, x_122);
lean::cnstr_set(x_123, 2, x_112);
lean::cnstr_set(x_123, 3, x_114);
lean::cnstr_set(x_123, 4, x_116);
x_124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_121);
x_125 = lean::apply_1(x_107, x_124);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
x_127 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_127, 0, x_126);
return x_127;
}
else
{
obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_135; obj* x_136; obj* x_137; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_128 = lean::cnstr_get(x_105, 0);
if (lean::is_exclusive(x_105)) {
 x_130 = x_105;
} else {
 lean::inc(x_128);
 lean::dec(x_105);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_128, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
x_135 = l_Lean_Expander_Declaration_transform___closed__2;
x_136 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_133);
x_137 = lean::cnstr_get(x_128, 2);
lean::inc(x_137);
lean::dec(x_128);
x_140 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_140, 0, x_131);
lean::cnstr_set(x_140, 1, x_136);
lean::cnstr_set(x_140, 2, x_137);
if (lean::is_scalar(x_130)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_130;
}
lean::cnstr_set(x_141, 0, x_140);
x_142 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_142, 0, x_110);
lean::cnstr_set(x_142, 1, x_141);
lean::cnstr_set(x_142, 2, x_112);
lean::cnstr_set(x_142, 3, x_114);
lean::cnstr_set(x_142, 4, x_116);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_121);
x_144 = lean::apply_1(x_107, x_143);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
x_146 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_146, 0, x_145);
return x_146;
}
}
}
default:
{
obj* x_149; 
lean::dec(x_6);
lean::dec(x_5);
x_149 = l_Lean_Expander_noExpansion(x_1);
return x_149;
}
}
}
}
obj* l_Lean_Expander_Declaration_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_Declaration_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_introRule_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = l_Lean_Parser_command_introRule_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_16; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_8);
x_16 = l_Lean_Expander_noExpansion(x_1);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_22 = x_10;
} else {
 lean::inc(x_20);
 lean::dec(x_10);
 x_22 = lean::box(0);
}
x_23 = lean::box(0);
x_24 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_17);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::cnstr_get(x_2, 1);
lean::inc(x_29);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_5, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_5, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_5, 2);
lean::inc(x_36);
lean::dec(x_5);
x_39 = l_Lean_Parser_Term_pi_HasView;
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_43 = lean::cnstr_get(x_20, 1);
lean::inc(x_43);
lean::dec(x_20);
x_46 = l_Lean_Expander_depArrow_transform___closed__1;
x_47 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_28);
lean::cnstr_set(x_48, 2, x_47);
lean::cnstr_set(x_48, 3, x_43);
x_49 = lean::apply_1(x_40, x_48);
x_50 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_49);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = l_Lean_Expander_axiom_transform___closed__1;
if (lean::is_scalar(x_12)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_12;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_32);
lean::cnstr_set(x_55, 1, x_34);
lean::cnstr_set(x_55, 2, x_36);
lean::cnstr_set(x_55, 3, x_54);
x_56 = lean::apply_1(x_29, x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
else
{
obj* x_62; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_8);
x_62 = l_Lean_Expander_noExpansion(x_1);
return x_62;
}
}
}
obj* l_Lean_Expander_introRule_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_introRule_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_variable_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("variables");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_variable_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_14; 
x_2 = l_Lean_Parser_command_variable_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_Lean_Parser_command_variables_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::box(0);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_14);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = l_Lean_Expander_variable_transform___closed__1;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::apply_1(x_8, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_25 = lean::cnstr_get(x_11, 0);
lean::inc(x_25);
lean::dec(x_11);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_30 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_14);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = l_Lean_Expander_variable_transform___closed__1;
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::apply_1(x_8, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
}
obj* l_Lean_Expander_variable_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_variable_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Expander");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("bindingAnnotationUpdate");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = l_Lean_Expander_bindingAnnotationUpdate;
x_4 = l_Lean_Parser_Syntax_mkNode(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1;
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
x_8 = l_Lean_Expander_bindingAnnotationUpdate;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
}
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_5);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_5)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_5;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
case 3:
{
obj* x_19; 
lean::dec(x_5);
x_19 = lean::box(0);
return x_19;
}
default:
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_5);
x_22 = lean::box(0);
return x_22;
}
}
}
}
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::mk_string("dummy");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_TermParserM_Monad;
x_10 = l_Lean_Parser_TermParserM_MonadExcept;
x_11 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_12 = l_Lean_Parser_TermParserM_Alternative;
x_13 = l_Lean_Expander_bindingAnnotationUpdate;
x_14 = l_Lean_Expander_bindingAnnotationUpdate_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
lean::dec(x_8);
return x_15;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::mk_string("dummy");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
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
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Expander_bindingAnnotationUpdate;
x_6 = l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Expander_bindingAnnotationUpdate_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::mk_string("dummy");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::apply_1(x_7, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_11);
lean::dec(x_13);
lean::inc(x_1);
x_18 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_1);
x_9 = x_18;
goto lbl_10;
}
else
{
obj* x_19; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; 
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_26 = x_4;
} else {
 lean::dec(x_4);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_11, 0);
x_29 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 1);
 x_31 = x_11;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_11);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 1);
 lean::cnstr_release(x_19, 2);
 x_34 = x_19;
} else {
 lean::inc(x_32);
 lean::dec(x_19);
 x_34 = lean::box(0);
}
x_35 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set(x_36, 2, x_24);
if (lean::is_scalar(x_21)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_21;
}
lean::cnstr_set(x_37, 0, x_36);
if (lean::is_scalar(x_31)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_31;
}
lean::cnstr_set(x_38, 0, x_27);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set(x_38, 2, x_29);
if (lean::is_scalar(x_26)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_26;
}
lean::cnstr_set(x_39, 0, x_38);
lean::inc(x_1);
x_41 = l_Lean_Expander_expandBracketedBinder___main(x_39, x_1);
x_9 = x_41;
goto lbl_10;
}
else
{
obj* x_47; 
lean::dec(x_11);
lean::dec(x_24);
lean::dec(x_19);
lean::dec(x_21);
lean::inc(x_1);
x_47 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_1);
x_9 = x_47;
goto lbl_10;
}
}
else
{
obj* x_53; 
lean::dec(x_22);
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_21);
lean::inc(x_1);
x_53 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_1);
x_9 = x_53;
goto lbl_10;
}
}
}
default:
{
obj* x_55; 
lean::inc(x_1);
x_55 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_1);
x_9 = x_55;
goto lbl_10;
}
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_1);
x_59 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_61 = x_9;
} else {
 lean::inc(x_59);
 lean::dec(x_9);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
return x_62;
}
else
{
obj* x_63; obj* x_66; 
x_63 = lean::cnstr_get(x_9, 0);
lean::inc(x_63);
lean::dec(x_9);
x_66 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_8);
lean::dec(x_63);
x_69 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_71 = x_66;
} else {
 lean::inc(x_69);
 lean::dec(x_66);
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
obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_75 = x_66;
} else {
 lean::inc(x_73);
 lean::dec(x_66);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_8;
}
lean::cnstr_set(x_76, 0, x_63);
lean::cnstr_set(x_76, 1, x_73);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
}
}
}
}
obj* l_Lean_Expander_variables_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_Lean_Parser_command_variables_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_9, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_11);
x_14 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_16 = x_12;
} else {
 lean::inc(x_14);
 lean::dec(x_12);
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
obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
lean::dec(x_2);
x_24 = l_List_join___main___rarg(x_18);
if (lean::is_scalar(x_11)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_Lean_Expander_variable_transform___closed__1;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::apply_1(x_21, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_20)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_20;
}
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_32; 
lean::dec(x_6);
x_32 = l_Lean_Expander_noExpansion(x_1);
lean::dec(x_1);
return x_32;
}
}
}
obj* l_Lean_Expander_Level_leading_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = l_Lean_Parser_Level_leading_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
switch (lean::obj_tag(x_6)) {
case 3:
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
default:
{
obj* x_16; 
lean::dec(x_6);
x_16 = l_Lean_Expander_noExpansion(x_1);
return x_16;
}
}
}
}
obj* l_Lean_Expander_Level_leading_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_Level_leading_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_Subtype_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Subtype");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
return x_3;
}
}
obj* l_Lean_Expander_Subtype_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_2 = l_Lean_Parser_Term_Subtype_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_Lean_Parser_Term_lambda_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
x_15 = l_Lean_Expander_getOptType___main(x_13);
lean::dec(x_13);
x_17 = 0;
x_18 = l_Lean_Expander_mkSimpleBinder(x_11, x_17, x_15);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_6, 4);
lean::inc(x_20);
lean::dec(x_6);
x_23 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_24 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_20);
x_26 = lean::apply_1(x_8, x_25);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Expander_Subtype_transform___closed__1;
x_30 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
obj* l_Lean_Expander_Subtype_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_Subtype_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("universe");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_universes_transform___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_7 = l_Lean_Parser_command_universe_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_2);
x_13 = lean::apply_1(x_8, x_12);
x_14 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_6;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_Lean_Expander_universes_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = l_Lean_Parser_command_universes_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1(x_7);
x_11 = l_Lean_Parser_noKind;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
obj* l_Lean_Expander_universes_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_universes_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_sorry_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::box(0);
x_1 = lean::mk_string("sorryAx");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_Expander_globId(x_2);
x_4 = l_Lean_Parser_Term_hole_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::box(0);
x_9 = lean::mk_string("_");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::apply_1(x_5, x_13);
x_15 = lean::mk_string("Bool");
x_16 = lean_name_mk_string(x_0, x_15);
x_17 = lean::mk_string("false");
x_18 = lean_name_mk_string(x_16, x_17);
x_19 = l_Lean_Expander_globId(x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_3, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
obj* l_Lean_Expander_sorry_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_sorry_transform___closed__1;
return x_2;
}
}
obj* l_Lean_Expander_sorry_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_sorry_transform(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
x_22 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_13, x_1, x_2);
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
x_25 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_7, x_1, x_2);
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
x_44 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_34, x_1, x_2);
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
x_47 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_34, x_1, x_2);
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
x_181 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_28, x_1, x_2);
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
x_184 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_28, x_1, x_2);
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
obj* l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__2(obj* x_0, obj* x_1) {
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
x_13 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_0, x_7, x_9);
x_0 = x_13;
x_1 = x_4;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
x_15 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__1(x_0, x_7, x_9);
x_16 = l_RBNode_setBlack___main___rarg(x_15);
x_0 = x_16;
x_1 = x_4;
goto _start;
}
}
}
}
obj* _init_l_Lean_Expander_builtinTransformers() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_0 = l_Lean_Parser_command_mixfix;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mixfix_transform), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_Lean_Parser_command_reserveMixfix;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_reserveMixfix_transform), 2, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_Term_bracketedBinders;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bracketedBinders_transform), 2, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_Term_lambda;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_lambda_transform), 2, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_Term_pi;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_pi_transform), 2, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_Term_depArrow;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_depArrow_transform___boxed), 2, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_Term_arrow;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_arrow_transform___boxed), 2, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_Term_paren;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_paren_transform___boxed), 2, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_Term_assume;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_assume_transform___boxed), 2, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_Term_if;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_if_transform___boxed), 2, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_Term_let;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_let_transform___boxed), 2, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_Lean_Parser_command_axiom;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_axiom_transform___boxed), 2, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_Declaration;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_Declaration_transform___boxed), 2, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_command_introRule;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_introRule_transform___boxed), 2, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_Parser_command_variable;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_variable_transform___boxed), 2, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_variables;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_variables_transform), 2, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_Level_leading;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_Level_leading_transform___boxed), 2, 0);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_Lean_Parser_Term_Subtype;
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_Subtype_transform___boxed), 2, 0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_Lean_Parser_command_universes;
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_universes_transform___boxed), 2, 0);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_Term_sorry;
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_sorry_transform___boxed), 2, 0);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_56);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_53);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_50);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_47);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_44);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_41);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_38);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_35);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_32);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_29);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_26);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_23);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_20);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_17);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_14);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_11);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_8);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_5);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_2);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::box(0);
x_82 = l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__2(x_81, x_80);
return x_82;
}
}
obj* l_Lean_Expander_ExpanderConfig_HasLift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Expander_ExpanderConfig_HasLift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_ExpanderConfig_HasLift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Expander_ExpanderState_new() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(0ul);
return x_0;
}
}
obj* l_Lean_Expander_mkScope(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_add(x_0, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_mkScope___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_mkScope(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
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
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(obj* x_0, obj* x_1) {
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
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_13 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_1);
 x_13 = lean::box(0);
}
lean::inc(x_3);
lean::inc(x_0);
x_16 = l___private_init_lean_expander_2__expandCore___main(x_0, x_9, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
lean::dec(x_16);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(x_0, x_11, x_30, x_3);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_13);
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
if (lean::is_scalar(x_13)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_13;
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
obj* l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
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
x_9 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_Syntax_flipScopes___main(x_11, x_4);
x_13 = l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(x_0, x_6);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_13 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_1);
 x_13 = lean::box(0);
}
lean::inc(x_3);
lean::inc(x_0);
x_16 = l___private_init_lean_expander_2__expandCore___main(x_0, x_9, x_2, x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
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
obj* x_25; obj* x_28; obj* x_30; obj* x_33; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
lean::dec(x_16);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(x_0, x_11, x_30, x_3);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_13);
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
if (lean::is_scalar(x_13)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_13;
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
obj* _init_l___private_init_lean_expander_2__expandCore___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("macro expansion limit exceeded");
return x_0;
}
}
obj* l___private_init_lean_expander_2__expandCore___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_10; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
lean::inc(x_1);
x_10 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_7);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_2);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_21; obj* x_23; 
lean::dec(x_1);
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(x_19, x_21);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_16, 1);
lean::inc(x_24);
lean::dec(x_16);
x_27 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(x_7, x_24, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_21);
x_29 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_31 = x_27;
} else {
 lean::inc(x_29);
 lean::dec(x_27);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_33 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 0);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_40 = x_33;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_33);
 x_40 = lean::box(0);
}
x_41 = l_Lean_Parser_Syntax_mkNode(x_21, x_36);
if (lean::is_scalar(x_40)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_40;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_38);
if (lean::is_scalar(x_35)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_35;
}
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_23, 0);
lean::inc(x_44);
lean::dec(x_23);
x_47 = l_Lean_Expander_mkScope(x_2, x_3);
if (lean::obj_tag(x_47) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_44);
lean::dec(x_16);
lean::dec(x_21);
x_53 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_55 = x_47;
} else {
 lean::inc(x_53);
 lean::dec(x_47);
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
obj* x_57; obj* x_60; obj* x_62; obj* x_65; obj* x_67; obj* x_68; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_57 = lean::cnstr_get(x_47, 0);
lean::inc(x_57);
lean::dec(x_47);
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
lean::dec(x_57);
x_65 = lean::box(0);
lean::inc(x_60);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_60);
lean::cnstr_set(x_67, 1, x_65);
x_68 = lean::cnstr_get(x_16, 1);
lean::inc(x_68);
lean::dec(x_16);
lean::inc(x_68);
x_72 = l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(x_60, x_68);
lean::inc(x_21);
x_74 = l_Lean_Parser_Syntax_mkNode(x_21, x_72);
x_75 = lean::cnstr_get(x_3, 0);
lean::inc(x_75);
x_77 = lean::apply_2(x_44, x_74, x_75);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_62);
lean::dec(x_67);
lean::dec(x_68);
lean::dec(x_21);
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
obj* x_88; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
lean::dec(x_77);
if (lean::obj_tag(x_88) == 0)
{
obj* x_92; 
lean::dec(x_67);
x_92 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(x_7, x_68, x_62, x_3);
if (lean::obj_tag(x_92) == 0)
{
obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_21);
x_94 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_96 = x_92;
} else {
 lean::inc(x_94);
 lean::dec(x_92);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_98 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_100 = x_92;
} else {
 lean::inc(x_98);
 lean::dec(x_92);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_98, 0);
x_103 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 x_105 = x_98;
} else {
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_98);
 x_105 = lean::box(0);
}
x_106 = l_Lean_Parser_Syntax_mkNode(x_21, x_101);
if (lean::is_scalar(x_105)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_105;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_100)) {
 x_108 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_108 = x_100;
}
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
}
else
{
obj* x_111; obj* x_114; 
lean::dec(x_68);
lean::dec(x_21);
x_111 = lean::cnstr_get(x_88, 0);
lean::inc(x_111);
lean::dec(x_88);
x_114 = l_Lean_Parser_Syntax_flipScopes___main(x_67, x_111);
x_0 = x_7;
x_1 = x_114;
x_2 = x_62;
goto _start;
}
}
}
}
}
}
else
{
obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_0);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_1);
x_118 = l___private_init_lean_expander_2__expandCore___main___closed__1;
x_119 = l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(x_117, x_118, x_2, x_3);
lean::dec(x_2);
lean::dec(x_117);
return x_119;
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_expander_2__expandCore(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_expander_2__expandCore___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Expander_expand(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1000ul);
x_3 = l_Lean_Expander_ExpanderState_new;
x_4 = l___private_init_lean_expander_2__expandCore___main(x_2, x_0, x_3, x_1);
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
obj* x_9; obj* x_11; obj* x_12; obj* x_15; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
if (lean::is_scalar(x_11)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_11;
}
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
}
obj* initialize_init_lean_parser_module(obj*);
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_expander(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
 l_Lean_Expander_TransformM_Monad = _init_l_Lean_Expander_TransformM_Monad();
lean::mark_persistent(l_Lean_Expander_TransformM_Monad);
 l_Lean_Expander_TransformM_MonadReader = _init_l_Lean_Expander_TransformM_MonadReader();
lean::mark_persistent(l_Lean_Expander_TransformM_MonadReader);
 l_Lean_Expander_TransformM_MonadExcept = _init_l_Lean_Expander_TransformM_MonadExcept();
lean::mark_persistent(l_Lean_Expander_TransformM_MonadExcept);
 l_Lean_Expander_noExpansion___closed__1 = _init_l_Lean_Expander_noExpansion___closed__1();
lean::mark_persistent(l_Lean_Expander_noExpansion___closed__1);
 l_Lean_Expander_coeBinderBracketedBinder___closed__1 = _init_l_Lean_Expander_coeBinderBracketedBinder___closed__1();
lean::mark_persistent(l_Lean_Expander_coeBinderBracketedBinder___closed__1);
 l_Lean_Expander_coeBinderBracketedBinder___closed__2 = _init_l_Lean_Expander_coeBinderBracketedBinder___closed__2();
lean::mark_persistent(l_Lean_Expander_coeBinderBracketedBinder___closed__2);
 l___private_init_lean_expander_1__popStxArg___closed__1 = _init_l___private_init_lean_expander_1__popStxArg___closed__1();
lean::mark_persistent(l___private_init_lean_expander_1__popStxArg___closed__1);
 l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1 = _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1();
lean::mark_persistent(l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1);
 l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2 = _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2();
lean::mark_persistent(l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2);
 l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3 = _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3();
lean::mark_persistent(l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3);
 l_Lean_Expander_mixfixToNotationSpec___closed__1 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__1();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__1);
 l_Lean_Expander_mixfixToNotationSpec___closed__2 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__2();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__2);
 l_Lean_Expander_mixfixToNotationSpec___closed__3 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__3();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__3);
 l_Lean_Expander_mixfixToNotationSpec___closed__4 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__4();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__4);
 l_Lean_Expander_mixfixToNotationSpec___closed__5 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__5();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__5);
 l_Lean_Expander_mixfixToNotationSpec___closed__6 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__6();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__6);
 l_Lean_Expander_mixfixToNotationSpec___closed__7 = _init_l_Lean_Expander_mixfixToNotationSpec___closed__7();
lean::mark_persistent(l_Lean_Expander_mixfixToNotationSpec___closed__7);
 l_Lean_Expander_mixfix_transform___closed__1 = _init_l_Lean_Expander_mixfix_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__1);
 l_Lean_Expander_mixfix_transform___closed__2 = _init_l_Lean_Expander_mixfix_transform___closed__2();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__2);
 l_Lean_Expander_mixfix_transform___closed__3 = _init_l_Lean_Expander_mixfix_transform___closed__3();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__3);
 l_Lean_Expander_mixfix_transform___closed__4 = _init_l_Lean_Expander_mixfix_transform___closed__4();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__4);
 l_Lean_Expander_mixfix_transform___closed__5 = _init_l_Lean_Expander_mixfix_transform___closed__5();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__5);
 l_Lean_Expander_mixfix_transform___closed__6 = _init_l_Lean_Expander_mixfix_transform___closed__6();
lean::mark_persistent(l_Lean_Expander_mixfix_transform___closed__6);
 l_Lean_Expander_reserveMixfix_transform___closed__1 = _init_l_Lean_Expander_reserveMixfix_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_reserveMixfix_transform___closed__1);
 l_Lean_Expander_mkSimpleBinder___closed__1 = _init_l_Lean_Expander_mkSimpleBinder___closed__1();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__1);
 l_Lean_Expander_mkSimpleBinder___closed__2 = _init_l_Lean_Expander_mkSimpleBinder___closed__2();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__2);
 l_Lean_Expander_mkSimpleBinder___closed__3 = _init_l_Lean_Expander_mkSimpleBinder___closed__3();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__3);
 l_Lean_Expander_mkSimpleBinder___closed__4 = _init_l_Lean_Expander_mkSimpleBinder___closed__4();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__4);
 l_Lean_Expander_mkSimpleBinder___closed__5 = _init_l_Lean_Expander_mkSimpleBinder___closed__5();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__5);
 l_Lean_Expander_mkSimpleBinder___closed__6 = _init_l_Lean_Expander_mkSimpleBinder___closed__6();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__6);
 l_Lean_Expander_mkSimpleBinder___closed__7 = _init_l_Lean_Expander_mkSimpleBinder___closed__7();
lean::mark_persistent(l_Lean_Expander_mkSimpleBinder___closed__7);
 l_Lean_Expander_binderIdentToIdent___main___closed__1 = _init_l_Lean_Expander_binderIdentToIdent___main___closed__1();
lean::mark_persistent(l_Lean_Expander_binderIdentToIdent___main___closed__1);
 l_Lean_Expander_getOptType___main___closed__1 = _init_l_Lean_Expander_getOptType___main___closed__1();
lean::mark_persistent(l_Lean_Expander_getOptType___main___closed__1);
 l_Lean_Expander_expandBracketedBinder___main___closed__1 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__1();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__1);
 l_Lean_Expander_expandBracketedBinder___main___closed__2 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__2();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__2);
 l_Lean_Expander_expandBracketedBinder___main___closed__3 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__3();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__3);
 l_Lean_Expander_expandBracketedBinder___main___closed__4 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__4();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__4);
 l_Lean_Expander_expandBracketedBinder___main___closed__5 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__5();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__5);
 l_Lean_Expander_expandBracketedBinder___main___closed__6 = _init_l_Lean_Expander_expandBracketedBinder___main___closed__6();
lean::mark_persistent(l_Lean_Expander_expandBracketedBinder___main___closed__6);
 l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1 = _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1();
lean::mark_persistent(l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1);
 l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2 = _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2();
lean::mark_persistent(l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2);
 l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3 = _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3();
lean::mark_persistent(l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3);
 l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4 = _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4();
lean::mark_persistent(l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4);
 l_Lean_Expander_lambda_transform___closed__1 = _init_l_Lean_Expander_lambda_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_lambda_transform___closed__1);
 l_Lean_Expander_depArrow_transform___closed__1 = _init_l_Lean_Expander_depArrow_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_depArrow_transform___closed__1);
 l_Lean_Expander_arrow_transform___closed__1 = _init_l_Lean_Expander_arrow_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_arrow_transform___closed__1);
 l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1 = _init_l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1();
lean::mark_persistent(l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1);
 l_Lean_Expander_paren_transform___closed__1 = _init_l_Lean_Expander_paren_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_paren_transform___closed__1);
 l_Lean_Expander_paren_transform___closed__2 = _init_l_Lean_Expander_paren_transform___closed__2();
lean::mark_persistent(l_Lean_Expander_paren_transform___closed__2);
 l_Lean_Expander_assume_transform___closed__1 = _init_l_Lean_Expander_assume_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_assume_transform___closed__1);
 l_Lean_Expander_if_transform___closed__1 = _init_l_Lean_Expander_if_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_if_transform___closed__1);
 l_Lean_Expander_if_transform___closed__2 = _init_l_Lean_Expander_if_transform___closed__2();
lean::mark_persistent(l_Lean_Expander_if_transform___closed__2);
 l_Lean_Expander_if_transform___closed__3 = _init_l_Lean_Expander_if_transform___closed__3();
lean::mark_persistent(l_Lean_Expander_if_transform___closed__3);
 l_Lean_Expander_let_transform___closed__1 = _init_l_Lean_Expander_let_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_let_transform___closed__1);
 l_Lean_Expander_axiom_transform___closed__1 = _init_l_Lean_Expander_axiom_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_axiom_transform___closed__1);
 l_Lean_Expander_Declaration_transform___closed__1 = _init_l_Lean_Expander_Declaration_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_Declaration_transform___closed__1);
 l_Lean_Expander_Declaration_transform___closed__2 = _init_l_Lean_Expander_Declaration_transform___closed__2();
lean::mark_persistent(l_Lean_Expander_Declaration_transform___closed__2);
 l_Lean_Expander_Declaration_transform___closed__3 = _init_l_Lean_Expander_Declaration_transform___closed__3();
lean::mark_persistent(l_Lean_Expander_Declaration_transform___closed__3);
 l_Lean_Expander_variable_transform___closed__1 = _init_l_Lean_Expander_variable_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_variable_transform___closed__1);
 l_Lean_Expander_bindingAnnotationUpdate = _init_l_Lean_Expander_bindingAnnotationUpdate();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate);
 l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27___elambda__1___closed__1);
 l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27 = _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_HasView_x_27);
 l_Lean_Expander_bindingAnnotationUpdate_HasView = _init_l_Lean_Expander_bindingAnnotationUpdate_HasView();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_HasView);
 l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView = _init_l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView);
 l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1 = _init_l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1);
 l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1 = _init_l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1);
 l_Lean_Expander_Subtype_transform___closed__1 = _init_l_Lean_Expander_Subtype_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_Subtype_transform___closed__1);
 l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1();
lean::mark_persistent(l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1);
 l_Lean_Expander_sorry_transform___closed__1 = _init_l_Lean_Expander_sorry_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_sorry_transform___closed__1);
 l_Lean_Expander_builtinTransformers = _init_l_Lean_Expander_builtinTransformers();
lean::mark_persistent(l_Lean_Expander_builtinTransformers);
 l_Lean_Expander_ExpanderState_new = _init_l_Lean_Expander_ExpanderState_new();
lean::mark_persistent(l_Lean_Expander_ExpanderState_new);
 l___private_init_lean_expander_2__expandCore___main___closed__1 = _init_l___private_init_lean_expander_2__expandCore___main___closed__1();
lean::mark_persistent(l___private_init_lean_expander_2__expandCore___main___closed__1);
return w;
}
