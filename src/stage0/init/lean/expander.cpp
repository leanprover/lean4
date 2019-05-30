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
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(obj*, obj*);
extern obj* l_Lean_Parser_Term_hole_HasView;
obj* l_Lean_Expander_depArrow_transform(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_binderDefault_HasView;
obj* l_Lean_Expander_assume_transform___closed__1;
obj* l_Lean_Expander_lambda_transform___boxed(obj*, obj*);
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
obj* l_Lean_Expander_variables_transform___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_mixfix;
obj* l_Lean_Expander_paren_transform(obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer___lambda__1(obj*, obj*);
extern obj* l_Lean_Parser_command_reserveMixfix_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(uint8, obj*, obj*);
obj* l_Lean_Expander_let_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__1;
obj* l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView;
obj* l_Lean_Expander_coeBinderBracketedBinder(obj*);
obj* l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(obj*, obj*);
obj* l_Lean_Expander_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__2(obj*);
obj* l_Lean_Expander_bracketedBinders_transform___boxed(obj*, obj*);
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
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___boxed(obj*, obj*);
obj* l_Lean_Expander_depArrow_transform___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_expander_2__expandCore___main___closed__1;
obj* l_Lean_Expander_mkSimpleBinder___closed__5;
obj* l_Lean_Expander_Level_leading_transform(obj*, obj*);
obj* l_Lean_Expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_Lean_Expander_TransformM_Monad;
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1(obj*);
extern obj* l_Lean_Parser_Term_bracketedBinders;
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(uint8, obj*, obj*);
obj* l___private_init_lean_expander_1__popStxArg(obj*, obj*);
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
extern obj* l_Lean_Parser_command_declaration_HasView;
extern obj* l_Lean_Parser_command_variables_HasView;
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
obj* l_Lean_Expander_mixfixToNotationSpec___closed__6;
obj* l_coe___at_Lean_Expander_depArrow_transform___spec__1(obj*);
obj* l_ReaderT_read___rarg(obj*, obj*);
obj* l___private_init_lean_expander_2__expandCore(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Expander_pi_transform___boxed(obj*, obj*);
obj* l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(obj*);
extern obj* l_Lean_Parser_Term_depArrow;
extern obj* l_Lean_Parser_command_introRule_HasView;
extern obj* l_Lean_Parser_command_universes_HasView;
obj* l_Lean_Expander_coeBracketedBinderMixedBinder(obj*);
obj* l___private_init_lean_expander_1__popStxArg___boxed(obj*, obj*);
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6___boxed(obj*, obj*);
extern obj* l_Lean_Parser_command_variable_HasView;
obj* l_Lean_Expander_reserveMixfix_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_coeNameIdent(obj*);
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2(obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l_Lean_Expander_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_coeIdentsBindersExt___rarg(obj*, obj*);
obj* l_Lean_Expander_expandBinders___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
obj* l_List_join___main___rarg(obj*);
obj* l_Lean_Expander_mkNotationTransformer___boxed(obj*, obj*, obj*);
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
extern obj* l_Lean_Parser_command_universes;
obj* l_Lean_Expander_error(obj*, obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Expander_getOptType___boxed(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1___boxed(obj*, obj*);
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
obj* l_Lean_Expander_declaration_transform(obj*, obj*);
obj* l_RBNode_insert___at_Lean_Expander_builtinTransformers___spec__1(obj*, obj*, obj*);
obj* l_Lean_Expander_Subtype_transform(obj*, obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
obj* l_Lean_Expander_builtinTransformers;
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1(obj*);
obj* l_Lean_Expander_mixfixToNotationSpec___closed__2;
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___boxed(obj*);
extern obj* l_Lean_Parser_noKind;
extern obj* l_Lean_Parser_Term_lambda_HasView;
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
obj* l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__3(obj*, obj*);
extern obj* l_Lean_Parser_Term_paren;
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2(obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mkNotationTransformer___lambda__1___boxed(obj*, obj*);
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
obj* l_Lean_Expander_declaration_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_declaration_transform___closed__3;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Expander_mkSimpleBinder___closed__6;
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_expandBracketedBinder___boxed(obj*, obj*);
obj* l_Lean_Expander_error___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_identUnivs;
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7___boxed(obj*, obj*);
obj* l_Lean_Expander_ExpanderConfig_HasLift___boxed(obj*);
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
extern obj* l_Lean_Parser_command_notation_HasView;
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8___boxed(obj*, obj*, obj*, obj*);
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
obj* l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(obj*, obj*, obj*);
obj* l_Lean_Expander_bindingAnnotationUpdate;
obj* l_Lean_Expander_lambda_transform(obj*, obj*);
obj* l_Lean_Expander_coeBindersExtBinders(obj*);
obj* l_Lean_Expander_universes_transform(obj*, obj*);
obj* l_Lean_Expander_getOptType___main___boxed(obj*);
extern obj* l_Lean_Parser_command_declaration;
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
obj* l_Lean_Expander_mkSimpleBinder___closed__3;
obj* l_Lean_Expander_introRule_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_declaration_transform___closed__2;
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1(obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(uint8, obj*, obj*);
obj* l_Lean_Expander_depArrow_transform___closed__1;
obj* l_Lean_Expander_expandBracketedBinder___main___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Level_leading_HasView;
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
obj* l_Lean_Expander_pi_transform___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Expander_Subtype_transform___boxed(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3___boxed(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(obj*, obj*);
obj* l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(obj*, obj*);
obj* l_Lean_Expander_declaration_transform___closed__1;
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
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(obj*, obj*);
obj* l_Lean_Expander_variable_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_axiom_transform___boxed(obj*, obj*);
obj* l_Lean_Expander_coeMixedBindersBindersExt___rarg(obj*, obj*);
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
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27;
extern obj* l_Lean_Parser_TermParserM_MonadExcept;
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1;
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(obj*, obj*);
extern obj* l_Lean_Parser_Term_match_HasView;
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(obj*, obj*);
obj* l_Lean_Expander_mixfixToNotationSpec(obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Expander_mkSimpleBinder___closed__4;
obj* l_Lean_Expander_noExpansion___closed__1;
obj* l_Lean_Expander_binderIdentToIdent___main(obj*);
extern obj* l_Lean_Parser_identUnivs_HasView;
obj* l_Lean_Expander_coeIdentsBindersExt(obj*);
extern obj* l_Lean_Parser_Term_if_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19___boxed(obj*, obj*, obj*);
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Expander_mixfix_transform___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(obj*, obj*);
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_NotationSpec_precedence_HasView;
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(uint8, obj*, obj*);
obj* l_Lean_Expander_coeBinderBracketedBinder___boxed(obj*);
extern obj* l_Lean_Parser_Term_binders_HasView;
extern obj* l_Lean_Parser_Term_let_HasView;
obj* l_Lean_Expander_mixfixToNotationSpec___closed__3;
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_command_introRule;
extern obj* l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
extern obj* l_Lean_Parser_Term_pi_HasView;
obj* l_Lean_Expander_expandBracketedBinder(obj*, obj*);
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
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_Expander_transformerConfigCoeFrontendConfig___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_transformerConfigCoeFrontendConfig(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_TransformM_Monad() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad;
x_2 = l_ExceptT_Monad___rarg(x_1);
x_3 = l_ReaderT_Monad___rarg(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_TransformM_MonadReader() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad;
x_2 = l_ExceptT_Monad___rarg(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_read___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_TransformM_MonadExcept() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Id_Monad;
x_2 = l_ExceptT_MonadExcept___rarg(x_1);
x_3 = l_ReaderT_MonadExcept___rarg(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_noExpansion___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Expander_noExpansion(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_noExpansion___closed__1;
return x_2;
}
}
obj* l_Lean_Expander_noExpansion___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_noExpansion(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_error___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_1(x_2, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 2);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_FileMap_toPosition(x_9, x_11);
lean::dec(x_9);
x_13 = 2;
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_14);
lean::cnstr_set(x_15, 4, x_4);
lean::cnstr_set_scalar(x_15, sizeof(void*)*5, x_13);
x_16 = lean::apply_2(x_6, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_3, 0);
x_18 = l_Lean_Parser_Syntax_getPos(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::mk_nat_obj(0u);
x_20 = l_Lean_FileMap_toPosition(x_9, x_19);
lean::dec(x_9);
x_21 = 2;
x_22 = l_String_splitAux___main___closed__1;
x_23 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_23, 0, x_8);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_10);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_23, 4, x_4);
lean::cnstr_set_scalar(x_23, sizeof(void*)*5, x_21);
x_24 = lean::apply_2(x_6, lean::box(0), x_23);
return x_24;
}
else
{
obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_26 = l_Lean_FileMap_toPosition(x_9, x_25);
lean::dec(x_9);
x_27 = 2;
x_28 = l_String_splitAux___main___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_10);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_4);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = lean::apply_2(x_6, lean::box(0), x_29);
return x_30;
}
}
}
}
obj* l_Lean_Expander_error___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_3);
lean::closure_set(x_9, 2, x_6);
lean::closure_set(x_9, 3, x_7);
x_10 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_2, x_9);
return x_10;
}
}
obj* l_Lean_Expander_error(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___rarg), 7, 0);
return x_3;
}
}
obj* l_Lean_Expander_error___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Expander_error___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Expander_error___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_error(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Expander_coeNameIdent(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = l_Lean_Name_toString___closed__1;
lean::inc(x_1);
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_1);
x_5 = l_Lean_Parser_Substring_ofString(x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_1);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
return x_7;
}
}
obj* l_Lean_Expander_globId(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = l_Lean_Parser_identUnivs_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::box(0);
x_5 = l_Lean_Name_toString___closed__1;
lean::inc(x_1);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_1);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_1);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
x_12 = lean::apply_1(x_3, x_11);
return x_12;
}
}
obj* l_Lean_Expander_coeIdentIdentUnivs(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Expander_coeIdentBinderId(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_Lean_Expander_coeIdentsBindersExt___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Expander_coeIdentsBindersExt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_List_map___main___at_Lean_Expander_coeIdentsBindersExt___spec__2___rarg(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Expander_coeIdentsBindersExt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_coeIdentsBindersExt___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Expander_coeBracketedBinderMixedBinder(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_Lean_Expander_coeMixedBindersBindersExt___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Expander_coeMixedBindersBindersExt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::box(0);
x_4 = l_List_map___main___at_Lean_Expander_coeMixedBindersBindersExt___spec__2___rarg(x_1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Expander_coeMixedBindersBindersExt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_coeMixedBindersBindersExt___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Expander_coeBindersExtBinders(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Expander_coeSimpleBinderBinders(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_coeBinderBracketedBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("(");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_coeBinderBracketedBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(")");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_coeBinderBracketedBinder(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_6 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
}
obj* l_Lean_Expander_coeBinderBracketedBinder___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_coeBinderBracketedBinder(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 2);
x_7 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Lean_FileMap_toPosition(x_6, x_8);
x_10 = 2;
x_11 = l_String_splitAux___main___closed__1;
lean::inc(x_5);
x_12 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_7);
lean::cnstr_set(x_12, 3, x_11);
lean::cnstr_set(x_12, 4, x_2);
lean::cnstr_set_scalar(x_12, sizeof(void*)*5, x_10);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = l_Lean_Parser_Syntax_getPos(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Lean_FileMap_toPosition(x_6, x_16);
x_18 = 2;
x_19 = l_String_splitAux___main___closed__1;
lean::inc(x_5);
x_20 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_7);
lean::cnstr_set(x_20, 3, x_19);
lean::cnstr_set(x_20, 4, x_2);
lean::cnstr_set_scalar(x_20, sizeof(void*)*5, x_18);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
lean::dec(x_15);
x_23 = l_Lean_FileMap_toPosition(x_6, x_22);
x_24 = 2;
x_25 = l_String_splitAux___main___closed__1;
lean::inc(x_5);
x_26 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_7);
lean::cnstr_set(x_26, 3, x_25);
lean::cnstr_set(x_26, 4, x_2);
lean::cnstr_set_scalar(x_26, sizeof(void*)*5, x_24);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* _init_l___private_init_lean_expander_1__popStxArg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mkNotationTransformer: unreachable");
return x_1;
}
}
obj* l___private_init_lean_expander_1__popStxArg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_7 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_5, x_6, x_1, x_2);
lean::dec(x_1);
lean::dec(x_5);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 1);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
lean::cnstr_set(x_1, 1, x_11);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_1);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_19, 2, x_15);
lean::cnstr_set(x_19, 3, x_16);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_expander_1__popStxArg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_expander_1__popStxArg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Lean_FileMap_toPosition(x_5, x_7);
x_9 = 2;
x_10 = l_String_splitAux___main___closed__1;
lean::inc(x_4);
x_11 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_10);
lean::cnstr_set(x_11, 4, x_2);
lean::cnstr_set_scalar(x_11, sizeof(void*)*5, x_9);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = l_Lean_Parser_Syntax_getPos(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Lean_FileMap_toPosition(x_5, x_15);
x_17 = 2;
x_18 = l_String_splitAux___main___closed__1;
lean::inc(x_4);
x_19 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_19, 0, x_4);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set(x_19, 2, x_6);
lean::cnstr_set(x_19, 3, x_18);
lean::cnstr_set(x_19, 4, x_2);
lean::cnstr_set_scalar(x_19, sizeof(void*)*5, x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
lean::dec(x_14);
x_22 = l_Lean_FileMap_toPosition(x_5, x_21);
x_23 = 2;
x_24 = l_String_splitAux___main___closed__1;
lean::inc(x_4);
x_25 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_6);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set(x_25, 4, x_2);
lean::cnstr_set_scalar(x_25, sizeof(void*)*5, x_23);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_coe___at_Lean_Expander_mkNotationTransformer___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(obj* x_1) {
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
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mkNotationTransformer: unimplemented");
return x_1;
}
}
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("λ");
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(",");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
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
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_2, 1);
x_13 = lean::cnstr_get(x_2, 0);
lean::dec(x_13);
lean::inc(x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_1);
x_15 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_16 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_3, x_4);
lean::dec(x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_1);
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::dec(x_8);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
lean::dec(x_20);
x_2 = x_12;
x_3 = x_22;
goto _start;
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_21);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::cnstr_get(x_21, 0);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_26; obj* x_27; 
lean::dec(x_25);
lean::dec(x_14);
x_26 = lean::cnstr_get(x_20, 1);
lean::inc(x_26);
lean::dec(x_20);
x_27 = l___private_init_lean_expander_1__popStxArg(x_26, x_4);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
lean::free_heap_obj(x_21);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
lean::dec(x_27);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
lean::dec(x_27);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = !lean::is_exclusive(x_32);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_32, 3);
lean::dec(x_35);
x_36 = l_Lean_Parser_Term_binderIdent_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::apply_1(x_37, x_33);
x_39 = lean::box(0);
lean::cnstr_set(x_2, 1, x_39);
lean::cnstr_set(x_2, 0, x_38);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_21, 0, x_42);
lean::cnstr_set(x_32, 3, x_21);
x_2 = x_12;
x_3 = x_32;
goto _start;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_44 = lean::cnstr_get(x_32, 0);
x_45 = lean::cnstr_get(x_32, 1);
x_46 = lean::cnstr_get(x_32, 2);
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_32);
x_47 = l_Lean_Parser_Term_binderIdent_HasView;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::apply_1(x_48, x_33);
x_50 = lean::box(0);
lean::cnstr_set(x_2, 1, x_50);
lean::cnstr_set(x_2, 0, x_49);
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_2);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_21, 0, x_53);
x_54 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_54, 0, x_44);
lean::cnstr_set(x_54, 1, x_45);
lean::cnstr_set(x_54, 2, x_46);
lean::cnstr_set(x_54, 3, x_21);
x_2 = x_12;
x_3 = x_54;
goto _start;
}
}
}
case 1:
{
obj* x_56; obj* x_57; 
lean::dec(x_25);
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_56 = lean::cnstr_get(x_20, 1);
lean::inc(x_56);
lean::dec(x_20);
x_57 = l___private_init_lean_expander_1__popStxArg(x_56, x_4);
if (lean::obj_tag(x_57) == 0)
{
uint8 x_58; 
lean::free_heap_obj(x_21);
lean::dec(x_12);
lean::dec(x_1);
x_58 = !lean::is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
obj* x_59; obj* x_60; 
x_59 = lean::cnstr_get(x_57, 0);
lean::inc(x_59);
lean::dec(x_57);
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; uint8 x_64; 
x_61 = lean::cnstr_get(x_57, 0);
lean::inc(x_61);
lean::dec(x_57);
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
lean::dec(x_61);
x_64 = !lean::is_exclusive(x_62);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_62, 3);
lean::dec(x_65);
x_66 = l_Lean_Parser_Term_binders_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::apply_1(x_67, x_63);
lean::cnstr_set(x_21, 0, x_68);
lean::cnstr_set(x_62, 3, x_21);
x_2 = x_12;
x_3 = x_62;
goto _start;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_70 = lean::cnstr_get(x_62, 0);
x_71 = lean::cnstr_get(x_62, 1);
x_72 = lean::cnstr_get(x_62, 2);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_62);
x_73 = l_Lean_Parser_Term_binders_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::apply_1(x_74, x_63);
lean::cnstr_set(x_21, 0, x_75);
x_76 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_76, 0, x_70);
lean::cnstr_set(x_76, 1, x_71);
lean::cnstr_set(x_76, 2, x_72);
lean::cnstr_set(x_76, 3, x_21);
x_2 = x_12;
x_3 = x_76;
goto _start;
}
}
}
default: 
{
obj* x_78; obj* x_79; 
lean::free_heap_obj(x_21);
x_78 = lean::cnstr_get(x_25, 0);
lean::inc(x_78);
lean::dec(x_25);
x_79 = lean::cnstr_get(x_78, 1);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_14);
x_80 = lean::cnstr_get(x_20, 1);
lean::inc(x_80);
lean::dec(x_20);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
x_82 = l___private_init_lean_expander_1__popStxArg(x_80, x_4);
if (lean::obj_tag(x_82) == 0)
{
uint8 x_83; 
lean::dec(x_81);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_83 = !lean::is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
}
else
{
obj* x_86; uint8 x_87; 
x_86 = lean::cnstr_get(x_82, 0);
lean::inc(x_86);
lean::dec(x_82);
x_87 = !lean::is_exclusive(x_86);
if (x_87 == 0)
{
obj* x_88; uint8 x_89; 
x_88 = lean::cnstr_get(x_86, 1);
x_89 = !lean::is_exclusive(x_88);
if (x_89 == 0)
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_86, 0);
x_91 = lean::cnstr_get(x_88, 2);
lean::cnstr_set(x_86, 1, x_90);
lean::cnstr_set(x_86, 0, x_81);
lean::cnstr_set(x_2, 1, x_91);
lean::cnstr_set(x_2, 0, x_86);
lean::cnstr_set(x_88, 2, x_2);
x_2 = x_12;
x_3 = x_88;
goto _start;
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_93 = lean::cnstr_get(x_86, 0);
x_94 = lean::cnstr_get(x_88, 0);
x_95 = lean::cnstr_get(x_88, 1);
x_96 = lean::cnstr_get(x_88, 2);
x_97 = lean::cnstr_get(x_88, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_88);
lean::cnstr_set(x_86, 1, x_93);
lean::cnstr_set(x_86, 0, x_81);
lean::cnstr_set(x_2, 1, x_96);
lean::cnstr_set(x_2, 0, x_86);
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set(x_98, 2, x_2);
lean::cnstr_set(x_98, 3, x_97);
x_2 = x_12;
x_3 = x_98;
goto _start;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_100 = lean::cnstr_get(x_86, 1);
x_101 = lean::cnstr_get(x_86, 0);
lean::inc(x_100);
lean::inc(x_101);
lean::dec(x_86);
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_100, 2);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_100, 3);
lean::inc(x_105);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 lean::cnstr_release(x_100, 2);
 lean::cnstr_release(x_100, 3);
 x_106 = x_100;
} else {
 lean::dec_ref(x_100);
 x_106 = lean::box(0);
}
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_81);
lean::cnstr_set(x_107, 1, x_101);
lean::cnstr_set(x_2, 1, x_104);
lean::cnstr_set(x_2, 0, x_107);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_102);
lean::cnstr_set(x_108, 1, x_103);
lean::cnstr_set(x_108, 2, x_2);
lean::cnstr_set(x_108, 3, x_105);
x_2 = x_12;
x_3 = x_108;
goto _start;
}
}
}
else
{
obj* x_110; obj* x_111; 
x_110 = lean::cnstr_get(x_79, 0);
lean::inc(x_110);
lean::dec(x_79);
x_111 = lean::cnstr_get(x_110, 1);
lean::inc(x_111);
lean::dec(x_110);
switch (lean::obj_tag(x_111)) {
case 0:
{
obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_111);
lean::dec(x_14);
x_112 = lean::cnstr_get(x_20, 1);
lean::inc(x_112);
lean::dec(x_20);
x_113 = lean::cnstr_get(x_78, 0);
lean::inc(x_113);
lean::dec(x_78);
x_114 = l___private_init_lean_expander_1__popStxArg(x_112, x_4);
if (lean::obj_tag(x_114) == 0)
{
uint8 x_115; 
lean::dec(x_113);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_115 = !lean::is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
lean::dec(x_114);
x_117 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
return x_117;
}
}
else
{
obj* x_118; uint8 x_119; 
x_118 = lean::cnstr_get(x_114, 0);
lean::inc(x_118);
lean::dec(x_114);
x_119 = !lean::is_exclusive(x_118);
if (x_119 == 0)
{
obj* x_120; uint8 x_121; 
x_120 = lean::cnstr_get(x_118, 1);
x_121 = !lean::is_exclusive(x_120);
if (x_121 == 0)
{
obj* x_122; obj* x_123; 
x_122 = lean::cnstr_get(x_118, 0);
x_123 = lean::cnstr_get(x_120, 2);
lean::cnstr_set(x_118, 1, x_122);
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_2, 1, x_123);
lean::cnstr_set(x_2, 0, x_118);
lean::cnstr_set(x_120, 2, x_2);
x_2 = x_12;
x_3 = x_120;
goto _start;
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_125 = lean::cnstr_get(x_118, 0);
x_126 = lean::cnstr_get(x_120, 0);
x_127 = lean::cnstr_get(x_120, 1);
x_128 = lean::cnstr_get(x_120, 2);
x_129 = lean::cnstr_get(x_120, 3);
lean::inc(x_129);
lean::inc(x_128);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_120);
lean::cnstr_set(x_118, 1, x_125);
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_2, 1, x_128);
lean::cnstr_set(x_2, 0, x_118);
x_130 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set(x_130, 1, x_127);
lean::cnstr_set(x_130, 2, x_2);
lean::cnstr_set(x_130, 3, x_129);
x_2 = x_12;
x_3 = x_130;
goto _start;
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_132 = lean::cnstr_get(x_118, 1);
x_133 = lean::cnstr_get(x_118, 0);
lean::inc(x_132);
lean::inc(x_133);
lean::dec(x_118);
x_134 = lean::cnstr_get(x_132, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_132, 2);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_132, 3);
lean::inc(x_137);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 lean::cnstr_release(x_132, 2);
 lean::cnstr_release(x_132, 3);
 x_138 = x_132;
} else {
 lean::dec_ref(x_132);
 x_138 = lean::box(0);
}
x_139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_139, 0, x_113);
lean::cnstr_set(x_139, 1, x_133);
lean::cnstr_set(x_2, 1, x_136);
lean::cnstr_set(x_2, 0, x_139);
if (lean::is_scalar(x_138)) {
 x_140 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_140 = x_138;
}
lean::cnstr_set(x_140, 0, x_134);
lean::cnstr_set(x_140, 1, x_135);
lean::cnstr_set(x_140, 2, x_2);
lean::cnstr_set(x_140, 3, x_137);
x_2 = x_12;
x_3 = x_140;
goto _start;
}
}
}
case 2:
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_142 = lean::cnstr_get(x_20, 1);
lean::inc(x_142);
lean::dec(x_20);
x_143 = lean::cnstr_get(x_78, 0);
lean::inc(x_143);
lean::dec(x_78);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
lean::dec(x_111);
x_145 = l___private_init_lean_expander_1__popStxArg(x_142, x_4);
if (lean::obj_tag(x_145) == 0)
{
uint8 x_146; 
lean::dec(x_144);
lean::dec(x_143);
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_146 = !lean::is_exclusive(x_145);
if (x_146 == 0)
{
return x_145;
}
else
{
obj* x_147; obj* x_148; 
x_147 = lean::cnstr_get(x_145, 0);
lean::inc(x_147);
lean::dec(x_145);
x_148 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_148, 0, x_147);
return x_148;
}
}
else
{
obj* x_149; obj* x_150; obj* x_151; 
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
lean::dec(x_145);
x_150 = lean::cnstr_get(x_149, 1);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_150, 3);
lean::inc(x_151);
if (lean::obj_tag(x_151) == 0)
{
obj* x_152; 
lean::dec(x_149);
lean::dec(x_144);
lean::dec(x_143);
lean::free_heap_obj(x_2);
x_152 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_150, x_4);
lean::dec(x_150);
lean::dec(x_14);
if (lean::obj_tag(x_152) == 0)
{
uint8 x_153; 
lean::dec(x_12);
lean::dec(x_1);
x_153 = !lean::is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
obj* x_154; obj* x_155; 
x_154 = lean::cnstr_get(x_152, 0);
lean::inc(x_154);
lean::dec(x_152);
x_155 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
return x_155;
}
}
else
{
obj* x_156; obj* x_157; 
x_156 = lean::cnstr_get(x_152, 0);
lean::inc(x_156);
lean::dec(x_152);
x_157 = lean::cnstr_get(x_156, 1);
lean::inc(x_157);
lean::dec(x_156);
x_2 = x_12;
x_3 = x_157;
goto _start;
}
}
else
{
uint8 x_159; 
lean::dec(x_14);
x_159 = !lean::is_exclusive(x_149);
if (x_159 == 0)
{
obj* x_160; obj* x_161; uint8 x_162; 
x_160 = lean::cnstr_get(x_149, 0);
x_161 = lean::cnstr_get(x_149, 1);
lean::dec(x_161);
x_162 = !lean::is_exclusive(x_150);
if (x_162 == 0)
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_163 = lean::cnstr_get(x_150, 2);
x_164 = lean::cnstr_get(x_150, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_151, 0);
lean::inc(x_165);
x_166 = l_Lean_Parser_Term_lambda_HasView;
x_167 = lean::cnstr_get(x_166, 1);
lean::inc(x_167);
x_168 = lean::box(0);
x_169 = lean::cnstr_get(x_144, 3);
lean::inc(x_169);
x_170 = lean::box(0);
lean::cnstr_set(x_2, 1, x_170);
lean::cnstr_set(x_2, 0, x_169);
x_171 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_172 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_168);
x_173 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_173, 0, x_172);
x_174 = lean::cnstr_get(x_144, 5);
lean::inc(x_174);
lean::dec(x_144);
x_175 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_176 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_177 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_177, 0, x_175);
lean::cnstr_set(x_177, 1, x_173);
lean::cnstr_set(x_177, 2, x_176);
lean::cnstr_set(x_177, 3, x_174);
lean::inc(x_167);
x_178 = lean::apply_1(x_167, x_177);
x_179 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_179, 0, x_175);
lean::cnstr_set(x_179, 1, x_165);
lean::cnstr_set(x_179, 2, x_176);
lean::cnstr_set(x_179, 3, x_160);
x_180 = lean::apply_1(x_167, x_179);
x_181 = l_Lean_Parser_Term_app_HasView;
x_182 = lean::cnstr_get(x_181, 1);
lean::inc(x_182);
x_183 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_183, 0, x_178);
lean::cnstr_set(x_183, 1, x_180);
x_184 = lean::apply_1(x_182, x_183);
lean::cnstr_set(x_149, 1, x_184);
lean::cnstr_set(x_149, 0, x_143);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_149);
lean::cnstr_set(x_185, 1, x_163);
lean::cnstr_set(x_150, 2, x_185);
x_2 = x_12;
x_3 = x_150;
goto _start;
}
else
{
obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_187 = lean::cnstr_get(x_150, 0);
x_188 = lean::cnstr_get(x_150, 1);
x_189 = lean::cnstr_get(x_150, 2);
lean::inc(x_189);
lean::inc(x_188);
lean::inc(x_187);
lean::dec(x_150);
x_190 = lean::cnstr_get(x_151, 0);
lean::inc(x_190);
x_191 = l_Lean_Parser_Term_lambda_HasView;
x_192 = lean::cnstr_get(x_191, 1);
lean::inc(x_192);
x_193 = lean::box(0);
x_194 = lean::cnstr_get(x_144, 3);
lean::inc(x_194);
x_195 = lean::box(0);
lean::cnstr_set(x_2, 1, x_195);
lean::cnstr_set(x_2, 0, x_194);
x_196 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_197 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_193);
x_198 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_198, 0, x_197);
x_199 = lean::cnstr_get(x_144, 5);
lean::inc(x_199);
lean::dec(x_144);
x_200 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_201 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_202 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_198);
lean::cnstr_set(x_202, 2, x_201);
lean::cnstr_set(x_202, 3, x_199);
lean::inc(x_192);
x_203 = lean::apply_1(x_192, x_202);
x_204 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_204, 0, x_200);
lean::cnstr_set(x_204, 1, x_190);
lean::cnstr_set(x_204, 2, x_201);
lean::cnstr_set(x_204, 3, x_160);
x_205 = lean::apply_1(x_192, x_204);
x_206 = l_Lean_Parser_Term_app_HasView;
x_207 = lean::cnstr_get(x_206, 1);
lean::inc(x_207);
x_208 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_208, 0, x_203);
lean::cnstr_set(x_208, 1, x_205);
x_209 = lean::apply_1(x_207, x_208);
lean::cnstr_set(x_149, 1, x_209);
lean::cnstr_set(x_149, 0, x_143);
x_210 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_210, 0, x_149);
lean::cnstr_set(x_210, 1, x_189);
x_211 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_211, 0, x_187);
lean::cnstr_set(x_211, 1, x_188);
lean::cnstr_set(x_211, 2, x_210);
lean::cnstr_set(x_211, 3, x_151);
x_2 = x_12;
x_3 = x_211;
goto _start;
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
x_213 = lean::cnstr_get(x_149, 0);
lean::inc(x_213);
lean::dec(x_149);
x_214 = lean::cnstr_get(x_150, 0);
lean::inc(x_214);
x_215 = lean::cnstr_get(x_150, 1);
lean::inc(x_215);
x_216 = lean::cnstr_get(x_150, 2);
lean::inc(x_216);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_release(x_150, 0);
 lean::cnstr_release(x_150, 1);
 lean::cnstr_release(x_150, 2);
 lean::cnstr_release(x_150, 3);
 x_217 = x_150;
} else {
 lean::dec_ref(x_150);
 x_217 = lean::box(0);
}
x_218 = lean::cnstr_get(x_151, 0);
lean::inc(x_218);
x_219 = l_Lean_Parser_Term_lambda_HasView;
x_220 = lean::cnstr_get(x_219, 1);
lean::inc(x_220);
x_221 = lean::box(0);
x_222 = lean::cnstr_get(x_144, 3);
lean::inc(x_222);
x_223 = lean::box(0);
lean::cnstr_set(x_2, 1, x_223);
lean::cnstr_set(x_2, 0, x_222);
x_224 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_225 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_225, 0, x_224);
lean::cnstr_set(x_225, 1, x_221);
x_226 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_226, 0, x_225);
x_227 = lean::cnstr_get(x_144, 5);
lean::inc(x_227);
lean::dec(x_144);
x_228 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_229 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_230 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_230, 0, x_228);
lean::cnstr_set(x_230, 1, x_226);
lean::cnstr_set(x_230, 2, x_229);
lean::cnstr_set(x_230, 3, x_227);
lean::inc(x_220);
x_231 = lean::apply_1(x_220, x_230);
x_232 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_232, 0, x_228);
lean::cnstr_set(x_232, 1, x_218);
lean::cnstr_set(x_232, 2, x_229);
lean::cnstr_set(x_232, 3, x_213);
x_233 = lean::apply_1(x_220, x_232);
x_234 = l_Lean_Parser_Term_app_HasView;
x_235 = lean::cnstr_get(x_234, 1);
lean::inc(x_235);
x_236 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_236, 0, x_231);
lean::cnstr_set(x_236, 1, x_233);
x_237 = lean::apply_1(x_235, x_236);
x_238 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_238, 0, x_143);
lean::cnstr_set(x_238, 1, x_237);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_216);
if (lean::is_scalar(x_217)) {
 x_240 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_240 = x_217;
}
lean::cnstr_set(x_240, 0, x_214);
lean::cnstr_set(x_240, 1, x_215);
lean::cnstr_set(x_240, 2, x_239);
lean::cnstr_set(x_240, 3, x_151);
x_2 = x_12;
x_3 = x_240;
goto _start;
}
}
}
}
default: 
{
obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_111);
lean::dec(x_78);
lean::free_heap_obj(x_2);
x_242 = lean::cnstr_get(x_20, 1);
lean::inc(x_242);
lean::dec(x_20);
x_243 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_244 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_243, x_242, x_4);
lean::dec(x_242);
lean::dec(x_14);
if (lean::obj_tag(x_244) == 0)
{
uint8 x_245; 
lean::dec(x_12);
lean::dec(x_1);
x_245 = !lean::is_exclusive(x_244);
if (x_245 == 0)
{
return x_244;
}
else
{
obj* x_246; obj* x_247; 
x_246 = lean::cnstr_get(x_244, 0);
lean::inc(x_246);
lean::dec(x_244);
x_247 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_247, 0, x_246);
return x_247;
}
}
else
{
obj* x_248; obj* x_249; 
x_248 = lean::cnstr_get(x_244, 0);
lean::inc(x_248);
lean::dec(x_244);
x_249 = lean::cnstr_get(x_248, 1);
lean::inc(x_249);
lean::dec(x_248);
x_2 = x_12;
x_3 = x_249;
goto _start;
}
}
}
}
}
}
}
else
{
obj* x_251; 
x_251 = lean::cnstr_get(x_21, 0);
lean::inc(x_251);
lean::dec(x_21);
switch (lean::obj_tag(x_251)) {
case 0:
{
obj* x_252; obj* x_253; 
lean::dec(x_251);
lean::dec(x_14);
x_252 = lean::cnstr_get(x_20, 1);
lean::inc(x_252);
lean::dec(x_20);
x_253 = l___private_init_lean_expander_1__popStxArg(x_252, x_4);
if (lean::obj_tag(x_253) == 0)
{
obj* x_254; obj* x_255; obj* x_256; 
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
if (lean::is_exclusive(x_253)) {
 lean::cnstr_release(x_253, 0);
 x_255 = x_253;
} else {
 lean::dec_ref(x_253);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_254);
return x_256;
}
else
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_257 = lean::cnstr_get(x_253, 0);
lean::inc(x_257);
lean::dec(x_253);
x_258 = lean::cnstr_get(x_257, 1);
lean::inc(x_258);
x_259 = lean::cnstr_get(x_257, 0);
lean::inc(x_259);
lean::dec(x_257);
x_260 = lean::cnstr_get(x_258, 0);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
x_262 = lean::cnstr_get(x_258, 2);
lean::inc(x_262);
if (lean::is_exclusive(x_258)) {
 lean::cnstr_release(x_258, 0);
 lean::cnstr_release(x_258, 1);
 lean::cnstr_release(x_258, 2);
 lean::cnstr_release(x_258, 3);
 x_263 = x_258;
} else {
 lean::dec_ref(x_258);
 x_263 = lean::box(0);
}
x_264 = l_Lean_Parser_Term_binderIdent_HasView;
x_265 = lean::cnstr_get(x_264, 0);
lean::inc(x_265);
x_266 = lean::apply_1(x_265, x_259);
x_267 = lean::box(0);
lean::cnstr_set(x_2, 1, x_267);
lean::cnstr_set(x_2, 0, x_266);
x_268 = lean::box(0);
x_269 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_269, 0, x_2);
lean::cnstr_set(x_269, 1, x_268);
x_270 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_270, 0, x_269);
x_271 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_271, 0, x_270);
if (lean::is_scalar(x_263)) {
 x_272 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_272 = x_263;
}
lean::cnstr_set(x_272, 0, x_260);
lean::cnstr_set(x_272, 1, x_261);
lean::cnstr_set(x_272, 2, x_262);
lean::cnstr_set(x_272, 3, x_271);
x_2 = x_12;
x_3 = x_272;
goto _start;
}
}
case 1:
{
obj* x_274; obj* x_275; 
lean::dec(x_251);
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_274 = lean::cnstr_get(x_20, 1);
lean::inc(x_274);
lean::dec(x_20);
x_275 = l___private_init_lean_expander_1__popStxArg(x_274, x_4);
if (lean::obj_tag(x_275) == 0)
{
obj* x_276; obj* x_277; obj* x_278; 
lean::dec(x_12);
lean::dec(x_1);
x_276 = lean::cnstr_get(x_275, 0);
lean::inc(x_276);
if (lean::is_exclusive(x_275)) {
 lean::cnstr_release(x_275, 0);
 x_277 = x_275;
} else {
 lean::dec_ref(x_275);
 x_277 = lean::box(0);
}
if (lean::is_scalar(x_277)) {
 x_278 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_278 = x_277;
}
lean::cnstr_set(x_278, 0, x_276);
return x_278;
}
else
{
obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
x_279 = lean::cnstr_get(x_275, 0);
lean::inc(x_279);
lean::dec(x_275);
x_280 = lean::cnstr_get(x_279, 1);
lean::inc(x_280);
x_281 = lean::cnstr_get(x_279, 0);
lean::inc(x_281);
lean::dec(x_279);
x_282 = lean::cnstr_get(x_280, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
x_284 = lean::cnstr_get(x_280, 2);
lean::inc(x_284);
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 lean::cnstr_release(x_280, 1);
 lean::cnstr_release(x_280, 2);
 lean::cnstr_release(x_280, 3);
 x_285 = x_280;
} else {
 lean::dec_ref(x_280);
 x_285 = lean::box(0);
}
x_286 = l_Lean_Parser_Term_binders_HasView;
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_288 = lean::apply_1(x_287, x_281);
x_289 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_289, 0, x_288);
if (lean::is_scalar(x_285)) {
 x_290 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_290 = x_285;
}
lean::cnstr_set(x_290, 0, x_282);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_289);
x_2 = x_12;
x_3 = x_290;
goto _start;
}
}
default: 
{
obj* x_292; obj* x_293; 
x_292 = lean::cnstr_get(x_251, 0);
lean::inc(x_292);
lean::dec(x_251);
x_293 = lean::cnstr_get(x_292, 1);
lean::inc(x_293);
if (lean::obj_tag(x_293) == 0)
{
obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_14);
x_294 = lean::cnstr_get(x_20, 1);
lean::inc(x_294);
lean::dec(x_20);
x_295 = lean::cnstr_get(x_292, 0);
lean::inc(x_295);
lean::dec(x_292);
x_296 = l___private_init_lean_expander_1__popStxArg(x_294, x_4);
if (lean::obj_tag(x_296) == 0)
{
obj* x_297; obj* x_298; obj* x_299; 
lean::dec(x_295);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_297 = lean::cnstr_get(x_296, 0);
lean::inc(x_297);
if (lean::is_exclusive(x_296)) {
 lean::cnstr_release(x_296, 0);
 x_298 = x_296;
} else {
 lean::dec_ref(x_296);
 x_298 = lean::box(0);
}
if (lean::is_scalar(x_298)) {
 x_299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_299 = x_298;
}
lean::cnstr_set(x_299, 0, x_297);
return x_299;
}
else
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; 
x_300 = lean::cnstr_get(x_296, 0);
lean::inc(x_300);
lean::dec(x_296);
x_301 = lean::cnstr_get(x_300, 1);
lean::inc(x_301);
x_302 = lean::cnstr_get(x_300, 0);
lean::inc(x_302);
if (lean::is_exclusive(x_300)) {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_303 = x_300;
} else {
 lean::dec_ref(x_300);
 x_303 = lean::box(0);
}
x_304 = lean::cnstr_get(x_301, 0);
lean::inc(x_304);
x_305 = lean::cnstr_get(x_301, 1);
lean::inc(x_305);
x_306 = lean::cnstr_get(x_301, 2);
lean::inc(x_306);
x_307 = lean::cnstr_get(x_301, 3);
lean::inc(x_307);
if (lean::is_exclusive(x_301)) {
 lean::cnstr_release(x_301, 0);
 lean::cnstr_release(x_301, 1);
 lean::cnstr_release(x_301, 2);
 lean::cnstr_release(x_301, 3);
 x_308 = x_301;
} else {
 lean::dec_ref(x_301);
 x_308 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_309 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_309 = x_303;
}
lean::cnstr_set(x_309, 0, x_295);
lean::cnstr_set(x_309, 1, x_302);
lean::cnstr_set(x_2, 1, x_306);
lean::cnstr_set(x_2, 0, x_309);
if (lean::is_scalar(x_308)) {
 x_310 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_310 = x_308;
}
lean::cnstr_set(x_310, 0, x_304);
lean::cnstr_set(x_310, 1, x_305);
lean::cnstr_set(x_310, 2, x_2);
lean::cnstr_set(x_310, 3, x_307);
x_2 = x_12;
x_3 = x_310;
goto _start;
}
}
else
{
obj* x_312; obj* x_313; 
x_312 = lean::cnstr_get(x_293, 0);
lean::inc(x_312);
lean::dec(x_293);
x_313 = lean::cnstr_get(x_312, 1);
lean::inc(x_313);
lean::dec(x_312);
switch (lean::obj_tag(x_313)) {
case 0:
{
obj* x_314; obj* x_315; obj* x_316; 
lean::dec(x_313);
lean::dec(x_14);
x_314 = lean::cnstr_get(x_20, 1);
lean::inc(x_314);
lean::dec(x_20);
x_315 = lean::cnstr_get(x_292, 0);
lean::inc(x_315);
lean::dec(x_292);
x_316 = l___private_init_lean_expander_1__popStxArg(x_314, x_4);
if (lean::obj_tag(x_316) == 0)
{
obj* x_317; obj* x_318; obj* x_319; 
lean::dec(x_315);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
if (lean::is_exclusive(x_316)) {
 lean::cnstr_release(x_316, 0);
 x_318 = x_316;
} else {
 lean::dec_ref(x_316);
 x_318 = lean::box(0);
}
if (lean::is_scalar(x_318)) {
 x_319 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_319 = x_318;
}
lean::cnstr_set(x_319, 0, x_317);
return x_319;
}
else
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
x_320 = lean::cnstr_get(x_316, 0);
lean::inc(x_320);
lean::dec(x_316);
x_321 = lean::cnstr_get(x_320, 1);
lean::inc(x_321);
x_322 = lean::cnstr_get(x_320, 0);
lean::inc(x_322);
if (lean::is_exclusive(x_320)) {
 lean::cnstr_release(x_320, 0);
 lean::cnstr_release(x_320, 1);
 x_323 = x_320;
} else {
 lean::dec_ref(x_320);
 x_323 = lean::box(0);
}
x_324 = lean::cnstr_get(x_321, 0);
lean::inc(x_324);
x_325 = lean::cnstr_get(x_321, 1);
lean::inc(x_325);
x_326 = lean::cnstr_get(x_321, 2);
lean::inc(x_326);
x_327 = lean::cnstr_get(x_321, 3);
lean::inc(x_327);
if (lean::is_exclusive(x_321)) {
 lean::cnstr_release(x_321, 0);
 lean::cnstr_release(x_321, 1);
 lean::cnstr_release(x_321, 2);
 lean::cnstr_release(x_321, 3);
 x_328 = x_321;
} else {
 lean::dec_ref(x_321);
 x_328 = lean::box(0);
}
if (lean::is_scalar(x_323)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_323;
}
lean::cnstr_set(x_329, 0, x_315);
lean::cnstr_set(x_329, 1, x_322);
lean::cnstr_set(x_2, 1, x_326);
lean::cnstr_set(x_2, 0, x_329);
if (lean::is_scalar(x_328)) {
 x_330 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_330 = x_328;
}
lean::cnstr_set(x_330, 0, x_324);
lean::cnstr_set(x_330, 1, x_325);
lean::cnstr_set(x_330, 2, x_2);
lean::cnstr_set(x_330, 3, x_327);
x_2 = x_12;
x_3 = x_330;
goto _start;
}
}
case 2:
{
obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_332 = lean::cnstr_get(x_20, 1);
lean::inc(x_332);
lean::dec(x_20);
x_333 = lean::cnstr_get(x_292, 0);
lean::inc(x_333);
lean::dec(x_292);
x_334 = lean::cnstr_get(x_313, 0);
lean::inc(x_334);
lean::dec(x_313);
x_335 = l___private_init_lean_expander_1__popStxArg(x_332, x_4);
if (lean::obj_tag(x_335) == 0)
{
obj* x_336; obj* x_337; obj* x_338; 
lean::dec(x_334);
lean::dec(x_333);
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_336 = lean::cnstr_get(x_335, 0);
lean::inc(x_336);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 x_337 = x_335;
} else {
 lean::dec_ref(x_335);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_336);
return x_338;
}
else
{
obj* x_339; obj* x_340; obj* x_341; 
x_339 = lean::cnstr_get(x_335, 0);
lean::inc(x_339);
lean::dec(x_335);
x_340 = lean::cnstr_get(x_339, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_340, 3);
lean::inc(x_341);
if (lean::obj_tag(x_341) == 0)
{
obj* x_342; 
lean::dec(x_339);
lean::dec(x_334);
lean::dec(x_333);
lean::free_heap_obj(x_2);
x_342 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_340, x_4);
lean::dec(x_340);
lean::dec(x_14);
if (lean::obj_tag(x_342) == 0)
{
obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_12);
lean::dec(x_1);
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
if (lean::is_exclusive(x_342)) {
 lean::cnstr_release(x_342, 0);
 x_344 = x_342;
} else {
 lean::dec_ref(x_342);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_343);
return x_345;
}
else
{
obj* x_346; obj* x_347; 
x_346 = lean::cnstr_get(x_342, 0);
lean::inc(x_346);
lean::dec(x_342);
x_347 = lean::cnstr_get(x_346, 1);
lean::inc(x_347);
lean::dec(x_346);
x_2 = x_12;
x_3 = x_347;
goto _start;
}
}
else
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
lean::dec(x_14);
x_349 = lean::cnstr_get(x_339, 0);
lean::inc(x_349);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 x_350 = x_339;
} else {
 lean::dec_ref(x_339);
 x_350 = lean::box(0);
}
x_351 = lean::cnstr_get(x_340, 0);
lean::inc(x_351);
x_352 = lean::cnstr_get(x_340, 1);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 2);
lean::inc(x_353);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_354 = x_340;
} else {
 lean::dec_ref(x_340);
 x_354 = lean::box(0);
}
x_355 = lean::cnstr_get(x_341, 0);
lean::inc(x_355);
x_356 = l_Lean_Parser_Term_lambda_HasView;
x_357 = lean::cnstr_get(x_356, 1);
lean::inc(x_357);
x_358 = lean::box(0);
x_359 = lean::cnstr_get(x_334, 3);
lean::inc(x_359);
x_360 = lean::box(0);
lean::cnstr_set(x_2, 1, x_360);
lean::cnstr_set(x_2, 0, x_359);
x_361 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_362 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_358);
x_363 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_363, 0, x_362);
x_364 = lean::cnstr_get(x_334, 5);
lean::inc(x_364);
lean::dec(x_334);
x_365 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_366 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_367 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_363);
lean::cnstr_set(x_367, 2, x_366);
lean::cnstr_set(x_367, 3, x_364);
lean::inc(x_357);
x_368 = lean::apply_1(x_357, x_367);
x_369 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_369, 0, x_365);
lean::cnstr_set(x_369, 1, x_355);
lean::cnstr_set(x_369, 2, x_366);
lean::cnstr_set(x_369, 3, x_349);
x_370 = lean::apply_1(x_357, x_369);
x_371 = l_Lean_Parser_Term_app_HasView;
x_372 = lean::cnstr_get(x_371, 1);
lean::inc(x_372);
x_373 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_373, 0, x_368);
lean::cnstr_set(x_373, 1, x_370);
x_374 = lean::apply_1(x_372, x_373);
if (lean::is_scalar(x_350)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_350;
}
lean::cnstr_set(x_375, 0, x_333);
lean::cnstr_set(x_375, 1, x_374);
x_376 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_376, 0, x_375);
lean::cnstr_set(x_376, 1, x_353);
if (lean::is_scalar(x_354)) {
 x_377 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_377 = x_354;
}
lean::cnstr_set(x_377, 0, x_351);
lean::cnstr_set(x_377, 1, x_352);
lean::cnstr_set(x_377, 2, x_376);
lean::cnstr_set(x_377, 3, x_341);
x_2 = x_12;
x_3 = x_377;
goto _start;
}
}
}
default: 
{
obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_313);
lean::dec(x_292);
lean::free_heap_obj(x_2);
x_379 = lean::cnstr_get(x_20, 1);
lean::inc(x_379);
lean::dec(x_20);
x_380 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_381 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_380, x_379, x_4);
lean::dec(x_379);
lean::dec(x_14);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; 
lean::dec(x_12);
lean::dec(x_1);
x_382 = lean::cnstr_get(x_381, 0);
lean::inc(x_382);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 x_383 = x_381;
} else {
 lean::dec_ref(x_381);
 x_383 = lean::box(0);
}
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_382);
return x_384;
}
else
{
obj* x_385; obj* x_386; 
x_385 = lean::cnstr_get(x_381, 0);
lean::inc(x_385);
lean::dec(x_381);
x_386 = lean::cnstr_get(x_385, 1);
lean::inc(x_386);
lean::dec(x_385);
x_2 = x_12;
x_3 = x_386;
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
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; 
x_388 = lean::cnstr_get(x_2, 1);
lean::inc(x_388);
lean::dec(x_2);
lean::inc(x_1);
x_389 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_389, 0, x_1);
x_390 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_391 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_390, x_3, x_4);
lean::dec(x_3);
if (lean::obj_tag(x_391) == 0)
{
obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_389);
lean::dec(x_388);
lean::dec(x_8);
lean::dec(x_1);
x_392 = lean::cnstr_get(x_391, 0);
lean::inc(x_392);
if (lean::is_exclusive(x_391)) {
 lean::cnstr_release(x_391, 0);
 x_393 = x_391;
} else {
 lean::dec_ref(x_391);
 x_393 = lean::box(0);
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_392);
return x_394;
}
else
{
obj* x_395; obj* x_396; 
x_395 = lean::cnstr_get(x_391, 0);
lean::inc(x_395);
lean::dec(x_391);
x_396 = lean::cnstr_get(x_8, 1);
lean::inc(x_396);
lean::dec(x_8);
if (lean::obj_tag(x_396) == 0)
{
obj* x_397; 
lean::dec(x_389);
x_397 = lean::cnstr_get(x_395, 1);
lean::inc(x_397);
lean::dec(x_395);
x_2 = x_388;
x_3 = x_397;
goto _start;
}
else
{
obj* x_399; obj* x_400; 
x_399 = lean::cnstr_get(x_396, 0);
lean::inc(x_399);
if (lean::is_exclusive(x_396)) {
 lean::cnstr_release(x_396, 0);
 x_400 = x_396;
} else {
 lean::dec_ref(x_396);
 x_400 = lean::box(0);
}
switch (lean::obj_tag(x_399)) {
case 0:
{
obj* x_401; obj* x_402; 
lean::dec(x_399);
lean::dec(x_389);
x_401 = lean::cnstr_get(x_395, 1);
lean::inc(x_401);
lean::dec(x_395);
x_402 = l___private_init_lean_expander_1__popStxArg(x_401, x_4);
if (lean::obj_tag(x_402) == 0)
{
obj* x_403; obj* x_404; obj* x_405; 
lean::dec(x_400);
lean::dec(x_388);
lean::dec(x_1);
x_403 = lean::cnstr_get(x_402, 0);
lean::inc(x_403);
if (lean::is_exclusive(x_402)) {
 lean::cnstr_release(x_402, 0);
 x_404 = x_402;
} else {
 lean::dec_ref(x_402);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_403);
return x_405;
}
else
{
obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
x_406 = lean::cnstr_get(x_402, 0);
lean::inc(x_406);
lean::dec(x_402);
x_407 = lean::cnstr_get(x_406, 1);
lean::inc(x_407);
x_408 = lean::cnstr_get(x_406, 0);
lean::inc(x_408);
lean::dec(x_406);
x_409 = lean::cnstr_get(x_407, 0);
lean::inc(x_409);
x_410 = lean::cnstr_get(x_407, 1);
lean::inc(x_410);
x_411 = lean::cnstr_get(x_407, 2);
lean::inc(x_411);
if (lean::is_exclusive(x_407)) {
 lean::cnstr_release(x_407, 0);
 lean::cnstr_release(x_407, 1);
 lean::cnstr_release(x_407, 2);
 lean::cnstr_release(x_407, 3);
 x_412 = x_407;
} else {
 lean::dec_ref(x_407);
 x_412 = lean::box(0);
}
x_413 = l_Lean_Parser_Term_binderIdent_HasView;
x_414 = lean::cnstr_get(x_413, 0);
lean::inc(x_414);
x_415 = lean::apply_1(x_414, x_408);
x_416 = lean::box(0);
x_417 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_417, 0, x_415);
lean::cnstr_set(x_417, 1, x_416);
x_418 = lean::box(0);
x_419 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_419, 0, x_417);
lean::cnstr_set(x_419, 1, x_418);
x_420 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_420, 0, x_419);
if (lean::is_scalar(x_400)) {
 x_421 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_421 = x_400;
}
lean::cnstr_set(x_421, 0, x_420);
if (lean::is_scalar(x_412)) {
 x_422 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_422 = x_412;
}
lean::cnstr_set(x_422, 0, x_409);
lean::cnstr_set(x_422, 1, x_410);
lean::cnstr_set(x_422, 2, x_411);
lean::cnstr_set(x_422, 3, x_421);
x_2 = x_388;
x_3 = x_422;
goto _start;
}
}
case 1:
{
obj* x_424; obj* x_425; 
lean::dec(x_399);
lean::dec(x_389);
x_424 = lean::cnstr_get(x_395, 1);
lean::inc(x_424);
lean::dec(x_395);
x_425 = l___private_init_lean_expander_1__popStxArg(x_424, x_4);
if (lean::obj_tag(x_425) == 0)
{
obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_400);
lean::dec(x_388);
lean::dec(x_1);
x_426 = lean::cnstr_get(x_425, 0);
lean::inc(x_426);
if (lean::is_exclusive(x_425)) {
 lean::cnstr_release(x_425, 0);
 x_427 = x_425;
} else {
 lean::dec_ref(x_425);
 x_427 = lean::box(0);
}
if (lean::is_scalar(x_427)) {
 x_428 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_428 = x_427;
}
lean::cnstr_set(x_428, 0, x_426);
return x_428;
}
else
{
obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; 
x_429 = lean::cnstr_get(x_425, 0);
lean::inc(x_429);
lean::dec(x_425);
x_430 = lean::cnstr_get(x_429, 1);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_429, 0);
lean::inc(x_431);
lean::dec(x_429);
x_432 = lean::cnstr_get(x_430, 0);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_430, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_430, 2);
lean::inc(x_434);
if (lean::is_exclusive(x_430)) {
 lean::cnstr_release(x_430, 0);
 lean::cnstr_release(x_430, 1);
 lean::cnstr_release(x_430, 2);
 lean::cnstr_release(x_430, 3);
 x_435 = x_430;
} else {
 lean::dec_ref(x_430);
 x_435 = lean::box(0);
}
x_436 = l_Lean_Parser_Term_binders_HasView;
x_437 = lean::cnstr_get(x_436, 0);
lean::inc(x_437);
x_438 = lean::apply_1(x_437, x_431);
if (lean::is_scalar(x_400)) {
 x_439 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_439 = x_400;
}
lean::cnstr_set(x_439, 0, x_438);
if (lean::is_scalar(x_435)) {
 x_440 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_440 = x_435;
}
lean::cnstr_set(x_440, 0, x_432);
lean::cnstr_set(x_440, 1, x_433);
lean::cnstr_set(x_440, 2, x_434);
lean::cnstr_set(x_440, 3, x_439);
x_2 = x_388;
x_3 = x_440;
goto _start;
}
}
default: 
{
obj* x_442; obj* x_443; 
lean::dec(x_400);
x_442 = lean::cnstr_get(x_399, 0);
lean::inc(x_442);
lean::dec(x_399);
x_443 = lean::cnstr_get(x_442, 1);
lean::inc(x_443);
if (lean::obj_tag(x_443) == 0)
{
obj* x_444; obj* x_445; obj* x_446; 
lean::dec(x_389);
x_444 = lean::cnstr_get(x_395, 1);
lean::inc(x_444);
lean::dec(x_395);
x_445 = lean::cnstr_get(x_442, 0);
lean::inc(x_445);
lean::dec(x_442);
x_446 = l___private_init_lean_expander_1__popStxArg(x_444, x_4);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; 
lean::dec(x_445);
lean::dec(x_388);
lean::dec(x_1);
x_447 = lean::cnstr_get(x_446, 0);
lean::inc(x_447);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 x_448 = x_446;
} else {
 lean::dec_ref(x_446);
 x_448 = lean::box(0);
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_447);
return x_449;
}
else
{
obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; 
x_450 = lean::cnstr_get(x_446, 0);
lean::inc(x_450);
lean::dec(x_446);
x_451 = lean::cnstr_get(x_450, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_450, 0);
lean::inc(x_452);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_453 = x_450;
} else {
 lean::dec_ref(x_450);
 x_453 = lean::box(0);
}
x_454 = lean::cnstr_get(x_451, 0);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_451, 1);
lean::inc(x_455);
x_456 = lean::cnstr_get(x_451, 2);
lean::inc(x_456);
x_457 = lean::cnstr_get(x_451, 3);
lean::inc(x_457);
if (lean::is_exclusive(x_451)) {
 lean::cnstr_release(x_451, 0);
 lean::cnstr_release(x_451, 1);
 lean::cnstr_release(x_451, 2);
 lean::cnstr_release(x_451, 3);
 x_458 = x_451;
} else {
 lean::dec_ref(x_451);
 x_458 = lean::box(0);
}
if (lean::is_scalar(x_453)) {
 x_459 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_459 = x_453;
}
lean::cnstr_set(x_459, 0, x_445);
lean::cnstr_set(x_459, 1, x_452);
x_460 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_460, 0, x_459);
lean::cnstr_set(x_460, 1, x_456);
if (lean::is_scalar(x_458)) {
 x_461 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_461 = x_458;
}
lean::cnstr_set(x_461, 0, x_454);
lean::cnstr_set(x_461, 1, x_455);
lean::cnstr_set(x_461, 2, x_460);
lean::cnstr_set(x_461, 3, x_457);
x_2 = x_388;
x_3 = x_461;
goto _start;
}
}
else
{
obj* x_463; obj* x_464; 
x_463 = lean::cnstr_get(x_443, 0);
lean::inc(x_463);
lean::dec(x_443);
x_464 = lean::cnstr_get(x_463, 1);
lean::inc(x_464);
lean::dec(x_463);
switch (lean::obj_tag(x_464)) {
case 0:
{
obj* x_465; obj* x_466; obj* x_467; 
lean::dec(x_464);
lean::dec(x_389);
x_465 = lean::cnstr_get(x_395, 1);
lean::inc(x_465);
lean::dec(x_395);
x_466 = lean::cnstr_get(x_442, 0);
lean::inc(x_466);
lean::dec(x_442);
x_467 = l___private_init_lean_expander_1__popStxArg(x_465, x_4);
if (lean::obj_tag(x_467) == 0)
{
obj* x_468; obj* x_469; obj* x_470; 
lean::dec(x_466);
lean::dec(x_388);
lean::dec(x_1);
x_468 = lean::cnstr_get(x_467, 0);
lean::inc(x_468);
if (lean::is_exclusive(x_467)) {
 lean::cnstr_release(x_467, 0);
 x_469 = x_467;
} else {
 lean::dec_ref(x_467);
 x_469 = lean::box(0);
}
if (lean::is_scalar(x_469)) {
 x_470 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_470 = x_469;
}
lean::cnstr_set(x_470, 0, x_468);
return x_470;
}
else
{
obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; 
x_471 = lean::cnstr_get(x_467, 0);
lean::inc(x_471);
lean::dec(x_467);
x_472 = lean::cnstr_get(x_471, 1);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_471, 0);
lean::inc(x_473);
if (lean::is_exclusive(x_471)) {
 lean::cnstr_release(x_471, 0);
 lean::cnstr_release(x_471, 1);
 x_474 = x_471;
} else {
 lean::dec_ref(x_471);
 x_474 = lean::box(0);
}
x_475 = lean::cnstr_get(x_472, 0);
lean::inc(x_475);
x_476 = lean::cnstr_get(x_472, 1);
lean::inc(x_476);
x_477 = lean::cnstr_get(x_472, 2);
lean::inc(x_477);
x_478 = lean::cnstr_get(x_472, 3);
lean::inc(x_478);
if (lean::is_exclusive(x_472)) {
 lean::cnstr_release(x_472, 0);
 lean::cnstr_release(x_472, 1);
 lean::cnstr_release(x_472, 2);
 lean::cnstr_release(x_472, 3);
 x_479 = x_472;
} else {
 lean::dec_ref(x_472);
 x_479 = lean::box(0);
}
if (lean::is_scalar(x_474)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_474;
}
lean::cnstr_set(x_480, 0, x_466);
lean::cnstr_set(x_480, 1, x_473);
x_481 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_481, 0, x_480);
lean::cnstr_set(x_481, 1, x_477);
if (lean::is_scalar(x_479)) {
 x_482 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_482 = x_479;
}
lean::cnstr_set(x_482, 0, x_475);
lean::cnstr_set(x_482, 1, x_476);
lean::cnstr_set(x_482, 2, x_481);
lean::cnstr_set(x_482, 3, x_478);
x_2 = x_388;
x_3 = x_482;
goto _start;
}
}
case 2:
{
obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_484 = lean::cnstr_get(x_395, 1);
lean::inc(x_484);
lean::dec(x_395);
x_485 = lean::cnstr_get(x_442, 0);
lean::inc(x_485);
lean::dec(x_442);
x_486 = lean::cnstr_get(x_464, 0);
lean::inc(x_486);
lean::dec(x_464);
x_487 = l___private_init_lean_expander_1__popStxArg(x_484, x_4);
if (lean::obj_tag(x_487) == 0)
{
obj* x_488; obj* x_489; obj* x_490; 
lean::dec(x_486);
lean::dec(x_485);
lean::dec(x_389);
lean::dec(x_388);
lean::dec(x_1);
x_488 = lean::cnstr_get(x_487, 0);
lean::inc(x_488);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 x_489 = x_487;
} else {
 lean::dec_ref(x_487);
 x_489 = lean::box(0);
}
if (lean::is_scalar(x_489)) {
 x_490 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_490 = x_489;
}
lean::cnstr_set(x_490, 0, x_488);
return x_490;
}
else
{
obj* x_491; obj* x_492; obj* x_493; 
x_491 = lean::cnstr_get(x_487, 0);
lean::inc(x_491);
lean::dec(x_487);
x_492 = lean::cnstr_get(x_491, 1);
lean::inc(x_492);
x_493 = lean::cnstr_get(x_492, 3);
lean::inc(x_493);
if (lean::obj_tag(x_493) == 0)
{
obj* x_494; 
lean::dec(x_491);
lean::dec(x_486);
lean::dec(x_485);
x_494 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_390, x_492, x_4);
lean::dec(x_492);
lean::dec(x_389);
if (lean::obj_tag(x_494) == 0)
{
obj* x_495; obj* x_496; obj* x_497; 
lean::dec(x_388);
lean::dec(x_1);
x_495 = lean::cnstr_get(x_494, 0);
lean::inc(x_495);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 x_496 = x_494;
} else {
 lean::dec_ref(x_494);
 x_496 = lean::box(0);
}
if (lean::is_scalar(x_496)) {
 x_497 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_497 = x_496;
}
lean::cnstr_set(x_497, 0, x_495);
return x_497;
}
else
{
obj* x_498; obj* x_499; 
x_498 = lean::cnstr_get(x_494, 0);
lean::inc(x_498);
lean::dec(x_494);
x_499 = lean::cnstr_get(x_498, 1);
lean::inc(x_499);
lean::dec(x_498);
x_2 = x_388;
x_3 = x_499;
goto _start;
}
}
else
{
obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; 
lean::dec(x_389);
x_501 = lean::cnstr_get(x_491, 0);
lean::inc(x_501);
if (lean::is_exclusive(x_491)) {
 lean::cnstr_release(x_491, 0);
 lean::cnstr_release(x_491, 1);
 x_502 = x_491;
} else {
 lean::dec_ref(x_491);
 x_502 = lean::box(0);
}
x_503 = lean::cnstr_get(x_492, 0);
lean::inc(x_503);
x_504 = lean::cnstr_get(x_492, 1);
lean::inc(x_504);
x_505 = lean::cnstr_get(x_492, 2);
lean::inc(x_505);
if (lean::is_exclusive(x_492)) {
 lean::cnstr_release(x_492, 0);
 lean::cnstr_release(x_492, 1);
 lean::cnstr_release(x_492, 2);
 lean::cnstr_release(x_492, 3);
 x_506 = x_492;
} else {
 lean::dec_ref(x_492);
 x_506 = lean::box(0);
}
x_507 = lean::cnstr_get(x_493, 0);
lean::inc(x_507);
x_508 = l_Lean_Parser_Term_lambda_HasView;
x_509 = lean::cnstr_get(x_508, 1);
lean::inc(x_509);
x_510 = lean::box(0);
x_511 = lean::cnstr_get(x_486, 3);
lean::inc(x_511);
x_512 = lean::box(0);
x_513 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_513, 0, x_511);
lean::cnstr_set(x_513, 1, x_512);
x_514 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_513);
x_515 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_515, 0, x_514);
lean::cnstr_set(x_515, 1, x_510);
x_516 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_516, 0, x_515);
x_517 = lean::cnstr_get(x_486, 5);
lean::inc(x_517);
lean::dec(x_486);
x_518 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_519 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_520 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_520, 0, x_518);
lean::cnstr_set(x_520, 1, x_516);
lean::cnstr_set(x_520, 2, x_519);
lean::cnstr_set(x_520, 3, x_517);
lean::inc(x_509);
x_521 = lean::apply_1(x_509, x_520);
x_522 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_522, 0, x_518);
lean::cnstr_set(x_522, 1, x_507);
lean::cnstr_set(x_522, 2, x_519);
lean::cnstr_set(x_522, 3, x_501);
x_523 = lean::apply_1(x_509, x_522);
x_524 = l_Lean_Parser_Term_app_HasView;
x_525 = lean::cnstr_get(x_524, 1);
lean::inc(x_525);
x_526 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_526, 0, x_521);
lean::cnstr_set(x_526, 1, x_523);
x_527 = lean::apply_1(x_525, x_526);
if (lean::is_scalar(x_502)) {
 x_528 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_528 = x_502;
}
lean::cnstr_set(x_528, 0, x_485);
lean::cnstr_set(x_528, 1, x_527);
x_529 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_529, 0, x_528);
lean::cnstr_set(x_529, 1, x_505);
if (lean::is_scalar(x_506)) {
 x_530 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_530 = x_506;
}
lean::cnstr_set(x_530, 0, x_503);
lean::cnstr_set(x_530, 1, x_504);
lean::cnstr_set(x_530, 2, x_529);
lean::cnstr_set(x_530, 3, x_493);
x_2 = x_388;
x_3 = x_530;
goto _start;
}
}
}
default: 
{
obj* x_532; obj* x_533; obj* x_534; 
lean::dec(x_464);
lean::dec(x_442);
x_532 = lean::cnstr_get(x_395, 1);
lean::inc(x_532);
lean::dec(x_395);
x_533 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_534 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_533, x_532, x_4);
lean::dec(x_532);
lean::dec(x_389);
if (lean::obj_tag(x_534) == 0)
{
obj* x_535; obj* x_536; obj* x_537; 
lean::dec(x_388);
lean::dec(x_1);
x_535 = lean::cnstr_get(x_534, 0);
lean::inc(x_535);
if (lean::is_exclusive(x_534)) {
 lean::cnstr_release(x_534, 0);
 x_536 = x_534;
} else {
 lean::dec_ref(x_534);
 x_536 = lean::box(0);
}
if (lean::is_scalar(x_536)) {
 x_537 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_537 = x_536;
}
lean::cnstr_set(x_537, 0, x_535);
return x_537;
}
else
{
obj* x_538; obj* x_539; 
x_538 = lean::cnstr_get(x_534, 0);
lean::inc(x_538);
lean::dec(x_534);
x_539 = lean::cnstr_get(x_538, 1);
lean::inc(x_539);
lean::dec(x_538);
x_2 = x_388;
x_3 = x_539;
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
else
{
uint8 x_541; 
lean::dec(x_10);
x_541 = !lean::is_exclusive(x_2);
if (x_541 == 0)
{
obj* x_542; obj* x_543; obj* x_544; 
x_542 = lean::cnstr_get(x_2, 1);
x_543 = lean::cnstr_get(x_2, 0);
lean::dec(x_543);
x_544 = l___private_init_lean_expander_1__popStxArg(x_3, x_4);
if (lean::obj_tag(x_544) == 0)
{
uint8 x_545; 
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_8);
lean::dec(x_1);
x_545 = !lean::is_exclusive(x_544);
if (x_545 == 0)
{
return x_544;
}
else
{
obj* x_546; obj* x_547; 
x_546 = lean::cnstr_get(x_544, 0);
lean::inc(x_546);
lean::dec(x_544);
x_547 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_547, 0, x_546);
return x_547;
}
}
else
{
obj* x_548; obj* x_549; 
x_548 = lean::cnstr_get(x_544, 0);
lean::inc(x_548);
lean::dec(x_544);
x_549 = lean::cnstr_get(x_8, 1);
lean::inc(x_549);
lean::dec(x_8);
if (lean::obj_tag(x_549) == 0)
{
obj* x_550; 
lean::free_heap_obj(x_2);
x_550 = lean::cnstr_get(x_548, 1);
lean::inc(x_550);
lean::dec(x_548);
x_2 = x_542;
x_3 = x_550;
goto _start;
}
else
{
uint8 x_552; 
x_552 = !lean::is_exclusive(x_549);
if (x_552 == 0)
{
obj* x_553; 
x_553 = lean::cnstr_get(x_549, 0);
switch (lean::obj_tag(x_553)) {
case 0:
{
obj* x_554; obj* x_555; 
lean::dec(x_553);
x_554 = lean::cnstr_get(x_548, 1);
lean::inc(x_554);
lean::dec(x_548);
x_555 = l___private_init_lean_expander_1__popStxArg(x_554, x_4);
if (lean::obj_tag(x_555) == 0)
{
uint8 x_556; 
lean::free_heap_obj(x_549);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_556 = !lean::is_exclusive(x_555);
if (x_556 == 0)
{
return x_555;
}
else
{
obj* x_557; obj* x_558; 
x_557 = lean::cnstr_get(x_555, 0);
lean::inc(x_557);
lean::dec(x_555);
x_558 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_558, 0, x_557);
return x_558;
}
}
else
{
obj* x_559; obj* x_560; obj* x_561; uint8 x_562; 
x_559 = lean::cnstr_get(x_555, 0);
lean::inc(x_559);
lean::dec(x_555);
x_560 = lean::cnstr_get(x_559, 1);
lean::inc(x_560);
x_561 = lean::cnstr_get(x_559, 0);
lean::inc(x_561);
lean::dec(x_559);
x_562 = !lean::is_exclusive(x_560);
if (x_562 == 0)
{
obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; 
x_563 = lean::cnstr_get(x_560, 3);
lean::dec(x_563);
x_564 = l_Lean_Parser_Term_binderIdent_HasView;
x_565 = lean::cnstr_get(x_564, 0);
lean::inc(x_565);
x_566 = lean::apply_1(x_565, x_561);
x_567 = lean::box(0);
lean::cnstr_set(x_2, 1, x_567);
lean::cnstr_set(x_2, 0, x_566);
x_568 = lean::box(0);
x_569 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_569, 0, x_2);
lean::cnstr_set(x_569, 1, x_568);
x_570 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_570, 0, x_569);
lean::cnstr_set(x_549, 0, x_570);
lean::cnstr_set(x_560, 3, x_549);
x_2 = x_542;
x_3 = x_560;
goto _start;
}
else
{
obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; 
x_572 = lean::cnstr_get(x_560, 0);
x_573 = lean::cnstr_get(x_560, 1);
x_574 = lean::cnstr_get(x_560, 2);
lean::inc(x_574);
lean::inc(x_573);
lean::inc(x_572);
lean::dec(x_560);
x_575 = l_Lean_Parser_Term_binderIdent_HasView;
x_576 = lean::cnstr_get(x_575, 0);
lean::inc(x_576);
x_577 = lean::apply_1(x_576, x_561);
x_578 = lean::box(0);
lean::cnstr_set(x_2, 1, x_578);
lean::cnstr_set(x_2, 0, x_577);
x_579 = lean::box(0);
x_580 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_580, 0, x_2);
lean::cnstr_set(x_580, 1, x_579);
x_581 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_549, 0, x_581);
x_582 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_582, 0, x_572);
lean::cnstr_set(x_582, 1, x_573);
lean::cnstr_set(x_582, 2, x_574);
lean::cnstr_set(x_582, 3, x_549);
x_2 = x_542;
x_3 = x_582;
goto _start;
}
}
}
case 1:
{
obj* x_584; obj* x_585; 
lean::dec(x_553);
lean::free_heap_obj(x_2);
x_584 = lean::cnstr_get(x_548, 1);
lean::inc(x_584);
lean::dec(x_548);
x_585 = l___private_init_lean_expander_1__popStxArg(x_584, x_4);
if (lean::obj_tag(x_585) == 0)
{
uint8 x_586; 
lean::free_heap_obj(x_549);
lean::dec(x_542);
lean::dec(x_1);
x_586 = !lean::is_exclusive(x_585);
if (x_586 == 0)
{
return x_585;
}
else
{
obj* x_587; obj* x_588; 
x_587 = lean::cnstr_get(x_585, 0);
lean::inc(x_587);
lean::dec(x_585);
x_588 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_588, 0, x_587);
return x_588;
}
}
else
{
obj* x_589; obj* x_590; obj* x_591; uint8 x_592; 
x_589 = lean::cnstr_get(x_585, 0);
lean::inc(x_589);
lean::dec(x_585);
x_590 = lean::cnstr_get(x_589, 1);
lean::inc(x_590);
x_591 = lean::cnstr_get(x_589, 0);
lean::inc(x_591);
lean::dec(x_589);
x_592 = !lean::is_exclusive(x_590);
if (x_592 == 0)
{
obj* x_593; obj* x_594; obj* x_595; obj* x_596; 
x_593 = lean::cnstr_get(x_590, 3);
lean::dec(x_593);
x_594 = l_Lean_Parser_Term_binders_HasView;
x_595 = lean::cnstr_get(x_594, 0);
lean::inc(x_595);
x_596 = lean::apply_1(x_595, x_591);
lean::cnstr_set(x_549, 0, x_596);
lean::cnstr_set(x_590, 3, x_549);
x_2 = x_542;
x_3 = x_590;
goto _start;
}
else
{
obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; 
x_598 = lean::cnstr_get(x_590, 0);
x_599 = lean::cnstr_get(x_590, 1);
x_600 = lean::cnstr_get(x_590, 2);
lean::inc(x_600);
lean::inc(x_599);
lean::inc(x_598);
lean::dec(x_590);
x_601 = l_Lean_Parser_Term_binders_HasView;
x_602 = lean::cnstr_get(x_601, 0);
lean::inc(x_602);
x_603 = lean::apply_1(x_602, x_591);
lean::cnstr_set(x_549, 0, x_603);
x_604 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_604, 0, x_598);
lean::cnstr_set(x_604, 1, x_599);
lean::cnstr_set(x_604, 2, x_600);
lean::cnstr_set(x_604, 3, x_549);
x_2 = x_542;
x_3 = x_604;
goto _start;
}
}
}
default: 
{
obj* x_606; obj* x_607; 
lean::free_heap_obj(x_549);
x_606 = lean::cnstr_get(x_553, 0);
lean::inc(x_606);
lean::dec(x_553);
x_607 = lean::cnstr_get(x_606, 1);
lean::inc(x_607);
if (lean::obj_tag(x_607) == 0)
{
obj* x_608; obj* x_609; obj* x_610; 
x_608 = lean::cnstr_get(x_548, 1);
lean::inc(x_608);
lean::dec(x_548);
x_609 = lean::cnstr_get(x_606, 0);
lean::inc(x_609);
lean::dec(x_606);
x_610 = l___private_init_lean_expander_1__popStxArg(x_608, x_4);
if (lean::obj_tag(x_610) == 0)
{
uint8 x_611; 
lean::dec(x_609);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_611 = !lean::is_exclusive(x_610);
if (x_611 == 0)
{
return x_610;
}
else
{
obj* x_612; obj* x_613; 
x_612 = lean::cnstr_get(x_610, 0);
lean::inc(x_612);
lean::dec(x_610);
x_613 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_613, 0, x_612);
return x_613;
}
}
else
{
obj* x_614; uint8 x_615; 
x_614 = lean::cnstr_get(x_610, 0);
lean::inc(x_614);
lean::dec(x_610);
x_615 = !lean::is_exclusive(x_614);
if (x_615 == 0)
{
obj* x_616; uint8 x_617; 
x_616 = lean::cnstr_get(x_614, 1);
x_617 = !lean::is_exclusive(x_616);
if (x_617 == 0)
{
obj* x_618; obj* x_619; 
x_618 = lean::cnstr_get(x_614, 0);
x_619 = lean::cnstr_get(x_616, 2);
lean::cnstr_set(x_614, 1, x_618);
lean::cnstr_set(x_614, 0, x_609);
lean::cnstr_set(x_2, 1, x_619);
lean::cnstr_set(x_2, 0, x_614);
lean::cnstr_set(x_616, 2, x_2);
x_2 = x_542;
x_3 = x_616;
goto _start;
}
else
{
obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; 
x_621 = lean::cnstr_get(x_614, 0);
x_622 = lean::cnstr_get(x_616, 0);
x_623 = lean::cnstr_get(x_616, 1);
x_624 = lean::cnstr_get(x_616, 2);
x_625 = lean::cnstr_get(x_616, 3);
lean::inc(x_625);
lean::inc(x_624);
lean::inc(x_623);
lean::inc(x_622);
lean::dec(x_616);
lean::cnstr_set(x_614, 1, x_621);
lean::cnstr_set(x_614, 0, x_609);
lean::cnstr_set(x_2, 1, x_624);
lean::cnstr_set(x_2, 0, x_614);
x_626 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_626, 0, x_622);
lean::cnstr_set(x_626, 1, x_623);
lean::cnstr_set(x_626, 2, x_2);
lean::cnstr_set(x_626, 3, x_625);
x_2 = x_542;
x_3 = x_626;
goto _start;
}
}
else
{
obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_636; 
x_628 = lean::cnstr_get(x_614, 1);
x_629 = lean::cnstr_get(x_614, 0);
lean::inc(x_628);
lean::inc(x_629);
lean::dec(x_614);
x_630 = lean::cnstr_get(x_628, 0);
lean::inc(x_630);
x_631 = lean::cnstr_get(x_628, 1);
lean::inc(x_631);
x_632 = lean::cnstr_get(x_628, 2);
lean::inc(x_632);
x_633 = lean::cnstr_get(x_628, 3);
lean::inc(x_633);
if (lean::is_exclusive(x_628)) {
 lean::cnstr_release(x_628, 0);
 lean::cnstr_release(x_628, 1);
 lean::cnstr_release(x_628, 2);
 lean::cnstr_release(x_628, 3);
 x_634 = x_628;
} else {
 lean::dec_ref(x_628);
 x_634 = lean::box(0);
}
x_635 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_635, 0, x_609);
lean::cnstr_set(x_635, 1, x_629);
lean::cnstr_set(x_2, 1, x_632);
lean::cnstr_set(x_2, 0, x_635);
if (lean::is_scalar(x_634)) {
 x_636 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_636 = x_634;
}
lean::cnstr_set(x_636, 0, x_630);
lean::cnstr_set(x_636, 1, x_631);
lean::cnstr_set(x_636, 2, x_2);
lean::cnstr_set(x_636, 3, x_633);
x_2 = x_542;
x_3 = x_636;
goto _start;
}
}
}
else
{
uint8 x_638; 
x_638 = !lean::is_exclusive(x_607);
if (x_638 == 0)
{
obj* x_639; obj* x_640; 
x_639 = lean::cnstr_get(x_607, 0);
x_640 = lean::cnstr_get(x_639, 1);
lean::inc(x_640);
lean::dec(x_639);
switch (lean::obj_tag(x_640)) {
case 0:
{
obj* x_641; obj* x_642; obj* x_643; 
lean::dec(x_640);
lean::free_heap_obj(x_607);
x_641 = lean::cnstr_get(x_548, 1);
lean::inc(x_641);
lean::dec(x_548);
x_642 = lean::cnstr_get(x_606, 0);
lean::inc(x_642);
lean::dec(x_606);
x_643 = l___private_init_lean_expander_1__popStxArg(x_641, x_4);
if (lean::obj_tag(x_643) == 0)
{
uint8 x_644; 
lean::dec(x_642);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_644 = !lean::is_exclusive(x_643);
if (x_644 == 0)
{
return x_643;
}
else
{
obj* x_645; obj* x_646; 
x_645 = lean::cnstr_get(x_643, 0);
lean::inc(x_645);
lean::dec(x_643);
x_646 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_646, 0, x_645);
return x_646;
}
}
else
{
obj* x_647; uint8 x_648; 
x_647 = lean::cnstr_get(x_643, 0);
lean::inc(x_647);
lean::dec(x_643);
x_648 = !lean::is_exclusive(x_647);
if (x_648 == 0)
{
obj* x_649; uint8 x_650; 
x_649 = lean::cnstr_get(x_647, 1);
x_650 = !lean::is_exclusive(x_649);
if (x_650 == 0)
{
obj* x_651; obj* x_652; 
x_651 = lean::cnstr_get(x_647, 0);
x_652 = lean::cnstr_get(x_649, 2);
lean::cnstr_set(x_647, 1, x_651);
lean::cnstr_set(x_647, 0, x_642);
lean::cnstr_set(x_2, 1, x_652);
lean::cnstr_set(x_2, 0, x_647);
lean::cnstr_set(x_649, 2, x_2);
x_2 = x_542;
x_3 = x_649;
goto _start;
}
else
{
obj* x_654; obj* x_655; obj* x_656; obj* x_657; obj* x_658; obj* x_659; 
x_654 = lean::cnstr_get(x_647, 0);
x_655 = lean::cnstr_get(x_649, 0);
x_656 = lean::cnstr_get(x_649, 1);
x_657 = lean::cnstr_get(x_649, 2);
x_658 = lean::cnstr_get(x_649, 3);
lean::inc(x_658);
lean::inc(x_657);
lean::inc(x_656);
lean::inc(x_655);
lean::dec(x_649);
lean::cnstr_set(x_647, 1, x_654);
lean::cnstr_set(x_647, 0, x_642);
lean::cnstr_set(x_2, 1, x_657);
lean::cnstr_set(x_2, 0, x_647);
x_659 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_659, 0, x_655);
lean::cnstr_set(x_659, 1, x_656);
lean::cnstr_set(x_659, 2, x_2);
lean::cnstr_set(x_659, 3, x_658);
x_2 = x_542;
x_3 = x_659;
goto _start;
}
}
else
{
obj* x_661; obj* x_662; obj* x_663; obj* x_664; obj* x_665; obj* x_666; obj* x_667; obj* x_668; obj* x_669; 
x_661 = lean::cnstr_get(x_647, 1);
x_662 = lean::cnstr_get(x_647, 0);
lean::inc(x_661);
lean::inc(x_662);
lean::dec(x_647);
x_663 = lean::cnstr_get(x_661, 0);
lean::inc(x_663);
x_664 = lean::cnstr_get(x_661, 1);
lean::inc(x_664);
x_665 = lean::cnstr_get(x_661, 2);
lean::inc(x_665);
x_666 = lean::cnstr_get(x_661, 3);
lean::inc(x_666);
if (lean::is_exclusive(x_661)) {
 lean::cnstr_release(x_661, 0);
 lean::cnstr_release(x_661, 1);
 lean::cnstr_release(x_661, 2);
 lean::cnstr_release(x_661, 3);
 x_667 = x_661;
} else {
 lean::dec_ref(x_661);
 x_667 = lean::box(0);
}
x_668 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_668, 0, x_642);
lean::cnstr_set(x_668, 1, x_662);
lean::cnstr_set(x_2, 1, x_665);
lean::cnstr_set(x_2, 0, x_668);
if (lean::is_scalar(x_667)) {
 x_669 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_669 = x_667;
}
lean::cnstr_set(x_669, 0, x_663);
lean::cnstr_set(x_669, 1, x_664);
lean::cnstr_set(x_669, 2, x_2);
lean::cnstr_set(x_669, 3, x_666);
x_2 = x_542;
x_3 = x_669;
goto _start;
}
}
}
case 2:
{
obj* x_671; obj* x_672; obj* x_673; obj* x_674; 
x_671 = lean::cnstr_get(x_548, 1);
lean::inc(x_671);
lean::dec(x_548);
x_672 = lean::cnstr_get(x_606, 0);
lean::inc(x_672);
lean::dec(x_606);
x_673 = lean::cnstr_get(x_640, 0);
lean::inc(x_673);
lean::dec(x_640);
x_674 = l___private_init_lean_expander_1__popStxArg(x_671, x_4);
if (lean::obj_tag(x_674) == 0)
{
uint8 x_675; 
lean::dec(x_673);
lean::dec(x_672);
lean::free_heap_obj(x_607);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_675 = !lean::is_exclusive(x_674);
if (x_675 == 0)
{
return x_674;
}
else
{
obj* x_676; obj* x_677; 
x_676 = lean::cnstr_get(x_674, 0);
lean::inc(x_676);
lean::dec(x_674);
x_677 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_677, 0, x_676);
return x_677;
}
}
else
{
obj* x_678; obj* x_679; obj* x_680; 
x_678 = lean::cnstr_get(x_674, 0);
lean::inc(x_678);
lean::dec(x_674);
x_679 = lean::cnstr_get(x_678, 1);
lean::inc(x_679);
x_680 = lean::cnstr_get(x_679, 3);
lean::inc(x_680);
if (lean::obj_tag(x_680) == 0)
{
obj* x_681; obj* x_682; 
lean::dec(x_678);
lean::dec(x_673);
lean::dec(x_672);
lean::free_heap_obj(x_2);
lean::inc(x_1);
lean::cnstr_set(x_607, 0, x_1);
x_681 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_682 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_607, x_681, x_679, x_4);
lean::dec(x_679);
lean::dec(x_607);
if (lean::obj_tag(x_682) == 0)
{
uint8 x_683; 
lean::dec(x_542);
lean::dec(x_1);
x_683 = !lean::is_exclusive(x_682);
if (x_683 == 0)
{
return x_682;
}
else
{
obj* x_684; obj* x_685; 
x_684 = lean::cnstr_get(x_682, 0);
lean::inc(x_684);
lean::dec(x_682);
x_685 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_685, 0, x_684);
return x_685;
}
}
else
{
obj* x_686; obj* x_687; 
x_686 = lean::cnstr_get(x_682, 0);
lean::inc(x_686);
lean::dec(x_682);
x_687 = lean::cnstr_get(x_686, 1);
lean::inc(x_687);
lean::dec(x_686);
x_2 = x_542;
x_3 = x_687;
goto _start;
}
}
else
{
uint8 x_689; 
lean::free_heap_obj(x_607);
x_689 = !lean::is_exclusive(x_678);
if (x_689 == 0)
{
obj* x_690; obj* x_691; uint8 x_692; 
x_690 = lean::cnstr_get(x_678, 0);
x_691 = lean::cnstr_get(x_678, 1);
lean::dec(x_691);
x_692 = !lean::is_exclusive(x_679);
if (x_692 == 0)
{
obj* x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; obj* x_710; obj* x_711; obj* x_712; obj* x_713; obj* x_714; obj* x_715; 
x_693 = lean::cnstr_get(x_679, 2);
x_694 = lean::cnstr_get(x_679, 3);
lean::dec(x_694);
x_695 = lean::cnstr_get(x_680, 0);
lean::inc(x_695);
x_696 = l_Lean_Parser_Term_lambda_HasView;
x_697 = lean::cnstr_get(x_696, 1);
lean::inc(x_697);
x_698 = lean::box(0);
x_699 = lean::cnstr_get(x_673, 3);
lean::inc(x_699);
x_700 = lean::box(0);
lean::cnstr_set(x_2, 1, x_700);
lean::cnstr_set(x_2, 0, x_699);
x_701 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_702 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_702, 0, x_701);
lean::cnstr_set(x_702, 1, x_698);
x_703 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_703, 0, x_702);
x_704 = lean::cnstr_get(x_673, 5);
lean::inc(x_704);
lean::dec(x_673);
x_705 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_706 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_707 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_707, 0, x_705);
lean::cnstr_set(x_707, 1, x_703);
lean::cnstr_set(x_707, 2, x_706);
lean::cnstr_set(x_707, 3, x_704);
lean::inc(x_697);
x_708 = lean::apply_1(x_697, x_707);
x_709 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_709, 0, x_705);
lean::cnstr_set(x_709, 1, x_695);
lean::cnstr_set(x_709, 2, x_706);
lean::cnstr_set(x_709, 3, x_690);
x_710 = lean::apply_1(x_697, x_709);
x_711 = l_Lean_Parser_Term_app_HasView;
x_712 = lean::cnstr_get(x_711, 1);
lean::inc(x_712);
x_713 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_713, 0, x_708);
lean::cnstr_set(x_713, 1, x_710);
x_714 = lean::apply_1(x_712, x_713);
lean::cnstr_set(x_678, 1, x_714);
lean::cnstr_set(x_678, 0, x_672);
x_715 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_715, 0, x_678);
lean::cnstr_set(x_715, 1, x_693);
lean::cnstr_set(x_679, 2, x_715);
x_2 = x_542;
x_3 = x_679;
goto _start;
}
else
{
obj* x_717; obj* x_718; obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; obj* x_725; obj* x_726; obj* x_727; obj* x_728; obj* x_729; obj* x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; 
x_717 = lean::cnstr_get(x_679, 0);
x_718 = lean::cnstr_get(x_679, 1);
x_719 = lean::cnstr_get(x_679, 2);
lean::inc(x_719);
lean::inc(x_718);
lean::inc(x_717);
lean::dec(x_679);
x_720 = lean::cnstr_get(x_680, 0);
lean::inc(x_720);
x_721 = l_Lean_Parser_Term_lambda_HasView;
x_722 = lean::cnstr_get(x_721, 1);
lean::inc(x_722);
x_723 = lean::box(0);
x_724 = lean::cnstr_get(x_673, 3);
lean::inc(x_724);
x_725 = lean::box(0);
lean::cnstr_set(x_2, 1, x_725);
lean::cnstr_set(x_2, 0, x_724);
x_726 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_727 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_727, 0, x_726);
lean::cnstr_set(x_727, 1, x_723);
x_728 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_728, 0, x_727);
x_729 = lean::cnstr_get(x_673, 5);
lean::inc(x_729);
lean::dec(x_673);
x_730 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_731 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_732 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_732, 0, x_730);
lean::cnstr_set(x_732, 1, x_728);
lean::cnstr_set(x_732, 2, x_731);
lean::cnstr_set(x_732, 3, x_729);
lean::inc(x_722);
x_733 = lean::apply_1(x_722, x_732);
x_734 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_734, 0, x_730);
lean::cnstr_set(x_734, 1, x_720);
lean::cnstr_set(x_734, 2, x_731);
lean::cnstr_set(x_734, 3, x_690);
x_735 = lean::apply_1(x_722, x_734);
x_736 = l_Lean_Parser_Term_app_HasView;
x_737 = lean::cnstr_get(x_736, 1);
lean::inc(x_737);
x_738 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_738, 0, x_733);
lean::cnstr_set(x_738, 1, x_735);
x_739 = lean::apply_1(x_737, x_738);
lean::cnstr_set(x_678, 1, x_739);
lean::cnstr_set(x_678, 0, x_672);
x_740 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_740, 0, x_678);
lean::cnstr_set(x_740, 1, x_719);
x_741 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_741, 0, x_717);
lean::cnstr_set(x_741, 1, x_718);
lean::cnstr_set(x_741, 2, x_740);
lean::cnstr_set(x_741, 3, x_680);
x_2 = x_542;
x_3 = x_741;
goto _start;
}
}
else
{
obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; obj* x_751; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; obj* x_761; obj* x_762; obj* x_763; obj* x_764; obj* x_765; obj* x_766; obj* x_767; obj* x_768; obj* x_769; obj* x_770; 
x_743 = lean::cnstr_get(x_678, 0);
lean::inc(x_743);
lean::dec(x_678);
x_744 = lean::cnstr_get(x_679, 0);
lean::inc(x_744);
x_745 = lean::cnstr_get(x_679, 1);
lean::inc(x_745);
x_746 = lean::cnstr_get(x_679, 2);
lean::inc(x_746);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_747 = x_679;
} else {
 lean::dec_ref(x_679);
 x_747 = lean::box(0);
}
x_748 = lean::cnstr_get(x_680, 0);
lean::inc(x_748);
x_749 = l_Lean_Parser_Term_lambda_HasView;
x_750 = lean::cnstr_get(x_749, 1);
lean::inc(x_750);
x_751 = lean::box(0);
x_752 = lean::cnstr_get(x_673, 3);
lean::inc(x_752);
x_753 = lean::box(0);
lean::cnstr_set(x_2, 1, x_753);
lean::cnstr_set(x_2, 0, x_752);
x_754 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_755 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_755, 0, x_754);
lean::cnstr_set(x_755, 1, x_751);
x_756 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_756, 0, x_755);
x_757 = lean::cnstr_get(x_673, 5);
lean::inc(x_757);
lean::dec(x_673);
x_758 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_759 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_760 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_760, 0, x_758);
lean::cnstr_set(x_760, 1, x_756);
lean::cnstr_set(x_760, 2, x_759);
lean::cnstr_set(x_760, 3, x_757);
lean::inc(x_750);
x_761 = lean::apply_1(x_750, x_760);
x_762 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_762, 0, x_758);
lean::cnstr_set(x_762, 1, x_748);
lean::cnstr_set(x_762, 2, x_759);
lean::cnstr_set(x_762, 3, x_743);
x_763 = lean::apply_1(x_750, x_762);
x_764 = l_Lean_Parser_Term_app_HasView;
x_765 = lean::cnstr_get(x_764, 1);
lean::inc(x_765);
x_766 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_766, 0, x_761);
lean::cnstr_set(x_766, 1, x_763);
x_767 = lean::apply_1(x_765, x_766);
x_768 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_768, 0, x_672);
lean::cnstr_set(x_768, 1, x_767);
x_769 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_769, 0, x_768);
lean::cnstr_set(x_769, 1, x_746);
if (lean::is_scalar(x_747)) {
 x_770 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_770 = x_747;
}
lean::cnstr_set(x_770, 0, x_744);
lean::cnstr_set(x_770, 1, x_745);
lean::cnstr_set(x_770, 2, x_769);
lean::cnstr_set(x_770, 3, x_680);
x_2 = x_542;
x_3 = x_770;
goto _start;
}
}
}
}
default: 
{
obj* x_772; obj* x_773; obj* x_774; 
lean::dec(x_640);
lean::dec(x_606);
lean::free_heap_obj(x_2);
x_772 = lean::cnstr_get(x_548, 1);
lean::inc(x_772);
lean::dec(x_548);
lean::inc(x_1);
lean::cnstr_set(x_607, 0, x_1);
x_773 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_774 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_607, x_773, x_772, x_4);
lean::dec(x_772);
lean::dec(x_607);
if (lean::obj_tag(x_774) == 0)
{
uint8 x_775; 
lean::dec(x_542);
lean::dec(x_1);
x_775 = !lean::is_exclusive(x_774);
if (x_775 == 0)
{
return x_774;
}
else
{
obj* x_776; obj* x_777; 
x_776 = lean::cnstr_get(x_774, 0);
lean::inc(x_776);
lean::dec(x_774);
x_777 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_777, 0, x_776);
return x_777;
}
}
else
{
obj* x_778; obj* x_779; 
x_778 = lean::cnstr_get(x_774, 0);
lean::inc(x_778);
lean::dec(x_774);
x_779 = lean::cnstr_get(x_778, 1);
lean::inc(x_779);
lean::dec(x_778);
x_2 = x_542;
x_3 = x_779;
goto _start;
}
}
}
}
else
{
obj* x_781; obj* x_782; 
x_781 = lean::cnstr_get(x_607, 0);
lean::inc(x_781);
lean::dec(x_607);
x_782 = lean::cnstr_get(x_781, 1);
lean::inc(x_782);
lean::dec(x_781);
switch (lean::obj_tag(x_782)) {
case 0:
{
obj* x_783; obj* x_784; obj* x_785; 
lean::dec(x_782);
x_783 = lean::cnstr_get(x_548, 1);
lean::inc(x_783);
lean::dec(x_548);
x_784 = lean::cnstr_get(x_606, 0);
lean::inc(x_784);
lean::dec(x_606);
x_785 = l___private_init_lean_expander_1__popStxArg(x_783, x_4);
if (lean::obj_tag(x_785) == 0)
{
obj* x_786; obj* x_787; obj* x_788; 
lean::dec(x_784);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_786 = lean::cnstr_get(x_785, 0);
lean::inc(x_786);
if (lean::is_exclusive(x_785)) {
 lean::cnstr_release(x_785, 0);
 x_787 = x_785;
} else {
 lean::dec_ref(x_785);
 x_787 = lean::box(0);
}
if (lean::is_scalar(x_787)) {
 x_788 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_788 = x_787;
}
lean::cnstr_set(x_788, 0, x_786);
return x_788;
}
else
{
obj* x_789; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; obj* x_796; obj* x_797; obj* x_798; obj* x_799; 
x_789 = lean::cnstr_get(x_785, 0);
lean::inc(x_789);
lean::dec(x_785);
x_790 = lean::cnstr_get(x_789, 1);
lean::inc(x_790);
x_791 = lean::cnstr_get(x_789, 0);
lean::inc(x_791);
if (lean::is_exclusive(x_789)) {
 lean::cnstr_release(x_789, 0);
 lean::cnstr_release(x_789, 1);
 x_792 = x_789;
} else {
 lean::dec_ref(x_789);
 x_792 = lean::box(0);
}
x_793 = lean::cnstr_get(x_790, 0);
lean::inc(x_793);
x_794 = lean::cnstr_get(x_790, 1);
lean::inc(x_794);
x_795 = lean::cnstr_get(x_790, 2);
lean::inc(x_795);
x_796 = lean::cnstr_get(x_790, 3);
lean::inc(x_796);
if (lean::is_exclusive(x_790)) {
 lean::cnstr_release(x_790, 0);
 lean::cnstr_release(x_790, 1);
 lean::cnstr_release(x_790, 2);
 lean::cnstr_release(x_790, 3);
 x_797 = x_790;
} else {
 lean::dec_ref(x_790);
 x_797 = lean::box(0);
}
if (lean::is_scalar(x_792)) {
 x_798 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_798 = x_792;
}
lean::cnstr_set(x_798, 0, x_784);
lean::cnstr_set(x_798, 1, x_791);
lean::cnstr_set(x_2, 1, x_795);
lean::cnstr_set(x_2, 0, x_798);
if (lean::is_scalar(x_797)) {
 x_799 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_799 = x_797;
}
lean::cnstr_set(x_799, 0, x_793);
lean::cnstr_set(x_799, 1, x_794);
lean::cnstr_set(x_799, 2, x_2);
lean::cnstr_set(x_799, 3, x_796);
x_2 = x_542;
x_3 = x_799;
goto _start;
}
}
case 2:
{
obj* x_801; obj* x_802; obj* x_803; obj* x_804; 
x_801 = lean::cnstr_get(x_548, 1);
lean::inc(x_801);
lean::dec(x_548);
x_802 = lean::cnstr_get(x_606, 0);
lean::inc(x_802);
lean::dec(x_606);
x_803 = lean::cnstr_get(x_782, 0);
lean::inc(x_803);
lean::dec(x_782);
x_804 = l___private_init_lean_expander_1__popStxArg(x_801, x_4);
if (lean::obj_tag(x_804) == 0)
{
obj* x_805; obj* x_806; obj* x_807; 
lean::dec(x_803);
lean::dec(x_802);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_805 = lean::cnstr_get(x_804, 0);
lean::inc(x_805);
if (lean::is_exclusive(x_804)) {
 lean::cnstr_release(x_804, 0);
 x_806 = x_804;
} else {
 lean::dec_ref(x_804);
 x_806 = lean::box(0);
}
if (lean::is_scalar(x_806)) {
 x_807 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_807 = x_806;
}
lean::cnstr_set(x_807, 0, x_805);
return x_807;
}
else
{
obj* x_808; obj* x_809; obj* x_810; 
x_808 = lean::cnstr_get(x_804, 0);
lean::inc(x_808);
lean::dec(x_804);
x_809 = lean::cnstr_get(x_808, 1);
lean::inc(x_809);
x_810 = lean::cnstr_get(x_809, 3);
lean::inc(x_810);
if (lean::obj_tag(x_810) == 0)
{
obj* x_811; obj* x_812; obj* x_813; 
lean::dec(x_808);
lean::dec(x_803);
lean::dec(x_802);
lean::free_heap_obj(x_2);
lean::inc(x_1);
x_811 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_811, 0, x_1);
x_812 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_813 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_811, x_812, x_809, x_4);
lean::dec(x_809);
lean::dec(x_811);
if (lean::obj_tag(x_813) == 0)
{
obj* x_814; obj* x_815; obj* x_816; 
lean::dec(x_542);
lean::dec(x_1);
x_814 = lean::cnstr_get(x_813, 0);
lean::inc(x_814);
if (lean::is_exclusive(x_813)) {
 lean::cnstr_release(x_813, 0);
 x_815 = x_813;
} else {
 lean::dec_ref(x_813);
 x_815 = lean::box(0);
}
if (lean::is_scalar(x_815)) {
 x_816 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_816 = x_815;
}
lean::cnstr_set(x_816, 0, x_814);
return x_816;
}
else
{
obj* x_817; obj* x_818; 
x_817 = lean::cnstr_get(x_813, 0);
lean::inc(x_817);
lean::dec(x_813);
x_818 = lean::cnstr_get(x_817, 1);
lean::inc(x_818);
lean::dec(x_817);
x_2 = x_542;
x_3 = x_818;
goto _start;
}
}
else
{
obj* x_820; obj* x_821; obj* x_822; obj* x_823; obj* x_824; obj* x_825; obj* x_826; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_838; obj* x_839; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; obj* x_846; obj* x_847; obj* x_848; 
x_820 = lean::cnstr_get(x_808, 0);
lean::inc(x_820);
if (lean::is_exclusive(x_808)) {
 lean::cnstr_release(x_808, 0);
 lean::cnstr_release(x_808, 1);
 x_821 = x_808;
} else {
 lean::dec_ref(x_808);
 x_821 = lean::box(0);
}
x_822 = lean::cnstr_get(x_809, 0);
lean::inc(x_822);
x_823 = lean::cnstr_get(x_809, 1);
lean::inc(x_823);
x_824 = lean::cnstr_get(x_809, 2);
lean::inc(x_824);
if (lean::is_exclusive(x_809)) {
 lean::cnstr_release(x_809, 0);
 lean::cnstr_release(x_809, 1);
 lean::cnstr_release(x_809, 2);
 lean::cnstr_release(x_809, 3);
 x_825 = x_809;
} else {
 lean::dec_ref(x_809);
 x_825 = lean::box(0);
}
x_826 = lean::cnstr_get(x_810, 0);
lean::inc(x_826);
x_827 = l_Lean_Parser_Term_lambda_HasView;
x_828 = lean::cnstr_get(x_827, 1);
lean::inc(x_828);
x_829 = lean::box(0);
x_830 = lean::cnstr_get(x_803, 3);
lean::inc(x_830);
x_831 = lean::box(0);
lean::cnstr_set(x_2, 1, x_831);
lean::cnstr_set(x_2, 0, x_830);
x_832 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_833 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_833, 0, x_832);
lean::cnstr_set(x_833, 1, x_829);
x_834 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_834, 0, x_833);
x_835 = lean::cnstr_get(x_803, 5);
lean::inc(x_835);
lean::dec(x_803);
x_836 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_837 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_838 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_838, 0, x_836);
lean::cnstr_set(x_838, 1, x_834);
lean::cnstr_set(x_838, 2, x_837);
lean::cnstr_set(x_838, 3, x_835);
lean::inc(x_828);
x_839 = lean::apply_1(x_828, x_838);
x_840 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_840, 0, x_836);
lean::cnstr_set(x_840, 1, x_826);
lean::cnstr_set(x_840, 2, x_837);
lean::cnstr_set(x_840, 3, x_820);
x_841 = lean::apply_1(x_828, x_840);
x_842 = l_Lean_Parser_Term_app_HasView;
x_843 = lean::cnstr_get(x_842, 1);
lean::inc(x_843);
x_844 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_844, 0, x_839);
lean::cnstr_set(x_844, 1, x_841);
x_845 = lean::apply_1(x_843, x_844);
if (lean::is_scalar(x_821)) {
 x_846 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_846 = x_821;
}
lean::cnstr_set(x_846, 0, x_802);
lean::cnstr_set(x_846, 1, x_845);
x_847 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_847, 0, x_846);
lean::cnstr_set(x_847, 1, x_824);
if (lean::is_scalar(x_825)) {
 x_848 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_848 = x_825;
}
lean::cnstr_set(x_848, 0, x_822);
lean::cnstr_set(x_848, 1, x_823);
lean::cnstr_set(x_848, 2, x_847);
lean::cnstr_set(x_848, 3, x_810);
x_2 = x_542;
x_3 = x_848;
goto _start;
}
}
}
default: 
{
obj* x_850; obj* x_851; obj* x_852; obj* x_853; 
lean::dec(x_782);
lean::dec(x_606);
lean::free_heap_obj(x_2);
x_850 = lean::cnstr_get(x_548, 1);
lean::inc(x_850);
lean::dec(x_548);
lean::inc(x_1);
x_851 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_851, 0, x_1);
x_852 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_853 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_851, x_852, x_850, x_4);
lean::dec(x_850);
lean::dec(x_851);
if (lean::obj_tag(x_853) == 0)
{
obj* x_854; obj* x_855; obj* x_856; 
lean::dec(x_542);
lean::dec(x_1);
x_854 = lean::cnstr_get(x_853, 0);
lean::inc(x_854);
if (lean::is_exclusive(x_853)) {
 lean::cnstr_release(x_853, 0);
 x_855 = x_853;
} else {
 lean::dec_ref(x_853);
 x_855 = lean::box(0);
}
if (lean::is_scalar(x_855)) {
 x_856 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_856 = x_855;
}
lean::cnstr_set(x_856, 0, x_854);
return x_856;
}
else
{
obj* x_857; obj* x_858; 
x_857 = lean::cnstr_get(x_853, 0);
lean::inc(x_857);
lean::dec(x_853);
x_858 = lean::cnstr_get(x_857, 1);
lean::inc(x_858);
lean::dec(x_857);
x_2 = x_542;
x_3 = x_858;
goto _start;
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
obj* x_860; 
x_860 = lean::cnstr_get(x_549, 0);
lean::inc(x_860);
lean::dec(x_549);
switch (lean::obj_tag(x_860)) {
case 0:
{
obj* x_861; obj* x_862; 
lean::dec(x_860);
x_861 = lean::cnstr_get(x_548, 1);
lean::inc(x_861);
lean::dec(x_548);
x_862 = l___private_init_lean_expander_1__popStxArg(x_861, x_4);
if (lean::obj_tag(x_862) == 0)
{
obj* x_863; obj* x_864; obj* x_865; 
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_863 = lean::cnstr_get(x_862, 0);
lean::inc(x_863);
if (lean::is_exclusive(x_862)) {
 lean::cnstr_release(x_862, 0);
 x_864 = x_862;
} else {
 lean::dec_ref(x_862);
 x_864 = lean::box(0);
}
if (lean::is_scalar(x_864)) {
 x_865 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_865 = x_864;
}
lean::cnstr_set(x_865, 0, x_863);
return x_865;
}
else
{
obj* x_866; obj* x_867; obj* x_868; obj* x_869; obj* x_870; obj* x_871; obj* x_872; obj* x_873; obj* x_874; obj* x_875; obj* x_876; obj* x_877; obj* x_878; obj* x_879; obj* x_880; obj* x_881; 
x_866 = lean::cnstr_get(x_862, 0);
lean::inc(x_866);
lean::dec(x_862);
x_867 = lean::cnstr_get(x_866, 1);
lean::inc(x_867);
x_868 = lean::cnstr_get(x_866, 0);
lean::inc(x_868);
lean::dec(x_866);
x_869 = lean::cnstr_get(x_867, 0);
lean::inc(x_869);
x_870 = lean::cnstr_get(x_867, 1);
lean::inc(x_870);
x_871 = lean::cnstr_get(x_867, 2);
lean::inc(x_871);
if (lean::is_exclusive(x_867)) {
 lean::cnstr_release(x_867, 0);
 lean::cnstr_release(x_867, 1);
 lean::cnstr_release(x_867, 2);
 lean::cnstr_release(x_867, 3);
 x_872 = x_867;
} else {
 lean::dec_ref(x_867);
 x_872 = lean::box(0);
}
x_873 = l_Lean_Parser_Term_binderIdent_HasView;
x_874 = lean::cnstr_get(x_873, 0);
lean::inc(x_874);
x_875 = lean::apply_1(x_874, x_868);
x_876 = lean::box(0);
lean::cnstr_set(x_2, 1, x_876);
lean::cnstr_set(x_2, 0, x_875);
x_877 = lean::box(0);
x_878 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_878, 0, x_2);
lean::cnstr_set(x_878, 1, x_877);
x_879 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_879, 0, x_878);
x_880 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_880, 0, x_879);
if (lean::is_scalar(x_872)) {
 x_881 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_881 = x_872;
}
lean::cnstr_set(x_881, 0, x_869);
lean::cnstr_set(x_881, 1, x_870);
lean::cnstr_set(x_881, 2, x_871);
lean::cnstr_set(x_881, 3, x_880);
x_2 = x_542;
x_3 = x_881;
goto _start;
}
}
case 1:
{
obj* x_883; obj* x_884; 
lean::dec(x_860);
lean::free_heap_obj(x_2);
x_883 = lean::cnstr_get(x_548, 1);
lean::inc(x_883);
lean::dec(x_548);
x_884 = l___private_init_lean_expander_1__popStxArg(x_883, x_4);
if (lean::obj_tag(x_884) == 0)
{
obj* x_885; obj* x_886; obj* x_887; 
lean::dec(x_542);
lean::dec(x_1);
x_885 = lean::cnstr_get(x_884, 0);
lean::inc(x_885);
if (lean::is_exclusive(x_884)) {
 lean::cnstr_release(x_884, 0);
 x_886 = x_884;
} else {
 lean::dec_ref(x_884);
 x_886 = lean::box(0);
}
if (lean::is_scalar(x_886)) {
 x_887 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_887 = x_886;
}
lean::cnstr_set(x_887, 0, x_885);
return x_887;
}
else
{
obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_896; obj* x_897; obj* x_898; obj* x_899; 
x_888 = lean::cnstr_get(x_884, 0);
lean::inc(x_888);
lean::dec(x_884);
x_889 = lean::cnstr_get(x_888, 1);
lean::inc(x_889);
x_890 = lean::cnstr_get(x_888, 0);
lean::inc(x_890);
lean::dec(x_888);
x_891 = lean::cnstr_get(x_889, 0);
lean::inc(x_891);
x_892 = lean::cnstr_get(x_889, 1);
lean::inc(x_892);
x_893 = lean::cnstr_get(x_889, 2);
lean::inc(x_893);
if (lean::is_exclusive(x_889)) {
 lean::cnstr_release(x_889, 0);
 lean::cnstr_release(x_889, 1);
 lean::cnstr_release(x_889, 2);
 lean::cnstr_release(x_889, 3);
 x_894 = x_889;
} else {
 lean::dec_ref(x_889);
 x_894 = lean::box(0);
}
x_895 = l_Lean_Parser_Term_binders_HasView;
x_896 = lean::cnstr_get(x_895, 0);
lean::inc(x_896);
x_897 = lean::apply_1(x_896, x_890);
x_898 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_898, 0, x_897);
if (lean::is_scalar(x_894)) {
 x_899 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_899 = x_894;
}
lean::cnstr_set(x_899, 0, x_891);
lean::cnstr_set(x_899, 1, x_892);
lean::cnstr_set(x_899, 2, x_893);
lean::cnstr_set(x_899, 3, x_898);
x_2 = x_542;
x_3 = x_899;
goto _start;
}
}
default: 
{
obj* x_901; obj* x_902; 
x_901 = lean::cnstr_get(x_860, 0);
lean::inc(x_901);
lean::dec(x_860);
x_902 = lean::cnstr_get(x_901, 1);
lean::inc(x_902);
if (lean::obj_tag(x_902) == 0)
{
obj* x_903; obj* x_904; obj* x_905; 
x_903 = lean::cnstr_get(x_548, 1);
lean::inc(x_903);
lean::dec(x_548);
x_904 = lean::cnstr_get(x_901, 0);
lean::inc(x_904);
lean::dec(x_901);
x_905 = l___private_init_lean_expander_1__popStxArg(x_903, x_4);
if (lean::obj_tag(x_905) == 0)
{
obj* x_906; obj* x_907; obj* x_908; 
lean::dec(x_904);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_906 = lean::cnstr_get(x_905, 0);
lean::inc(x_906);
if (lean::is_exclusive(x_905)) {
 lean::cnstr_release(x_905, 0);
 x_907 = x_905;
} else {
 lean::dec_ref(x_905);
 x_907 = lean::box(0);
}
if (lean::is_scalar(x_907)) {
 x_908 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_908 = x_907;
}
lean::cnstr_set(x_908, 0, x_906);
return x_908;
}
else
{
obj* x_909; obj* x_910; obj* x_911; obj* x_912; obj* x_913; obj* x_914; obj* x_915; obj* x_916; obj* x_917; obj* x_918; obj* x_919; 
x_909 = lean::cnstr_get(x_905, 0);
lean::inc(x_909);
lean::dec(x_905);
x_910 = lean::cnstr_get(x_909, 1);
lean::inc(x_910);
x_911 = lean::cnstr_get(x_909, 0);
lean::inc(x_911);
if (lean::is_exclusive(x_909)) {
 lean::cnstr_release(x_909, 0);
 lean::cnstr_release(x_909, 1);
 x_912 = x_909;
} else {
 lean::dec_ref(x_909);
 x_912 = lean::box(0);
}
x_913 = lean::cnstr_get(x_910, 0);
lean::inc(x_913);
x_914 = lean::cnstr_get(x_910, 1);
lean::inc(x_914);
x_915 = lean::cnstr_get(x_910, 2);
lean::inc(x_915);
x_916 = lean::cnstr_get(x_910, 3);
lean::inc(x_916);
if (lean::is_exclusive(x_910)) {
 lean::cnstr_release(x_910, 0);
 lean::cnstr_release(x_910, 1);
 lean::cnstr_release(x_910, 2);
 lean::cnstr_release(x_910, 3);
 x_917 = x_910;
} else {
 lean::dec_ref(x_910);
 x_917 = lean::box(0);
}
if (lean::is_scalar(x_912)) {
 x_918 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_918 = x_912;
}
lean::cnstr_set(x_918, 0, x_904);
lean::cnstr_set(x_918, 1, x_911);
lean::cnstr_set(x_2, 1, x_915);
lean::cnstr_set(x_2, 0, x_918);
if (lean::is_scalar(x_917)) {
 x_919 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_919 = x_917;
}
lean::cnstr_set(x_919, 0, x_913);
lean::cnstr_set(x_919, 1, x_914);
lean::cnstr_set(x_919, 2, x_2);
lean::cnstr_set(x_919, 3, x_916);
x_2 = x_542;
x_3 = x_919;
goto _start;
}
}
else
{
obj* x_921; obj* x_922; obj* x_923; 
x_921 = lean::cnstr_get(x_902, 0);
lean::inc(x_921);
if (lean::is_exclusive(x_902)) {
 lean::cnstr_release(x_902, 0);
 x_922 = x_902;
} else {
 lean::dec_ref(x_902);
 x_922 = lean::box(0);
}
x_923 = lean::cnstr_get(x_921, 1);
lean::inc(x_923);
lean::dec(x_921);
switch (lean::obj_tag(x_923)) {
case 0:
{
obj* x_924; obj* x_925; obj* x_926; 
lean::dec(x_923);
lean::dec(x_922);
x_924 = lean::cnstr_get(x_548, 1);
lean::inc(x_924);
lean::dec(x_548);
x_925 = lean::cnstr_get(x_901, 0);
lean::inc(x_925);
lean::dec(x_901);
x_926 = l___private_init_lean_expander_1__popStxArg(x_924, x_4);
if (lean::obj_tag(x_926) == 0)
{
obj* x_927; obj* x_928; obj* x_929; 
lean::dec(x_925);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_927 = lean::cnstr_get(x_926, 0);
lean::inc(x_927);
if (lean::is_exclusive(x_926)) {
 lean::cnstr_release(x_926, 0);
 x_928 = x_926;
} else {
 lean::dec_ref(x_926);
 x_928 = lean::box(0);
}
if (lean::is_scalar(x_928)) {
 x_929 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_929 = x_928;
}
lean::cnstr_set(x_929, 0, x_927);
return x_929;
}
else
{
obj* x_930; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; 
x_930 = lean::cnstr_get(x_926, 0);
lean::inc(x_930);
lean::dec(x_926);
x_931 = lean::cnstr_get(x_930, 1);
lean::inc(x_931);
x_932 = lean::cnstr_get(x_930, 0);
lean::inc(x_932);
if (lean::is_exclusive(x_930)) {
 lean::cnstr_release(x_930, 0);
 lean::cnstr_release(x_930, 1);
 x_933 = x_930;
} else {
 lean::dec_ref(x_930);
 x_933 = lean::box(0);
}
x_934 = lean::cnstr_get(x_931, 0);
lean::inc(x_934);
x_935 = lean::cnstr_get(x_931, 1);
lean::inc(x_935);
x_936 = lean::cnstr_get(x_931, 2);
lean::inc(x_936);
x_937 = lean::cnstr_get(x_931, 3);
lean::inc(x_937);
if (lean::is_exclusive(x_931)) {
 lean::cnstr_release(x_931, 0);
 lean::cnstr_release(x_931, 1);
 lean::cnstr_release(x_931, 2);
 lean::cnstr_release(x_931, 3);
 x_938 = x_931;
} else {
 lean::dec_ref(x_931);
 x_938 = lean::box(0);
}
if (lean::is_scalar(x_933)) {
 x_939 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_939 = x_933;
}
lean::cnstr_set(x_939, 0, x_925);
lean::cnstr_set(x_939, 1, x_932);
lean::cnstr_set(x_2, 1, x_936);
lean::cnstr_set(x_2, 0, x_939);
if (lean::is_scalar(x_938)) {
 x_940 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_940 = x_938;
}
lean::cnstr_set(x_940, 0, x_934);
lean::cnstr_set(x_940, 1, x_935);
lean::cnstr_set(x_940, 2, x_2);
lean::cnstr_set(x_940, 3, x_937);
x_2 = x_542;
x_3 = x_940;
goto _start;
}
}
case 2:
{
obj* x_942; obj* x_943; obj* x_944; obj* x_945; 
x_942 = lean::cnstr_get(x_548, 1);
lean::inc(x_942);
lean::dec(x_548);
x_943 = lean::cnstr_get(x_901, 0);
lean::inc(x_943);
lean::dec(x_901);
x_944 = lean::cnstr_get(x_923, 0);
lean::inc(x_944);
lean::dec(x_923);
x_945 = l___private_init_lean_expander_1__popStxArg(x_942, x_4);
if (lean::obj_tag(x_945) == 0)
{
obj* x_946; obj* x_947; obj* x_948; 
lean::dec(x_944);
lean::dec(x_943);
lean::dec(x_922);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_946 = lean::cnstr_get(x_945, 0);
lean::inc(x_946);
if (lean::is_exclusive(x_945)) {
 lean::cnstr_release(x_945, 0);
 x_947 = x_945;
} else {
 lean::dec_ref(x_945);
 x_947 = lean::box(0);
}
if (lean::is_scalar(x_947)) {
 x_948 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_948 = x_947;
}
lean::cnstr_set(x_948, 0, x_946);
return x_948;
}
else
{
obj* x_949; obj* x_950; obj* x_951; 
x_949 = lean::cnstr_get(x_945, 0);
lean::inc(x_949);
lean::dec(x_945);
x_950 = lean::cnstr_get(x_949, 1);
lean::inc(x_950);
x_951 = lean::cnstr_get(x_950, 3);
lean::inc(x_951);
if (lean::obj_tag(x_951) == 0)
{
obj* x_952; obj* x_953; obj* x_954; 
lean::dec(x_949);
lean::dec(x_944);
lean::dec(x_943);
lean::free_heap_obj(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_922)) {
 x_952 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_952 = x_922;
}
lean::cnstr_set(x_952, 0, x_1);
x_953 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_954 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_952, x_953, x_950, x_4);
lean::dec(x_950);
lean::dec(x_952);
if (lean::obj_tag(x_954) == 0)
{
obj* x_955; obj* x_956; obj* x_957; 
lean::dec(x_542);
lean::dec(x_1);
x_955 = lean::cnstr_get(x_954, 0);
lean::inc(x_955);
if (lean::is_exclusive(x_954)) {
 lean::cnstr_release(x_954, 0);
 x_956 = x_954;
} else {
 lean::dec_ref(x_954);
 x_956 = lean::box(0);
}
if (lean::is_scalar(x_956)) {
 x_957 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_957 = x_956;
}
lean::cnstr_set(x_957, 0, x_955);
return x_957;
}
else
{
obj* x_958; obj* x_959; 
x_958 = lean::cnstr_get(x_954, 0);
lean::inc(x_958);
lean::dec(x_954);
x_959 = lean::cnstr_get(x_958, 1);
lean::inc(x_959);
lean::dec(x_958);
x_2 = x_542;
x_3 = x_959;
goto _start;
}
}
else
{
obj* x_961; obj* x_962; obj* x_963; obj* x_964; obj* x_965; obj* x_966; obj* x_967; obj* x_968; obj* x_969; obj* x_970; obj* x_971; obj* x_972; obj* x_973; obj* x_974; obj* x_975; obj* x_976; obj* x_977; obj* x_978; obj* x_979; obj* x_980; obj* x_981; obj* x_982; obj* x_983; obj* x_984; obj* x_985; obj* x_986; obj* x_987; obj* x_988; obj* x_989; 
lean::dec(x_922);
x_961 = lean::cnstr_get(x_949, 0);
lean::inc(x_961);
if (lean::is_exclusive(x_949)) {
 lean::cnstr_release(x_949, 0);
 lean::cnstr_release(x_949, 1);
 x_962 = x_949;
} else {
 lean::dec_ref(x_949);
 x_962 = lean::box(0);
}
x_963 = lean::cnstr_get(x_950, 0);
lean::inc(x_963);
x_964 = lean::cnstr_get(x_950, 1);
lean::inc(x_964);
x_965 = lean::cnstr_get(x_950, 2);
lean::inc(x_965);
if (lean::is_exclusive(x_950)) {
 lean::cnstr_release(x_950, 0);
 lean::cnstr_release(x_950, 1);
 lean::cnstr_release(x_950, 2);
 lean::cnstr_release(x_950, 3);
 x_966 = x_950;
} else {
 lean::dec_ref(x_950);
 x_966 = lean::box(0);
}
x_967 = lean::cnstr_get(x_951, 0);
lean::inc(x_967);
x_968 = l_Lean_Parser_Term_lambda_HasView;
x_969 = lean::cnstr_get(x_968, 1);
lean::inc(x_969);
x_970 = lean::box(0);
x_971 = lean::cnstr_get(x_944, 3);
lean::inc(x_971);
x_972 = lean::box(0);
lean::cnstr_set(x_2, 1, x_972);
lean::cnstr_set(x_2, 0, x_971);
x_973 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_974 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_974, 0, x_973);
lean::cnstr_set(x_974, 1, x_970);
x_975 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_975, 0, x_974);
x_976 = lean::cnstr_get(x_944, 5);
lean::inc(x_976);
lean::dec(x_944);
x_977 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_978 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_979 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_979, 0, x_977);
lean::cnstr_set(x_979, 1, x_975);
lean::cnstr_set(x_979, 2, x_978);
lean::cnstr_set(x_979, 3, x_976);
lean::inc(x_969);
x_980 = lean::apply_1(x_969, x_979);
x_981 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_981, 0, x_977);
lean::cnstr_set(x_981, 1, x_967);
lean::cnstr_set(x_981, 2, x_978);
lean::cnstr_set(x_981, 3, x_961);
x_982 = lean::apply_1(x_969, x_981);
x_983 = l_Lean_Parser_Term_app_HasView;
x_984 = lean::cnstr_get(x_983, 1);
lean::inc(x_984);
x_985 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_985, 0, x_980);
lean::cnstr_set(x_985, 1, x_982);
x_986 = lean::apply_1(x_984, x_985);
if (lean::is_scalar(x_962)) {
 x_987 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_987 = x_962;
}
lean::cnstr_set(x_987, 0, x_943);
lean::cnstr_set(x_987, 1, x_986);
x_988 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_988, 0, x_987);
lean::cnstr_set(x_988, 1, x_965);
if (lean::is_scalar(x_966)) {
 x_989 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_989 = x_966;
}
lean::cnstr_set(x_989, 0, x_963);
lean::cnstr_set(x_989, 1, x_964);
lean::cnstr_set(x_989, 2, x_988);
lean::cnstr_set(x_989, 3, x_951);
x_2 = x_542;
x_3 = x_989;
goto _start;
}
}
}
default: 
{
obj* x_991; obj* x_992; obj* x_993; obj* x_994; 
lean::dec(x_923);
lean::dec(x_901);
lean::free_heap_obj(x_2);
x_991 = lean::cnstr_get(x_548, 1);
lean::inc(x_991);
lean::dec(x_548);
lean::inc(x_1);
if (lean::is_scalar(x_922)) {
 x_992 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_992 = x_922;
}
lean::cnstr_set(x_992, 0, x_1);
x_993 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_994 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_992, x_993, x_991, x_4);
lean::dec(x_991);
lean::dec(x_992);
if (lean::obj_tag(x_994) == 0)
{
obj* x_995; obj* x_996; obj* x_997; 
lean::dec(x_542);
lean::dec(x_1);
x_995 = lean::cnstr_get(x_994, 0);
lean::inc(x_995);
if (lean::is_exclusive(x_994)) {
 lean::cnstr_release(x_994, 0);
 x_996 = x_994;
} else {
 lean::dec_ref(x_994);
 x_996 = lean::box(0);
}
if (lean::is_scalar(x_996)) {
 x_997 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_997 = x_996;
}
lean::cnstr_set(x_997, 0, x_995);
return x_997;
}
else
{
obj* x_998; obj* x_999; 
x_998 = lean::cnstr_get(x_994, 0);
lean::inc(x_998);
lean::dec(x_994);
x_999 = lean::cnstr_get(x_998, 1);
lean::inc(x_999);
lean::dec(x_998);
x_2 = x_542;
x_3 = x_999;
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
else
{
obj* x_1001; obj* x_1002; 
x_1001 = lean::cnstr_get(x_2, 1);
lean::inc(x_1001);
lean::dec(x_2);
x_1002 = l___private_init_lean_expander_1__popStxArg(x_3, x_4);
if (lean::obj_tag(x_1002) == 0)
{
obj* x_1003; obj* x_1004; obj* x_1005; 
lean::dec(x_1001);
lean::dec(x_8);
lean::dec(x_1);
x_1003 = lean::cnstr_get(x_1002, 0);
lean::inc(x_1003);
if (lean::is_exclusive(x_1002)) {
 lean::cnstr_release(x_1002, 0);
 x_1004 = x_1002;
} else {
 lean::dec_ref(x_1002);
 x_1004 = lean::box(0);
}
if (lean::is_scalar(x_1004)) {
 x_1005 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1005 = x_1004;
}
lean::cnstr_set(x_1005, 0, x_1003);
return x_1005;
}
else
{
obj* x_1006; obj* x_1007; 
x_1006 = lean::cnstr_get(x_1002, 0);
lean::inc(x_1006);
lean::dec(x_1002);
x_1007 = lean::cnstr_get(x_8, 1);
lean::inc(x_1007);
lean::dec(x_8);
if (lean::obj_tag(x_1007) == 0)
{
obj* x_1008; 
x_1008 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1008);
lean::dec(x_1006);
x_2 = x_1001;
x_3 = x_1008;
goto _start;
}
else
{
obj* x_1010; obj* x_1011; 
x_1010 = lean::cnstr_get(x_1007, 0);
lean::inc(x_1010);
if (lean::is_exclusive(x_1007)) {
 lean::cnstr_release(x_1007, 0);
 x_1011 = x_1007;
} else {
 lean::dec_ref(x_1007);
 x_1011 = lean::box(0);
}
switch (lean::obj_tag(x_1010)) {
case 0:
{
obj* x_1012; obj* x_1013; 
lean::dec(x_1010);
x_1012 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1012);
lean::dec(x_1006);
x_1013 = l___private_init_lean_expander_1__popStxArg(x_1012, x_4);
if (lean::obj_tag(x_1013) == 0)
{
obj* x_1014; obj* x_1015; obj* x_1016; 
lean::dec(x_1011);
lean::dec(x_1001);
lean::dec(x_1);
x_1014 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1014);
if (lean::is_exclusive(x_1013)) {
 lean::cnstr_release(x_1013, 0);
 x_1015 = x_1013;
} else {
 lean::dec_ref(x_1013);
 x_1015 = lean::box(0);
}
if (lean::is_scalar(x_1015)) {
 x_1016 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1016 = x_1015;
}
lean::cnstr_set(x_1016, 0, x_1014);
return x_1016;
}
else
{
obj* x_1017; obj* x_1018; obj* x_1019; obj* x_1020; obj* x_1021; obj* x_1022; obj* x_1023; obj* x_1024; obj* x_1025; obj* x_1026; obj* x_1027; obj* x_1028; obj* x_1029; obj* x_1030; obj* x_1031; obj* x_1032; obj* x_1033; 
x_1017 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1017);
lean::dec(x_1013);
x_1018 = lean::cnstr_get(x_1017, 1);
lean::inc(x_1018);
x_1019 = lean::cnstr_get(x_1017, 0);
lean::inc(x_1019);
lean::dec(x_1017);
x_1020 = lean::cnstr_get(x_1018, 0);
lean::inc(x_1020);
x_1021 = lean::cnstr_get(x_1018, 1);
lean::inc(x_1021);
x_1022 = lean::cnstr_get(x_1018, 2);
lean::inc(x_1022);
if (lean::is_exclusive(x_1018)) {
 lean::cnstr_release(x_1018, 0);
 lean::cnstr_release(x_1018, 1);
 lean::cnstr_release(x_1018, 2);
 lean::cnstr_release(x_1018, 3);
 x_1023 = x_1018;
} else {
 lean::dec_ref(x_1018);
 x_1023 = lean::box(0);
}
x_1024 = l_Lean_Parser_Term_binderIdent_HasView;
x_1025 = lean::cnstr_get(x_1024, 0);
lean::inc(x_1025);
x_1026 = lean::apply_1(x_1025, x_1019);
x_1027 = lean::box(0);
x_1028 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1028, 0, x_1026);
lean::cnstr_set(x_1028, 1, x_1027);
x_1029 = lean::box(0);
x_1030 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1030, 0, x_1028);
lean::cnstr_set(x_1030, 1, x_1029);
x_1031 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1031, 0, x_1030);
if (lean::is_scalar(x_1011)) {
 x_1032 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1032 = x_1011;
}
lean::cnstr_set(x_1032, 0, x_1031);
if (lean::is_scalar(x_1023)) {
 x_1033 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1033 = x_1023;
}
lean::cnstr_set(x_1033, 0, x_1020);
lean::cnstr_set(x_1033, 1, x_1021);
lean::cnstr_set(x_1033, 2, x_1022);
lean::cnstr_set(x_1033, 3, x_1032);
x_2 = x_1001;
x_3 = x_1033;
goto _start;
}
}
case 1:
{
obj* x_1035; obj* x_1036; 
lean::dec(x_1010);
x_1035 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1035);
lean::dec(x_1006);
x_1036 = l___private_init_lean_expander_1__popStxArg(x_1035, x_4);
if (lean::obj_tag(x_1036) == 0)
{
obj* x_1037; obj* x_1038; obj* x_1039; 
lean::dec(x_1011);
lean::dec(x_1001);
lean::dec(x_1);
x_1037 = lean::cnstr_get(x_1036, 0);
lean::inc(x_1037);
if (lean::is_exclusive(x_1036)) {
 lean::cnstr_release(x_1036, 0);
 x_1038 = x_1036;
} else {
 lean::dec_ref(x_1036);
 x_1038 = lean::box(0);
}
if (lean::is_scalar(x_1038)) {
 x_1039 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1039 = x_1038;
}
lean::cnstr_set(x_1039, 0, x_1037);
return x_1039;
}
else
{
obj* x_1040; obj* x_1041; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; obj* x_1046; obj* x_1047; obj* x_1048; obj* x_1049; obj* x_1050; obj* x_1051; 
x_1040 = lean::cnstr_get(x_1036, 0);
lean::inc(x_1040);
lean::dec(x_1036);
x_1041 = lean::cnstr_get(x_1040, 1);
lean::inc(x_1041);
x_1042 = lean::cnstr_get(x_1040, 0);
lean::inc(x_1042);
lean::dec(x_1040);
x_1043 = lean::cnstr_get(x_1041, 0);
lean::inc(x_1043);
x_1044 = lean::cnstr_get(x_1041, 1);
lean::inc(x_1044);
x_1045 = lean::cnstr_get(x_1041, 2);
lean::inc(x_1045);
if (lean::is_exclusive(x_1041)) {
 lean::cnstr_release(x_1041, 0);
 lean::cnstr_release(x_1041, 1);
 lean::cnstr_release(x_1041, 2);
 lean::cnstr_release(x_1041, 3);
 x_1046 = x_1041;
} else {
 lean::dec_ref(x_1041);
 x_1046 = lean::box(0);
}
x_1047 = l_Lean_Parser_Term_binders_HasView;
x_1048 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1048);
x_1049 = lean::apply_1(x_1048, x_1042);
if (lean::is_scalar(x_1011)) {
 x_1050 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1050 = x_1011;
}
lean::cnstr_set(x_1050, 0, x_1049);
if (lean::is_scalar(x_1046)) {
 x_1051 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1051 = x_1046;
}
lean::cnstr_set(x_1051, 0, x_1043);
lean::cnstr_set(x_1051, 1, x_1044);
lean::cnstr_set(x_1051, 2, x_1045);
lean::cnstr_set(x_1051, 3, x_1050);
x_2 = x_1001;
x_3 = x_1051;
goto _start;
}
}
default: 
{
obj* x_1053; obj* x_1054; 
lean::dec(x_1011);
x_1053 = lean::cnstr_get(x_1010, 0);
lean::inc(x_1053);
lean::dec(x_1010);
x_1054 = lean::cnstr_get(x_1053, 1);
lean::inc(x_1054);
if (lean::obj_tag(x_1054) == 0)
{
obj* x_1055; obj* x_1056; obj* x_1057; 
x_1055 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1055);
lean::dec(x_1006);
x_1056 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1056);
lean::dec(x_1053);
x_1057 = l___private_init_lean_expander_1__popStxArg(x_1055, x_4);
if (lean::obj_tag(x_1057) == 0)
{
obj* x_1058; obj* x_1059; obj* x_1060; 
lean::dec(x_1056);
lean::dec(x_1001);
lean::dec(x_1);
x_1058 = lean::cnstr_get(x_1057, 0);
lean::inc(x_1058);
if (lean::is_exclusive(x_1057)) {
 lean::cnstr_release(x_1057, 0);
 x_1059 = x_1057;
} else {
 lean::dec_ref(x_1057);
 x_1059 = lean::box(0);
}
if (lean::is_scalar(x_1059)) {
 x_1060 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1060 = x_1059;
}
lean::cnstr_set(x_1060, 0, x_1058);
return x_1060;
}
else
{
obj* x_1061; obj* x_1062; obj* x_1063; obj* x_1064; obj* x_1065; obj* x_1066; obj* x_1067; obj* x_1068; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; 
x_1061 = lean::cnstr_get(x_1057, 0);
lean::inc(x_1061);
lean::dec(x_1057);
x_1062 = lean::cnstr_get(x_1061, 1);
lean::inc(x_1062);
x_1063 = lean::cnstr_get(x_1061, 0);
lean::inc(x_1063);
if (lean::is_exclusive(x_1061)) {
 lean::cnstr_release(x_1061, 0);
 lean::cnstr_release(x_1061, 1);
 x_1064 = x_1061;
} else {
 lean::dec_ref(x_1061);
 x_1064 = lean::box(0);
}
x_1065 = lean::cnstr_get(x_1062, 0);
lean::inc(x_1065);
x_1066 = lean::cnstr_get(x_1062, 1);
lean::inc(x_1066);
x_1067 = lean::cnstr_get(x_1062, 2);
lean::inc(x_1067);
x_1068 = lean::cnstr_get(x_1062, 3);
lean::inc(x_1068);
if (lean::is_exclusive(x_1062)) {
 lean::cnstr_release(x_1062, 0);
 lean::cnstr_release(x_1062, 1);
 lean::cnstr_release(x_1062, 2);
 lean::cnstr_release(x_1062, 3);
 x_1069 = x_1062;
} else {
 lean::dec_ref(x_1062);
 x_1069 = lean::box(0);
}
if (lean::is_scalar(x_1064)) {
 x_1070 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1070 = x_1064;
}
lean::cnstr_set(x_1070, 0, x_1056);
lean::cnstr_set(x_1070, 1, x_1063);
x_1071 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1071, 0, x_1070);
lean::cnstr_set(x_1071, 1, x_1067);
if (lean::is_scalar(x_1069)) {
 x_1072 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1072 = x_1069;
}
lean::cnstr_set(x_1072, 0, x_1065);
lean::cnstr_set(x_1072, 1, x_1066);
lean::cnstr_set(x_1072, 2, x_1071);
lean::cnstr_set(x_1072, 3, x_1068);
x_2 = x_1001;
x_3 = x_1072;
goto _start;
}
}
else
{
obj* x_1074; obj* x_1075; obj* x_1076; 
x_1074 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1074);
if (lean::is_exclusive(x_1054)) {
 lean::cnstr_release(x_1054, 0);
 x_1075 = x_1054;
} else {
 lean::dec_ref(x_1054);
 x_1075 = lean::box(0);
}
x_1076 = lean::cnstr_get(x_1074, 1);
lean::inc(x_1076);
lean::dec(x_1074);
switch (lean::obj_tag(x_1076)) {
case 0:
{
obj* x_1077; obj* x_1078; obj* x_1079; 
lean::dec(x_1076);
lean::dec(x_1075);
x_1077 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1077);
lean::dec(x_1006);
x_1078 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1078);
lean::dec(x_1053);
x_1079 = l___private_init_lean_expander_1__popStxArg(x_1077, x_4);
if (lean::obj_tag(x_1079) == 0)
{
obj* x_1080; obj* x_1081; obj* x_1082; 
lean::dec(x_1078);
lean::dec(x_1001);
lean::dec(x_1);
x_1080 = lean::cnstr_get(x_1079, 0);
lean::inc(x_1080);
if (lean::is_exclusive(x_1079)) {
 lean::cnstr_release(x_1079, 0);
 x_1081 = x_1079;
} else {
 lean::dec_ref(x_1079);
 x_1081 = lean::box(0);
}
if (lean::is_scalar(x_1081)) {
 x_1082 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1082 = x_1081;
}
lean::cnstr_set(x_1082, 0, x_1080);
return x_1082;
}
else
{
obj* x_1083; obj* x_1084; obj* x_1085; obj* x_1086; obj* x_1087; obj* x_1088; obj* x_1089; obj* x_1090; obj* x_1091; obj* x_1092; obj* x_1093; obj* x_1094; 
x_1083 = lean::cnstr_get(x_1079, 0);
lean::inc(x_1083);
lean::dec(x_1079);
x_1084 = lean::cnstr_get(x_1083, 1);
lean::inc(x_1084);
x_1085 = lean::cnstr_get(x_1083, 0);
lean::inc(x_1085);
if (lean::is_exclusive(x_1083)) {
 lean::cnstr_release(x_1083, 0);
 lean::cnstr_release(x_1083, 1);
 x_1086 = x_1083;
} else {
 lean::dec_ref(x_1083);
 x_1086 = lean::box(0);
}
x_1087 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1087);
x_1088 = lean::cnstr_get(x_1084, 1);
lean::inc(x_1088);
x_1089 = lean::cnstr_get(x_1084, 2);
lean::inc(x_1089);
x_1090 = lean::cnstr_get(x_1084, 3);
lean::inc(x_1090);
if (lean::is_exclusive(x_1084)) {
 lean::cnstr_release(x_1084, 0);
 lean::cnstr_release(x_1084, 1);
 lean::cnstr_release(x_1084, 2);
 lean::cnstr_release(x_1084, 3);
 x_1091 = x_1084;
} else {
 lean::dec_ref(x_1084);
 x_1091 = lean::box(0);
}
if (lean::is_scalar(x_1086)) {
 x_1092 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1092 = x_1086;
}
lean::cnstr_set(x_1092, 0, x_1078);
lean::cnstr_set(x_1092, 1, x_1085);
x_1093 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1093, 0, x_1092);
lean::cnstr_set(x_1093, 1, x_1089);
if (lean::is_scalar(x_1091)) {
 x_1094 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1094 = x_1091;
}
lean::cnstr_set(x_1094, 0, x_1087);
lean::cnstr_set(x_1094, 1, x_1088);
lean::cnstr_set(x_1094, 2, x_1093);
lean::cnstr_set(x_1094, 3, x_1090);
x_2 = x_1001;
x_3 = x_1094;
goto _start;
}
}
case 2:
{
obj* x_1096; obj* x_1097; obj* x_1098; obj* x_1099; 
x_1096 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1096);
lean::dec(x_1006);
x_1097 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1097);
lean::dec(x_1053);
x_1098 = lean::cnstr_get(x_1076, 0);
lean::inc(x_1098);
lean::dec(x_1076);
x_1099 = l___private_init_lean_expander_1__popStxArg(x_1096, x_4);
if (lean::obj_tag(x_1099) == 0)
{
obj* x_1100; obj* x_1101; obj* x_1102; 
lean::dec(x_1098);
lean::dec(x_1097);
lean::dec(x_1075);
lean::dec(x_1001);
lean::dec(x_1);
x_1100 = lean::cnstr_get(x_1099, 0);
lean::inc(x_1100);
if (lean::is_exclusive(x_1099)) {
 lean::cnstr_release(x_1099, 0);
 x_1101 = x_1099;
} else {
 lean::dec_ref(x_1099);
 x_1101 = lean::box(0);
}
if (lean::is_scalar(x_1101)) {
 x_1102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1102 = x_1101;
}
lean::cnstr_set(x_1102, 0, x_1100);
return x_1102;
}
else
{
obj* x_1103; obj* x_1104; obj* x_1105; 
x_1103 = lean::cnstr_get(x_1099, 0);
lean::inc(x_1103);
lean::dec(x_1099);
x_1104 = lean::cnstr_get(x_1103, 1);
lean::inc(x_1104);
x_1105 = lean::cnstr_get(x_1104, 3);
lean::inc(x_1105);
if (lean::obj_tag(x_1105) == 0)
{
obj* x_1106; obj* x_1107; obj* x_1108; 
lean::dec(x_1103);
lean::dec(x_1098);
lean::dec(x_1097);
lean::inc(x_1);
if (lean::is_scalar(x_1075)) {
 x_1106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1106 = x_1075;
}
lean::cnstr_set(x_1106, 0, x_1);
x_1107 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_1108 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_1106, x_1107, x_1104, x_4);
lean::dec(x_1104);
lean::dec(x_1106);
if (lean::obj_tag(x_1108) == 0)
{
obj* x_1109; obj* x_1110; obj* x_1111; 
lean::dec(x_1001);
lean::dec(x_1);
x_1109 = lean::cnstr_get(x_1108, 0);
lean::inc(x_1109);
if (lean::is_exclusive(x_1108)) {
 lean::cnstr_release(x_1108, 0);
 x_1110 = x_1108;
} else {
 lean::dec_ref(x_1108);
 x_1110 = lean::box(0);
}
if (lean::is_scalar(x_1110)) {
 x_1111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1111 = x_1110;
}
lean::cnstr_set(x_1111, 0, x_1109);
return x_1111;
}
else
{
obj* x_1112; obj* x_1113; 
x_1112 = lean::cnstr_get(x_1108, 0);
lean::inc(x_1112);
lean::dec(x_1108);
x_1113 = lean::cnstr_get(x_1112, 1);
lean::inc(x_1113);
lean::dec(x_1112);
x_2 = x_1001;
x_3 = x_1113;
goto _start;
}
}
else
{
obj* x_1115; obj* x_1116; obj* x_1117; obj* x_1118; obj* x_1119; obj* x_1120; obj* x_1121; obj* x_1122; obj* x_1123; obj* x_1124; obj* x_1125; obj* x_1126; obj* x_1127; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; obj* x_1132; obj* x_1133; obj* x_1134; obj* x_1135; obj* x_1136; obj* x_1137; obj* x_1138; obj* x_1139; obj* x_1140; obj* x_1141; obj* x_1142; obj* x_1143; obj* x_1144; 
lean::dec(x_1075);
x_1115 = lean::cnstr_get(x_1103, 0);
lean::inc(x_1115);
if (lean::is_exclusive(x_1103)) {
 lean::cnstr_release(x_1103, 0);
 lean::cnstr_release(x_1103, 1);
 x_1116 = x_1103;
} else {
 lean::dec_ref(x_1103);
 x_1116 = lean::box(0);
}
x_1117 = lean::cnstr_get(x_1104, 0);
lean::inc(x_1117);
x_1118 = lean::cnstr_get(x_1104, 1);
lean::inc(x_1118);
x_1119 = lean::cnstr_get(x_1104, 2);
lean::inc(x_1119);
if (lean::is_exclusive(x_1104)) {
 lean::cnstr_release(x_1104, 0);
 lean::cnstr_release(x_1104, 1);
 lean::cnstr_release(x_1104, 2);
 lean::cnstr_release(x_1104, 3);
 x_1120 = x_1104;
} else {
 lean::dec_ref(x_1104);
 x_1120 = lean::box(0);
}
x_1121 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1121);
x_1122 = l_Lean_Parser_Term_lambda_HasView;
x_1123 = lean::cnstr_get(x_1122, 1);
lean::inc(x_1123);
x_1124 = lean::box(0);
x_1125 = lean::cnstr_get(x_1098, 3);
lean::inc(x_1125);
x_1126 = lean::box(0);
x_1127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1127, 0, x_1125);
lean::cnstr_set(x_1127, 1, x_1126);
x_1128 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_1127);
x_1129 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1129, 0, x_1128);
lean::cnstr_set(x_1129, 1, x_1124);
x_1130 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1130, 0, x_1129);
x_1131 = lean::cnstr_get(x_1098, 5);
lean::inc(x_1131);
lean::dec(x_1098);
x_1132 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_1133 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_1134 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_1134, 0, x_1132);
lean::cnstr_set(x_1134, 1, x_1130);
lean::cnstr_set(x_1134, 2, x_1133);
lean::cnstr_set(x_1134, 3, x_1131);
lean::inc(x_1123);
x_1135 = lean::apply_1(x_1123, x_1134);
x_1136 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_1136, 0, x_1132);
lean::cnstr_set(x_1136, 1, x_1121);
lean::cnstr_set(x_1136, 2, x_1133);
lean::cnstr_set(x_1136, 3, x_1115);
x_1137 = lean::apply_1(x_1123, x_1136);
x_1138 = l_Lean_Parser_Term_app_HasView;
x_1139 = lean::cnstr_get(x_1138, 1);
lean::inc(x_1139);
x_1140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1140, 0, x_1135);
lean::cnstr_set(x_1140, 1, x_1137);
x_1141 = lean::apply_1(x_1139, x_1140);
if (lean::is_scalar(x_1116)) {
 x_1142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1142 = x_1116;
}
lean::cnstr_set(x_1142, 0, x_1097);
lean::cnstr_set(x_1142, 1, x_1141);
x_1143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1143, 0, x_1142);
lean::cnstr_set(x_1143, 1, x_1119);
if (lean::is_scalar(x_1120)) {
 x_1144 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1144 = x_1120;
}
lean::cnstr_set(x_1144, 0, x_1117);
lean::cnstr_set(x_1144, 1, x_1118);
lean::cnstr_set(x_1144, 2, x_1143);
lean::cnstr_set(x_1144, 3, x_1105);
x_2 = x_1001;
x_3 = x_1144;
goto _start;
}
}
}
default: 
{
obj* x_1146; obj* x_1147; obj* x_1148; obj* x_1149; 
lean::dec(x_1076);
lean::dec(x_1053);
x_1146 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1146);
lean::dec(x_1006);
lean::inc(x_1);
if (lean::is_scalar(x_1075)) {
 x_1147 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1147 = x_1075;
}
lean::cnstr_set(x_1147, 0, x_1);
x_1148 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_1149 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_1147, x_1148, x_1146, x_4);
lean::dec(x_1146);
lean::dec(x_1147);
if (lean::obj_tag(x_1149) == 0)
{
obj* x_1150; obj* x_1151; obj* x_1152; 
lean::dec(x_1001);
lean::dec(x_1);
x_1150 = lean::cnstr_get(x_1149, 0);
lean::inc(x_1150);
if (lean::is_exclusive(x_1149)) {
 lean::cnstr_release(x_1149, 0);
 x_1151 = x_1149;
} else {
 lean::dec_ref(x_1149);
 x_1151 = lean::box(0);
}
if (lean::is_scalar(x_1151)) {
 x_1152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1152 = x_1151;
}
lean::cnstr_set(x_1152, 0, x_1150);
return x_1152;
}
else
{
obj* x_1153; obj* x_1154; 
x_1153 = lean::cnstr_get(x_1149, 0);
lean::inc(x_1153);
lean::dec(x_1149);
x_1154 = lean::cnstr_get(x_1153, 1);
lean::inc(x_1154);
lean::dec(x_1153);
x_2 = x_1001;
x_3 = x_1154;
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
}
obj* l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(obj* x_1) {
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
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_5);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_8, 2);
lean::inc(x_9);
lean::dec(x_8);
lean::cnstr_set(x_4, 0, x_9);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_10, 2);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_13);
return x_1;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_16 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_15);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
} else {
 lean::dec_ref(x_14);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::dec(x_17);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_16);
return x_22;
}
}
}
}
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_Syntax_isOfKind___main(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_Lean_Parser_identUnivs_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
}
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean_name_dec_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
obj* x_10; 
lean::inc(x_7);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
}
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
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
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_2, 1);
x_13 = lean::cnstr_get(x_2, 0);
lean::dec(x_13);
lean::inc(x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_1);
x_15 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_16 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_3, x_4);
lean::dec(x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_1);
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::dec(x_8);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
lean::dec(x_20);
x_2 = x_12;
x_3 = x_22;
goto _start;
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_21);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::cnstr_get(x_21, 0);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_26; obj* x_27; 
lean::dec(x_25);
lean::dec(x_14);
x_26 = lean::cnstr_get(x_20, 1);
lean::inc(x_26);
lean::dec(x_20);
x_27 = l___private_init_lean_expander_1__popStxArg(x_26, x_4);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
lean::free_heap_obj(x_21);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
lean::dec(x_27);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
lean::dec(x_27);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = !lean::is_exclusive(x_32);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_32, 3);
lean::dec(x_35);
x_36 = l_Lean_Parser_Term_binderIdent_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::apply_1(x_37, x_33);
x_39 = lean::box(0);
lean::cnstr_set(x_2, 1, x_39);
lean::cnstr_set(x_2, 0, x_38);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_21, 0, x_42);
lean::cnstr_set(x_32, 3, x_21);
x_2 = x_12;
x_3 = x_32;
goto _start;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_44 = lean::cnstr_get(x_32, 0);
x_45 = lean::cnstr_get(x_32, 1);
x_46 = lean::cnstr_get(x_32, 2);
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_32);
x_47 = l_Lean_Parser_Term_binderIdent_HasView;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::apply_1(x_48, x_33);
x_50 = lean::box(0);
lean::cnstr_set(x_2, 1, x_50);
lean::cnstr_set(x_2, 0, x_49);
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_2);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_21, 0, x_53);
x_54 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_54, 0, x_44);
lean::cnstr_set(x_54, 1, x_45);
lean::cnstr_set(x_54, 2, x_46);
lean::cnstr_set(x_54, 3, x_21);
x_2 = x_12;
x_3 = x_54;
goto _start;
}
}
}
case 1:
{
obj* x_56; obj* x_57; 
lean::dec(x_25);
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_56 = lean::cnstr_get(x_20, 1);
lean::inc(x_56);
lean::dec(x_20);
x_57 = l___private_init_lean_expander_1__popStxArg(x_56, x_4);
if (lean::obj_tag(x_57) == 0)
{
uint8 x_58; 
lean::free_heap_obj(x_21);
lean::dec(x_12);
lean::dec(x_1);
x_58 = !lean::is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
obj* x_59; obj* x_60; 
x_59 = lean::cnstr_get(x_57, 0);
lean::inc(x_59);
lean::dec(x_57);
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; uint8 x_64; 
x_61 = lean::cnstr_get(x_57, 0);
lean::inc(x_61);
lean::dec(x_57);
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
lean::dec(x_61);
x_64 = !lean::is_exclusive(x_62);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_62, 3);
lean::dec(x_65);
x_66 = l_Lean_Parser_Term_binders_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::apply_1(x_67, x_63);
lean::cnstr_set(x_21, 0, x_68);
lean::cnstr_set(x_62, 3, x_21);
x_2 = x_12;
x_3 = x_62;
goto _start;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_70 = lean::cnstr_get(x_62, 0);
x_71 = lean::cnstr_get(x_62, 1);
x_72 = lean::cnstr_get(x_62, 2);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_62);
x_73 = l_Lean_Parser_Term_binders_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::apply_1(x_74, x_63);
lean::cnstr_set(x_21, 0, x_75);
x_76 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_76, 0, x_70);
lean::cnstr_set(x_76, 1, x_71);
lean::cnstr_set(x_76, 2, x_72);
lean::cnstr_set(x_76, 3, x_21);
x_2 = x_12;
x_3 = x_76;
goto _start;
}
}
}
default: 
{
obj* x_78; obj* x_79; 
lean::free_heap_obj(x_21);
x_78 = lean::cnstr_get(x_25, 0);
lean::inc(x_78);
lean::dec(x_25);
x_79 = lean::cnstr_get(x_78, 1);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_14);
x_80 = lean::cnstr_get(x_20, 1);
lean::inc(x_80);
lean::dec(x_20);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
x_82 = l___private_init_lean_expander_1__popStxArg(x_80, x_4);
if (lean::obj_tag(x_82) == 0)
{
uint8 x_83; 
lean::dec(x_81);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_83 = !lean::is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
}
else
{
obj* x_86; uint8 x_87; 
x_86 = lean::cnstr_get(x_82, 0);
lean::inc(x_86);
lean::dec(x_82);
x_87 = !lean::is_exclusive(x_86);
if (x_87 == 0)
{
obj* x_88; uint8 x_89; 
x_88 = lean::cnstr_get(x_86, 1);
x_89 = !lean::is_exclusive(x_88);
if (x_89 == 0)
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_86, 0);
x_91 = lean::cnstr_get(x_88, 2);
lean::cnstr_set(x_86, 1, x_90);
lean::cnstr_set(x_86, 0, x_81);
lean::cnstr_set(x_2, 1, x_91);
lean::cnstr_set(x_2, 0, x_86);
lean::cnstr_set(x_88, 2, x_2);
x_2 = x_12;
x_3 = x_88;
goto _start;
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_93 = lean::cnstr_get(x_86, 0);
x_94 = lean::cnstr_get(x_88, 0);
x_95 = lean::cnstr_get(x_88, 1);
x_96 = lean::cnstr_get(x_88, 2);
x_97 = lean::cnstr_get(x_88, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_88);
lean::cnstr_set(x_86, 1, x_93);
lean::cnstr_set(x_86, 0, x_81);
lean::cnstr_set(x_2, 1, x_96);
lean::cnstr_set(x_2, 0, x_86);
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set(x_98, 2, x_2);
lean::cnstr_set(x_98, 3, x_97);
x_2 = x_12;
x_3 = x_98;
goto _start;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_100 = lean::cnstr_get(x_86, 1);
x_101 = lean::cnstr_get(x_86, 0);
lean::inc(x_100);
lean::inc(x_101);
lean::dec(x_86);
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_100, 2);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_100, 3);
lean::inc(x_105);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 lean::cnstr_release(x_100, 2);
 lean::cnstr_release(x_100, 3);
 x_106 = x_100;
} else {
 lean::dec_ref(x_100);
 x_106 = lean::box(0);
}
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_81);
lean::cnstr_set(x_107, 1, x_101);
lean::cnstr_set(x_2, 1, x_104);
lean::cnstr_set(x_2, 0, x_107);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_102);
lean::cnstr_set(x_108, 1, x_103);
lean::cnstr_set(x_108, 2, x_2);
lean::cnstr_set(x_108, 3, x_105);
x_2 = x_12;
x_3 = x_108;
goto _start;
}
}
}
else
{
obj* x_110; obj* x_111; 
x_110 = lean::cnstr_get(x_79, 0);
lean::inc(x_110);
lean::dec(x_79);
x_111 = lean::cnstr_get(x_110, 1);
lean::inc(x_111);
lean::dec(x_110);
switch (lean::obj_tag(x_111)) {
case 0:
{
obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_111);
lean::dec(x_14);
x_112 = lean::cnstr_get(x_20, 1);
lean::inc(x_112);
lean::dec(x_20);
x_113 = lean::cnstr_get(x_78, 0);
lean::inc(x_113);
lean::dec(x_78);
x_114 = l___private_init_lean_expander_1__popStxArg(x_112, x_4);
if (lean::obj_tag(x_114) == 0)
{
uint8 x_115; 
lean::dec(x_113);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_115 = !lean::is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
lean::dec(x_114);
x_117 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
return x_117;
}
}
else
{
obj* x_118; uint8 x_119; 
x_118 = lean::cnstr_get(x_114, 0);
lean::inc(x_118);
lean::dec(x_114);
x_119 = !lean::is_exclusive(x_118);
if (x_119 == 0)
{
obj* x_120; uint8 x_121; 
x_120 = lean::cnstr_get(x_118, 1);
x_121 = !lean::is_exclusive(x_120);
if (x_121 == 0)
{
obj* x_122; obj* x_123; 
x_122 = lean::cnstr_get(x_118, 0);
x_123 = lean::cnstr_get(x_120, 2);
lean::cnstr_set(x_118, 1, x_122);
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_2, 1, x_123);
lean::cnstr_set(x_2, 0, x_118);
lean::cnstr_set(x_120, 2, x_2);
x_2 = x_12;
x_3 = x_120;
goto _start;
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_125 = lean::cnstr_get(x_118, 0);
x_126 = lean::cnstr_get(x_120, 0);
x_127 = lean::cnstr_get(x_120, 1);
x_128 = lean::cnstr_get(x_120, 2);
x_129 = lean::cnstr_get(x_120, 3);
lean::inc(x_129);
lean::inc(x_128);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_120);
lean::cnstr_set(x_118, 1, x_125);
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set(x_2, 1, x_128);
lean::cnstr_set(x_2, 0, x_118);
x_130 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set(x_130, 1, x_127);
lean::cnstr_set(x_130, 2, x_2);
lean::cnstr_set(x_130, 3, x_129);
x_2 = x_12;
x_3 = x_130;
goto _start;
}
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_132 = lean::cnstr_get(x_118, 1);
x_133 = lean::cnstr_get(x_118, 0);
lean::inc(x_132);
lean::inc(x_133);
lean::dec(x_118);
x_134 = lean::cnstr_get(x_132, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_132, 2);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_132, 3);
lean::inc(x_137);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 lean::cnstr_release(x_132, 2);
 lean::cnstr_release(x_132, 3);
 x_138 = x_132;
} else {
 lean::dec_ref(x_132);
 x_138 = lean::box(0);
}
x_139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_139, 0, x_113);
lean::cnstr_set(x_139, 1, x_133);
lean::cnstr_set(x_2, 1, x_136);
lean::cnstr_set(x_2, 0, x_139);
if (lean::is_scalar(x_138)) {
 x_140 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_140 = x_138;
}
lean::cnstr_set(x_140, 0, x_134);
lean::cnstr_set(x_140, 1, x_135);
lean::cnstr_set(x_140, 2, x_2);
lean::cnstr_set(x_140, 3, x_137);
x_2 = x_12;
x_3 = x_140;
goto _start;
}
}
}
case 2:
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_142 = lean::cnstr_get(x_20, 1);
lean::inc(x_142);
lean::dec(x_20);
x_143 = lean::cnstr_get(x_78, 0);
lean::inc(x_143);
lean::dec(x_78);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
lean::dec(x_111);
x_145 = l___private_init_lean_expander_1__popStxArg(x_142, x_4);
if (lean::obj_tag(x_145) == 0)
{
uint8 x_146; 
lean::dec(x_144);
lean::dec(x_143);
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_146 = !lean::is_exclusive(x_145);
if (x_146 == 0)
{
return x_145;
}
else
{
obj* x_147; obj* x_148; 
x_147 = lean::cnstr_get(x_145, 0);
lean::inc(x_147);
lean::dec(x_145);
x_148 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_148, 0, x_147);
return x_148;
}
}
else
{
obj* x_149; obj* x_150; obj* x_151; 
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
lean::dec(x_145);
x_150 = lean::cnstr_get(x_149, 1);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_150, 3);
lean::inc(x_151);
if (lean::obj_tag(x_151) == 0)
{
obj* x_152; 
lean::dec(x_149);
lean::dec(x_144);
lean::dec(x_143);
lean::free_heap_obj(x_2);
x_152 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_150, x_4);
lean::dec(x_150);
lean::dec(x_14);
if (lean::obj_tag(x_152) == 0)
{
uint8 x_153; 
lean::dec(x_12);
lean::dec(x_1);
x_153 = !lean::is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
obj* x_154; obj* x_155; 
x_154 = lean::cnstr_get(x_152, 0);
lean::inc(x_154);
lean::dec(x_152);
x_155 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
return x_155;
}
}
else
{
obj* x_156; obj* x_157; 
x_156 = lean::cnstr_get(x_152, 0);
lean::inc(x_156);
lean::dec(x_152);
x_157 = lean::cnstr_get(x_156, 1);
lean::inc(x_157);
lean::dec(x_156);
x_2 = x_12;
x_3 = x_157;
goto _start;
}
}
else
{
uint8 x_159; 
lean::dec(x_14);
x_159 = !lean::is_exclusive(x_149);
if (x_159 == 0)
{
obj* x_160; obj* x_161; uint8 x_162; 
x_160 = lean::cnstr_get(x_149, 0);
x_161 = lean::cnstr_get(x_149, 1);
lean::dec(x_161);
x_162 = !lean::is_exclusive(x_150);
if (x_162 == 0)
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_163 = lean::cnstr_get(x_150, 2);
x_164 = lean::cnstr_get(x_150, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_151, 0);
lean::inc(x_165);
x_166 = l_Lean_Parser_Term_lambda_HasView;
x_167 = lean::cnstr_get(x_166, 1);
lean::inc(x_167);
x_168 = lean::box(0);
x_169 = lean::cnstr_get(x_144, 3);
lean::inc(x_169);
x_170 = lean::box(0);
lean::cnstr_set(x_2, 1, x_170);
lean::cnstr_set(x_2, 0, x_169);
x_171 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_172 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_168);
x_173 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_173, 0, x_172);
x_174 = lean::cnstr_get(x_144, 5);
lean::inc(x_174);
lean::dec(x_144);
x_175 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_176 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_177 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_177, 0, x_175);
lean::cnstr_set(x_177, 1, x_173);
lean::cnstr_set(x_177, 2, x_176);
lean::cnstr_set(x_177, 3, x_174);
lean::inc(x_167);
x_178 = lean::apply_1(x_167, x_177);
x_179 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_179, 0, x_175);
lean::cnstr_set(x_179, 1, x_165);
lean::cnstr_set(x_179, 2, x_176);
lean::cnstr_set(x_179, 3, x_160);
x_180 = lean::apply_1(x_167, x_179);
x_181 = l_Lean_Parser_Term_app_HasView;
x_182 = lean::cnstr_get(x_181, 1);
lean::inc(x_182);
x_183 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_183, 0, x_178);
lean::cnstr_set(x_183, 1, x_180);
x_184 = lean::apply_1(x_182, x_183);
lean::cnstr_set(x_149, 1, x_184);
lean::cnstr_set(x_149, 0, x_143);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_149);
lean::cnstr_set(x_185, 1, x_163);
lean::cnstr_set(x_150, 2, x_185);
x_2 = x_12;
x_3 = x_150;
goto _start;
}
else
{
obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_187 = lean::cnstr_get(x_150, 0);
x_188 = lean::cnstr_get(x_150, 1);
x_189 = lean::cnstr_get(x_150, 2);
lean::inc(x_189);
lean::inc(x_188);
lean::inc(x_187);
lean::dec(x_150);
x_190 = lean::cnstr_get(x_151, 0);
lean::inc(x_190);
x_191 = l_Lean_Parser_Term_lambda_HasView;
x_192 = lean::cnstr_get(x_191, 1);
lean::inc(x_192);
x_193 = lean::box(0);
x_194 = lean::cnstr_get(x_144, 3);
lean::inc(x_194);
x_195 = lean::box(0);
lean::cnstr_set(x_2, 1, x_195);
lean::cnstr_set(x_2, 0, x_194);
x_196 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_197 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_193);
x_198 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_198, 0, x_197);
x_199 = lean::cnstr_get(x_144, 5);
lean::inc(x_199);
lean::dec(x_144);
x_200 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_201 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_202 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_198);
lean::cnstr_set(x_202, 2, x_201);
lean::cnstr_set(x_202, 3, x_199);
lean::inc(x_192);
x_203 = lean::apply_1(x_192, x_202);
x_204 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_204, 0, x_200);
lean::cnstr_set(x_204, 1, x_190);
lean::cnstr_set(x_204, 2, x_201);
lean::cnstr_set(x_204, 3, x_160);
x_205 = lean::apply_1(x_192, x_204);
x_206 = l_Lean_Parser_Term_app_HasView;
x_207 = lean::cnstr_get(x_206, 1);
lean::inc(x_207);
x_208 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_208, 0, x_203);
lean::cnstr_set(x_208, 1, x_205);
x_209 = lean::apply_1(x_207, x_208);
lean::cnstr_set(x_149, 1, x_209);
lean::cnstr_set(x_149, 0, x_143);
x_210 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_210, 0, x_149);
lean::cnstr_set(x_210, 1, x_189);
x_211 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_211, 0, x_187);
lean::cnstr_set(x_211, 1, x_188);
lean::cnstr_set(x_211, 2, x_210);
lean::cnstr_set(x_211, 3, x_151);
x_2 = x_12;
x_3 = x_211;
goto _start;
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
x_213 = lean::cnstr_get(x_149, 0);
lean::inc(x_213);
lean::dec(x_149);
x_214 = lean::cnstr_get(x_150, 0);
lean::inc(x_214);
x_215 = lean::cnstr_get(x_150, 1);
lean::inc(x_215);
x_216 = lean::cnstr_get(x_150, 2);
lean::inc(x_216);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_release(x_150, 0);
 lean::cnstr_release(x_150, 1);
 lean::cnstr_release(x_150, 2);
 lean::cnstr_release(x_150, 3);
 x_217 = x_150;
} else {
 lean::dec_ref(x_150);
 x_217 = lean::box(0);
}
x_218 = lean::cnstr_get(x_151, 0);
lean::inc(x_218);
x_219 = l_Lean_Parser_Term_lambda_HasView;
x_220 = lean::cnstr_get(x_219, 1);
lean::inc(x_220);
x_221 = lean::box(0);
x_222 = lean::cnstr_get(x_144, 3);
lean::inc(x_222);
x_223 = lean::box(0);
lean::cnstr_set(x_2, 1, x_223);
lean::cnstr_set(x_2, 0, x_222);
x_224 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_225 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_225, 0, x_224);
lean::cnstr_set(x_225, 1, x_221);
x_226 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_226, 0, x_225);
x_227 = lean::cnstr_get(x_144, 5);
lean::inc(x_227);
lean::dec(x_144);
x_228 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_229 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_230 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_230, 0, x_228);
lean::cnstr_set(x_230, 1, x_226);
lean::cnstr_set(x_230, 2, x_229);
lean::cnstr_set(x_230, 3, x_227);
lean::inc(x_220);
x_231 = lean::apply_1(x_220, x_230);
x_232 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_232, 0, x_228);
lean::cnstr_set(x_232, 1, x_218);
lean::cnstr_set(x_232, 2, x_229);
lean::cnstr_set(x_232, 3, x_213);
x_233 = lean::apply_1(x_220, x_232);
x_234 = l_Lean_Parser_Term_app_HasView;
x_235 = lean::cnstr_get(x_234, 1);
lean::inc(x_235);
x_236 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_236, 0, x_231);
lean::cnstr_set(x_236, 1, x_233);
x_237 = lean::apply_1(x_235, x_236);
x_238 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_238, 0, x_143);
lean::cnstr_set(x_238, 1, x_237);
x_239 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_216);
if (lean::is_scalar(x_217)) {
 x_240 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_240 = x_217;
}
lean::cnstr_set(x_240, 0, x_214);
lean::cnstr_set(x_240, 1, x_215);
lean::cnstr_set(x_240, 2, x_239);
lean::cnstr_set(x_240, 3, x_151);
x_2 = x_12;
x_3 = x_240;
goto _start;
}
}
}
}
default: 
{
obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_111);
lean::dec(x_78);
lean::free_heap_obj(x_2);
x_242 = lean::cnstr_get(x_20, 1);
lean::inc(x_242);
lean::dec(x_20);
x_243 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_244 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_243, x_242, x_4);
lean::dec(x_242);
lean::dec(x_14);
if (lean::obj_tag(x_244) == 0)
{
uint8 x_245; 
lean::dec(x_12);
lean::dec(x_1);
x_245 = !lean::is_exclusive(x_244);
if (x_245 == 0)
{
return x_244;
}
else
{
obj* x_246; obj* x_247; 
x_246 = lean::cnstr_get(x_244, 0);
lean::inc(x_246);
lean::dec(x_244);
x_247 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_247, 0, x_246);
return x_247;
}
}
else
{
obj* x_248; obj* x_249; 
x_248 = lean::cnstr_get(x_244, 0);
lean::inc(x_248);
lean::dec(x_244);
x_249 = lean::cnstr_get(x_248, 1);
lean::inc(x_249);
lean::dec(x_248);
x_2 = x_12;
x_3 = x_249;
goto _start;
}
}
}
}
}
}
}
else
{
obj* x_251; 
x_251 = lean::cnstr_get(x_21, 0);
lean::inc(x_251);
lean::dec(x_21);
switch (lean::obj_tag(x_251)) {
case 0:
{
obj* x_252; obj* x_253; 
lean::dec(x_251);
lean::dec(x_14);
x_252 = lean::cnstr_get(x_20, 1);
lean::inc(x_252);
lean::dec(x_20);
x_253 = l___private_init_lean_expander_1__popStxArg(x_252, x_4);
if (lean::obj_tag(x_253) == 0)
{
obj* x_254; obj* x_255; obj* x_256; 
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
if (lean::is_exclusive(x_253)) {
 lean::cnstr_release(x_253, 0);
 x_255 = x_253;
} else {
 lean::dec_ref(x_253);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_254);
return x_256;
}
else
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_257 = lean::cnstr_get(x_253, 0);
lean::inc(x_257);
lean::dec(x_253);
x_258 = lean::cnstr_get(x_257, 1);
lean::inc(x_258);
x_259 = lean::cnstr_get(x_257, 0);
lean::inc(x_259);
lean::dec(x_257);
x_260 = lean::cnstr_get(x_258, 0);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
x_262 = lean::cnstr_get(x_258, 2);
lean::inc(x_262);
if (lean::is_exclusive(x_258)) {
 lean::cnstr_release(x_258, 0);
 lean::cnstr_release(x_258, 1);
 lean::cnstr_release(x_258, 2);
 lean::cnstr_release(x_258, 3);
 x_263 = x_258;
} else {
 lean::dec_ref(x_258);
 x_263 = lean::box(0);
}
x_264 = l_Lean_Parser_Term_binderIdent_HasView;
x_265 = lean::cnstr_get(x_264, 0);
lean::inc(x_265);
x_266 = lean::apply_1(x_265, x_259);
x_267 = lean::box(0);
lean::cnstr_set(x_2, 1, x_267);
lean::cnstr_set(x_2, 0, x_266);
x_268 = lean::box(0);
x_269 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_269, 0, x_2);
lean::cnstr_set(x_269, 1, x_268);
x_270 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_270, 0, x_269);
x_271 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_271, 0, x_270);
if (lean::is_scalar(x_263)) {
 x_272 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_272 = x_263;
}
lean::cnstr_set(x_272, 0, x_260);
lean::cnstr_set(x_272, 1, x_261);
lean::cnstr_set(x_272, 2, x_262);
lean::cnstr_set(x_272, 3, x_271);
x_2 = x_12;
x_3 = x_272;
goto _start;
}
}
case 1:
{
obj* x_274; obj* x_275; 
lean::dec(x_251);
lean::dec(x_14);
lean::free_heap_obj(x_2);
x_274 = lean::cnstr_get(x_20, 1);
lean::inc(x_274);
lean::dec(x_20);
x_275 = l___private_init_lean_expander_1__popStxArg(x_274, x_4);
if (lean::obj_tag(x_275) == 0)
{
obj* x_276; obj* x_277; obj* x_278; 
lean::dec(x_12);
lean::dec(x_1);
x_276 = lean::cnstr_get(x_275, 0);
lean::inc(x_276);
if (lean::is_exclusive(x_275)) {
 lean::cnstr_release(x_275, 0);
 x_277 = x_275;
} else {
 lean::dec_ref(x_275);
 x_277 = lean::box(0);
}
if (lean::is_scalar(x_277)) {
 x_278 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_278 = x_277;
}
lean::cnstr_set(x_278, 0, x_276);
return x_278;
}
else
{
obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
x_279 = lean::cnstr_get(x_275, 0);
lean::inc(x_279);
lean::dec(x_275);
x_280 = lean::cnstr_get(x_279, 1);
lean::inc(x_280);
x_281 = lean::cnstr_get(x_279, 0);
lean::inc(x_281);
lean::dec(x_279);
x_282 = lean::cnstr_get(x_280, 0);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
x_284 = lean::cnstr_get(x_280, 2);
lean::inc(x_284);
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 lean::cnstr_release(x_280, 1);
 lean::cnstr_release(x_280, 2);
 lean::cnstr_release(x_280, 3);
 x_285 = x_280;
} else {
 lean::dec_ref(x_280);
 x_285 = lean::box(0);
}
x_286 = l_Lean_Parser_Term_binders_HasView;
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_288 = lean::apply_1(x_287, x_281);
x_289 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_289, 0, x_288);
if (lean::is_scalar(x_285)) {
 x_290 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_290 = x_285;
}
lean::cnstr_set(x_290, 0, x_282);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_289);
x_2 = x_12;
x_3 = x_290;
goto _start;
}
}
default: 
{
obj* x_292; obj* x_293; 
x_292 = lean::cnstr_get(x_251, 0);
lean::inc(x_292);
lean::dec(x_251);
x_293 = lean::cnstr_get(x_292, 1);
lean::inc(x_293);
if (lean::obj_tag(x_293) == 0)
{
obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_14);
x_294 = lean::cnstr_get(x_20, 1);
lean::inc(x_294);
lean::dec(x_20);
x_295 = lean::cnstr_get(x_292, 0);
lean::inc(x_295);
lean::dec(x_292);
x_296 = l___private_init_lean_expander_1__popStxArg(x_294, x_4);
if (lean::obj_tag(x_296) == 0)
{
obj* x_297; obj* x_298; obj* x_299; 
lean::dec(x_295);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_297 = lean::cnstr_get(x_296, 0);
lean::inc(x_297);
if (lean::is_exclusive(x_296)) {
 lean::cnstr_release(x_296, 0);
 x_298 = x_296;
} else {
 lean::dec_ref(x_296);
 x_298 = lean::box(0);
}
if (lean::is_scalar(x_298)) {
 x_299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_299 = x_298;
}
lean::cnstr_set(x_299, 0, x_297);
return x_299;
}
else
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; 
x_300 = lean::cnstr_get(x_296, 0);
lean::inc(x_300);
lean::dec(x_296);
x_301 = lean::cnstr_get(x_300, 1);
lean::inc(x_301);
x_302 = lean::cnstr_get(x_300, 0);
lean::inc(x_302);
if (lean::is_exclusive(x_300)) {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_303 = x_300;
} else {
 lean::dec_ref(x_300);
 x_303 = lean::box(0);
}
x_304 = lean::cnstr_get(x_301, 0);
lean::inc(x_304);
x_305 = lean::cnstr_get(x_301, 1);
lean::inc(x_305);
x_306 = lean::cnstr_get(x_301, 2);
lean::inc(x_306);
x_307 = lean::cnstr_get(x_301, 3);
lean::inc(x_307);
if (lean::is_exclusive(x_301)) {
 lean::cnstr_release(x_301, 0);
 lean::cnstr_release(x_301, 1);
 lean::cnstr_release(x_301, 2);
 lean::cnstr_release(x_301, 3);
 x_308 = x_301;
} else {
 lean::dec_ref(x_301);
 x_308 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_309 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_309 = x_303;
}
lean::cnstr_set(x_309, 0, x_295);
lean::cnstr_set(x_309, 1, x_302);
lean::cnstr_set(x_2, 1, x_306);
lean::cnstr_set(x_2, 0, x_309);
if (lean::is_scalar(x_308)) {
 x_310 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_310 = x_308;
}
lean::cnstr_set(x_310, 0, x_304);
lean::cnstr_set(x_310, 1, x_305);
lean::cnstr_set(x_310, 2, x_2);
lean::cnstr_set(x_310, 3, x_307);
x_2 = x_12;
x_3 = x_310;
goto _start;
}
}
else
{
obj* x_312; obj* x_313; 
x_312 = lean::cnstr_get(x_293, 0);
lean::inc(x_312);
lean::dec(x_293);
x_313 = lean::cnstr_get(x_312, 1);
lean::inc(x_313);
lean::dec(x_312);
switch (lean::obj_tag(x_313)) {
case 0:
{
obj* x_314; obj* x_315; obj* x_316; 
lean::dec(x_313);
lean::dec(x_14);
x_314 = lean::cnstr_get(x_20, 1);
lean::inc(x_314);
lean::dec(x_20);
x_315 = lean::cnstr_get(x_292, 0);
lean::inc(x_315);
lean::dec(x_292);
x_316 = l___private_init_lean_expander_1__popStxArg(x_314, x_4);
if (lean::obj_tag(x_316) == 0)
{
obj* x_317; obj* x_318; obj* x_319; 
lean::dec(x_315);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
if (lean::is_exclusive(x_316)) {
 lean::cnstr_release(x_316, 0);
 x_318 = x_316;
} else {
 lean::dec_ref(x_316);
 x_318 = lean::box(0);
}
if (lean::is_scalar(x_318)) {
 x_319 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_319 = x_318;
}
lean::cnstr_set(x_319, 0, x_317);
return x_319;
}
else
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
x_320 = lean::cnstr_get(x_316, 0);
lean::inc(x_320);
lean::dec(x_316);
x_321 = lean::cnstr_get(x_320, 1);
lean::inc(x_321);
x_322 = lean::cnstr_get(x_320, 0);
lean::inc(x_322);
if (lean::is_exclusive(x_320)) {
 lean::cnstr_release(x_320, 0);
 lean::cnstr_release(x_320, 1);
 x_323 = x_320;
} else {
 lean::dec_ref(x_320);
 x_323 = lean::box(0);
}
x_324 = lean::cnstr_get(x_321, 0);
lean::inc(x_324);
x_325 = lean::cnstr_get(x_321, 1);
lean::inc(x_325);
x_326 = lean::cnstr_get(x_321, 2);
lean::inc(x_326);
x_327 = lean::cnstr_get(x_321, 3);
lean::inc(x_327);
if (lean::is_exclusive(x_321)) {
 lean::cnstr_release(x_321, 0);
 lean::cnstr_release(x_321, 1);
 lean::cnstr_release(x_321, 2);
 lean::cnstr_release(x_321, 3);
 x_328 = x_321;
} else {
 lean::dec_ref(x_321);
 x_328 = lean::box(0);
}
if (lean::is_scalar(x_323)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_323;
}
lean::cnstr_set(x_329, 0, x_315);
lean::cnstr_set(x_329, 1, x_322);
lean::cnstr_set(x_2, 1, x_326);
lean::cnstr_set(x_2, 0, x_329);
if (lean::is_scalar(x_328)) {
 x_330 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_330 = x_328;
}
lean::cnstr_set(x_330, 0, x_324);
lean::cnstr_set(x_330, 1, x_325);
lean::cnstr_set(x_330, 2, x_2);
lean::cnstr_set(x_330, 3, x_327);
x_2 = x_12;
x_3 = x_330;
goto _start;
}
}
case 2:
{
obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_332 = lean::cnstr_get(x_20, 1);
lean::inc(x_332);
lean::dec(x_20);
x_333 = lean::cnstr_get(x_292, 0);
lean::inc(x_333);
lean::dec(x_292);
x_334 = lean::cnstr_get(x_313, 0);
lean::inc(x_334);
lean::dec(x_313);
x_335 = l___private_init_lean_expander_1__popStxArg(x_332, x_4);
if (lean::obj_tag(x_335) == 0)
{
obj* x_336; obj* x_337; obj* x_338; 
lean::dec(x_334);
lean::dec(x_333);
lean::dec(x_14);
lean::free_heap_obj(x_2);
lean::dec(x_12);
lean::dec(x_1);
x_336 = lean::cnstr_get(x_335, 0);
lean::inc(x_336);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 x_337 = x_335;
} else {
 lean::dec_ref(x_335);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_336);
return x_338;
}
else
{
obj* x_339; obj* x_340; obj* x_341; 
x_339 = lean::cnstr_get(x_335, 0);
lean::inc(x_339);
lean::dec(x_335);
x_340 = lean::cnstr_get(x_339, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_340, 3);
lean::inc(x_341);
if (lean::obj_tag(x_341) == 0)
{
obj* x_342; 
lean::dec(x_339);
lean::dec(x_334);
lean::dec(x_333);
lean::free_heap_obj(x_2);
x_342 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_15, x_340, x_4);
lean::dec(x_340);
lean::dec(x_14);
if (lean::obj_tag(x_342) == 0)
{
obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_12);
lean::dec(x_1);
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
if (lean::is_exclusive(x_342)) {
 lean::cnstr_release(x_342, 0);
 x_344 = x_342;
} else {
 lean::dec_ref(x_342);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_343);
return x_345;
}
else
{
obj* x_346; obj* x_347; 
x_346 = lean::cnstr_get(x_342, 0);
lean::inc(x_346);
lean::dec(x_342);
x_347 = lean::cnstr_get(x_346, 1);
lean::inc(x_347);
lean::dec(x_346);
x_2 = x_12;
x_3 = x_347;
goto _start;
}
}
else
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
lean::dec(x_14);
x_349 = lean::cnstr_get(x_339, 0);
lean::inc(x_349);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 x_350 = x_339;
} else {
 lean::dec_ref(x_339);
 x_350 = lean::box(0);
}
x_351 = lean::cnstr_get(x_340, 0);
lean::inc(x_351);
x_352 = lean::cnstr_get(x_340, 1);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 2);
lean::inc(x_353);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_354 = x_340;
} else {
 lean::dec_ref(x_340);
 x_354 = lean::box(0);
}
x_355 = lean::cnstr_get(x_341, 0);
lean::inc(x_355);
x_356 = l_Lean_Parser_Term_lambda_HasView;
x_357 = lean::cnstr_get(x_356, 1);
lean::inc(x_357);
x_358 = lean::box(0);
x_359 = lean::cnstr_get(x_334, 3);
lean::inc(x_359);
x_360 = lean::box(0);
lean::cnstr_set(x_2, 1, x_360);
lean::cnstr_set(x_2, 0, x_359);
x_361 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_362 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_358);
x_363 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_363, 0, x_362);
x_364 = lean::cnstr_get(x_334, 5);
lean::inc(x_364);
lean::dec(x_334);
x_365 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_366 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_367 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_363);
lean::cnstr_set(x_367, 2, x_366);
lean::cnstr_set(x_367, 3, x_364);
lean::inc(x_357);
x_368 = lean::apply_1(x_357, x_367);
x_369 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_369, 0, x_365);
lean::cnstr_set(x_369, 1, x_355);
lean::cnstr_set(x_369, 2, x_366);
lean::cnstr_set(x_369, 3, x_349);
x_370 = lean::apply_1(x_357, x_369);
x_371 = l_Lean_Parser_Term_app_HasView;
x_372 = lean::cnstr_get(x_371, 1);
lean::inc(x_372);
x_373 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_373, 0, x_368);
lean::cnstr_set(x_373, 1, x_370);
x_374 = lean::apply_1(x_372, x_373);
if (lean::is_scalar(x_350)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_350;
}
lean::cnstr_set(x_375, 0, x_333);
lean::cnstr_set(x_375, 1, x_374);
x_376 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_376, 0, x_375);
lean::cnstr_set(x_376, 1, x_353);
if (lean::is_scalar(x_354)) {
 x_377 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_377 = x_354;
}
lean::cnstr_set(x_377, 0, x_351);
lean::cnstr_set(x_377, 1, x_352);
lean::cnstr_set(x_377, 2, x_376);
lean::cnstr_set(x_377, 3, x_341);
x_2 = x_12;
x_3 = x_377;
goto _start;
}
}
}
default: 
{
obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_313);
lean::dec(x_292);
lean::free_heap_obj(x_2);
x_379 = lean::cnstr_get(x_20, 1);
lean::inc(x_379);
lean::dec(x_20);
x_380 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_381 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_14, x_380, x_379, x_4);
lean::dec(x_379);
lean::dec(x_14);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; 
lean::dec(x_12);
lean::dec(x_1);
x_382 = lean::cnstr_get(x_381, 0);
lean::inc(x_382);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 x_383 = x_381;
} else {
 lean::dec_ref(x_381);
 x_383 = lean::box(0);
}
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_382);
return x_384;
}
else
{
obj* x_385; obj* x_386; 
x_385 = lean::cnstr_get(x_381, 0);
lean::inc(x_385);
lean::dec(x_381);
x_386 = lean::cnstr_get(x_385, 1);
lean::inc(x_386);
lean::dec(x_385);
x_2 = x_12;
x_3 = x_386;
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
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; 
x_388 = lean::cnstr_get(x_2, 1);
lean::inc(x_388);
lean::dec(x_2);
lean::inc(x_1);
x_389 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_389, 0, x_1);
x_390 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_391 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_390, x_3, x_4);
lean::dec(x_3);
if (lean::obj_tag(x_391) == 0)
{
obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_389);
lean::dec(x_388);
lean::dec(x_8);
lean::dec(x_1);
x_392 = lean::cnstr_get(x_391, 0);
lean::inc(x_392);
if (lean::is_exclusive(x_391)) {
 lean::cnstr_release(x_391, 0);
 x_393 = x_391;
} else {
 lean::dec_ref(x_391);
 x_393 = lean::box(0);
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_392);
return x_394;
}
else
{
obj* x_395; obj* x_396; 
x_395 = lean::cnstr_get(x_391, 0);
lean::inc(x_395);
lean::dec(x_391);
x_396 = lean::cnstr_get(x_8, 1);
lean::inc(x_396);
lean::dec(x_8);
if (lean::obj_tag(x_396) == 0)
{
obj* x_397; 
lean::dec(x_389);
x_397 = lean::cnstr_get(x_395, 1);
lean::inc(x_397);
lean::dec(x_395);
x_2 = x_388;
x_3 = x_397;
goto _start;
}
else
{
obj* x_399; obj* x_400; 
x_399 = lean::cnstr_get(x_396, 0);
lean::inc(x_399);
if (lean::is_exclusive(x_396)) {
 lean::cnstr_release(x_396, 0);
 x_400 = x_396;
} else {
 lean::dec_ref(x_396);
 x_400 = lean::box(0);
}
switch (lean::obj_tag(x_399)) {
case 0:
{
obj* x_401; obj* x_402; 
lean::dec(x_399);
lean::dec(x_389);
x_401 = lean::cnstr_get(x_395, 1);
lean::inc(x_401);
lean::dec(x_395);
x_402 = l___private_init_lean_expander_1__popStxArg(x_401, x_4);
if (lean::obj_tag(x_402) == 0)
{
obj* x_403; obj* x_404; obj* x_405; 
lean::dec(x_400);
lean::dec(x_388);
lean::dec(x_1);
x_403 = lean::cnstr_get(x_402, 0);
lean::inc(x_403);
if (lean::is_exclusive(x_402)) {
 lean::cnstr_release(x_402, 0);
 x_404 = x_402;
} else {
 lean::dec_ref(x_402);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_403);
return x_405;
}
else
{
obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
x_406 = lean::cnstr_get(x_402, 0);
lean::inc(x_406);
lean::dec(x_402);
x_407 = lean::cnstr_get(x_406, 1);
lean::inc(x_407);
x_408 = lean::cnstr_get(x_406, 0);
lean::inc(x_408);
lean::dec(x_406);
x_409 = lean::cnstr_get(x_407, 0);
lean::inc(x_409);
x_410 = lean::cnstr_get(x_407, 1);
lean::inc(x_410);
x_411 = lean::cnstr_get(x_407, 2);
lean::inc(x_411);
if (lean::is_exclusive(x_407)) {
 lean::cnstr_release(x_407, 0);
 lean::cnstr_release(x_407, 1);
 lean::cnstr_release(x_407, 2);
 lean::cnstr_release(x_407, 3);
 x_412 = x_407;
} else {
 lean::dec_ref(x_407);
 x_412 = lean::box(0);
}
x_413 = l_Lean_Parser_Term_binderIdent_HasView;
x_414 = lean::cnstr_get(x_413, 0);
lean::inc(x_414);
x_415 = lean::apply_1(x_414, x_408);
x_416 = lean::box(0);
x_417 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_417, 0, x_415);
lean::cnstr_set(x_417, 1, x_416);
x_418 = lean::box(0);
x_419 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_419, 0, x_417);
lean::cnstr_set(x_419, 1, x_418);
x_420 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_420, 0, x_419);
if (lean::is_scalar(x_400)) {
 x_421 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_421 = x_400;
}
lean::cnstr_set(x_421, 0, x_420);
if (lean::is_scalar(x_412)) {
 x_422 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_422 = x_412;
}
lean::cnstr_set(x_422, 0, x_409);
lean::cnstr_set(x_422, 1, x_410);
lean::cnstr_set(x_422, 2, x_411);
lean::cnstr_set(x_422, 3, x_421);
x_2 = x_388;
x_3 = x_422;
goto _start;
}
}
case 1:
{
obj* x_424; obj* x_425; 
lean::dec(x_399);
lean::dec(x_389);
x_424 = lean::cnstr_get(x_395, 1);
lean::inc(x_424);
lean::dec(x_395);
x_425 = l___private_init_lean_expander_1__popStxArg(x_424, x_4);
if (lean::obj_tag(x_425) == 0)
{
obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_400);
lean::dec(x_388);
lean::dec(x_1);
x_426 = lean::cnstr_get(x_425, 0);
lean::inc(x_426);
if (lean::is_exclusive(x_425)) {
 lean::cnstr_release(x_425, 0);
 x_427 = x_425;
} else {
 lean::dec_ref(x_425);
 x_427 = lean::box(0);
}
if (lean::is_scalar(x_427)) {
 x_428 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_428 = x_427;
}
lean::cnstr_set(x_428, 0, x_426);
return x_428;
}
else
{
obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; 
x_429 = lean::cnstr_get(x_425, 0);
lean::inc(x_429);
lean::dec(x_425);
x_430 = lean::cnstr_get(x_429, 1);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_429, 0);
lean::inc(x_431);
lean::dec(x_429);
x_432 = lean::cnstr_get(x_430, 0);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_430, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_430, 2);
lean::inc(x_434);
if (lean::is_exclusive(x_430)) {
 lean::cnstr_release(x_430, 0);
 lean::cnstr_release(x_430, 1);
 lean::cnstr_release(x_430, 2);
 lean::cnstr_release(x_430, 3);
 x_435 = x_430;
} else {
 lean::dec_ref(x_430);
 x_435 = lean::box(0);
}
x_436 = l_Lean_Parser_Term_binders_HasView;
x_437 = lean::cnstr_get(x_436, 0);
lean::inc(x_437);
x_438 = lean::apply_1(x_437, x_431);
if (lean::is_scalar(x_400)) {
 x_439 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_439 = x_400;
}
lean::cnstr_set(x_439, 0, x_438);
if (lean::is_scalar(x_435)) {
 x_440 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_440 = x_435;
}
lean::cnstr_set(x_440, 0, x_432);
lean::cnstr_set(x_440, 1, x_433);
lean::cnstr_set(x_440, 2, x_434);
lean::cnstr_set(x_440, 3, x_439);
x_2 = x_388;
x_3 = x_440;
goto _start;
}
}
default: 
{
obj* x_442; obj* x_443; 
lean::dec(x_400);
x_442 = lean::cnstr_get(x_399, 0);
lean::inc(x_442);
lean::dec(x_399);
x_443 = lean::cnstr_get(x_442, 1);
lean::inc(x_443);
if (lean::obj_tag(x_443) == 0)
{
obj* x_444; obj* x_445; obj* x_446; 
lean::dec(x_389);
x_444 = lean::cnstr_get(x_395, 1);
lean::inc(x_444);
lean::dec(x_395);
x_445 = lean::cnstr_get(x_442, 0);
lean::inc(x_445);
lean::dec(x_442);
x_446 = l___private_init_lean_expander_1__popStxArg(x_444, x_4);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; 
lean::dec(x_445);
lean::dec(x_388);
lean::dec(x_1);
x_447 = lean::cnstr_get(x_446, 0);
lean::inc(x_447);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 x_448 = x_446;
} else {
 lean::dec_ref(x_446);
 x_448 = lean::box(0);
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_447);
return x_449;
}
else
{
obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; 
x_450 = lean::cnstr_get(x_446, 0);
lean::inc(x_450);
lean::dec(x_446);
x_451 = lean::cnstr_get(x_450, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_450, 0);
lean::inc(x_452);
if (lean::is_exclusive(x_450)) {
 lean::cnstr_release(x_450, 0);
 lean::cnstr_release(x_450, 1);
 x_453 = x_450;
} else {
 lean::dec_ref(x_450);
 x_453 = lean::box(0);
}
x_454 = lean::cnstr_get(x_451, 0);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_451, 1);
lean::inc(x_455);
x_456 = lean::cnstr_get(x_451, 2);
lean::inc(x_456);
x_457 = lean::cnstr_get(x_451, 3);
lean::inc(x_457);
if (lean::is_exclusive(x_451)) {
 lean::cnstr_release(x_451, 0);
 lean::cnstr_release(x_451, 1);
 lean::cnstr_release(x_451, 2);
 lean::cnstr_release(x_451, 3);
 x_458 = x_451;
} else {
 lean::dec_ref(x_451);
 x_458 = lean::box(0);
}
if (lean::is_scalar(x_453)) {
 x_459 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_459 = x_453;
}
lean::cnstr_set(x_459, 0, x_445);
lean::cnstr_set(x_459, 1, x_452);
x_460 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_460, 0, x_459);
lean::cnstr_set(x_460, 1, x_456);
if (lean::is_scalar(x_458)) {
 x_461 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_461 = x_458;
}
lean::cnstr_set(x_461, 0, x_454);
lean::cnstr_set(x_461, 1, x_455);
lean::cnstr_set(x_461, 2, x_460);
lean::cnstr_set(x_461, 3, x_457);
x_2 = x_388;
x_3 = x_461;
goto _start;
}
}
else
{
obj* x_463; obj* x_464; 
x_463 = lean::cnstr_get(x_443, 0);
lean::inc(x_463);
lean::dec(x_443);
x_464 = lean::cnstr_get(x_463, 1);
lean::inc(x_464);
lean::dec(x_463);
switch (lean::obj_tag(x_464)) {
case 0:
{
obj* x_465; obj* x_466; obj* x_467; 
lean::dec(x_464);
lean::dec(x_389);
x_465 = lean::cnstr_get(x_395, 1);
lean::inc(x_465);
lean::dec(x_395);
x_466 = lean::cnstr_get(x_442, 0);
lean::inc(x_466);
lean::dec(x_442);
x_467 = l___private_init_lean_expander_1__popStxArg(x_465, x_4);
if (lean::obj_tag(x_467) == 0)
{
obj* x_468; obj* x_469; obj* x_470; 
lean::dec(x_466);
lean::dec(x_388);
lean::dec(x_1);
x_468 = lean::cnstr_get(x_467, 0);
lean::inc(x_468);
if (lean::is_exclusive(x_467)) {
 lean::cnstr_release(x_467, 0);
 x_469 = x_467;
} else {
 lean::dec_ref(x_467);
 x_469 = lean::box(0);
}
if (lean::is_scalar(x_469)) {
 x_470 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_470 = x_469;
}
lean::cnstr_set(x_470, 0, x_468);
return x_470;
}
else
{
obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; 
x_471 = lean::cnstr_get(x_467, 0);
lean::inc(x_471);
lean::dec(x_467);
x_472 = lean::cnstr_get(x_471, 1);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_471, 0);
lean::inc(x_473);
if (lean::is_exclusive(x_471)) {
 lean::cnstr_release(x_471, 0);
 lean::cnstr_release(x_471, 1);
 x_474 = x_471;
} else {
 lean::dec_ref(x_471);
 x_474 = lean::box(0);
}
x_475 = lean::cnstr_get(x_472, 0);
lean::inc(x_475);
x_476 = lean::cnstr_get(x_472, 1);
lean::inc(x_476);
x_477 = lean::cnstr_get(x_472, 2);
lean::inc(x_477);
x_478 = lean::cnstr_get(x_472, 3);
lean::inc(x_478);
if (lean::is_exclusive(x_472)) {
 lean::cnstr_release(x_472, 0);
 lean::cnstr_release(x_472, 1);
 lean::cnstr_release(x_472, 2);
 lean::cnstr_release(x_472, 3);
 x_479 = x_472;
} else {
 lean::dec_ref(x_472);
 x_479 = lean::box(0);
}
if (lean::is_scalar(x_474)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_474;
}
lean::cnstr_set(x_480, 0, x_466);
lean::cnstr_set(x_480, 1, x_473);
x_481 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_481, 0, x_480);
lean::cnstr_set(x_481, 1, x_477);
if (lean::is_scalar(x_479)) {
 x_482 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_482 = x_479;
}
lean::cnstr_set(x_482, 0, x_475);
lean::cnstr_set(x_482, 1, x_476);
lean::cnstr_set(x_482, 2, x_481);
lean::cnstr_set(x_482, 3, x_478);
x_2 = x_388;
x_3 = x_482;
goto _start;
}
}
case 2:
{
obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_484 = lean::cnstr_get(x_395, 1);
lean::inc(x_484);
lean::dec(x_395);
x_485 = lean::cnstr_get(x_442, 0);
lean::inc(x_485);
lean::dec(x_442);
x_486 = lean::cnstr_get(x_464, 0);
lean::inc(x_486);
lean::dec(x_464);
x_487 = l___private_init_lean_expander_1__popStxArg(x_484, x_4);
if (lean::obj_tag(x_487) == 0)
{
obj* x_488; obj* x_489; obj* x_490; 
lean::dec(x_486);
lean::dec(x_485);
lean::dec(x_389);
lean::dec(x_388);
lean::dec(x_1);
x_488 = lean::cnstr_get(x_487, 0);
lean::inc(x_488);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 x_489 = x_487;
} else {
 lean::dec_ref(x_487);
 x_489 = lean::box(0);
}
if (lean::is_scalar(x_489)) {
 x_490 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_490 = x_489;
}
lean::cnstr_set(x_490, 0, x_488);
return x_490;
}
else
{
obj* x_491; obj* x_492; obj* x_493; 
x_491 = lean::cnstr_get(x_487, 0);
lean::inc(x_491);
lean::dec(x_487);
x_492 = lean::cnstr_get(x_491, 1);
lean::inc(x_492);
x_493 = lean::cnstr_get(x_492, 3);
lean::inc(x_493);
if (lean::obj_tag(x_493) == 0)
{
obj* x_494; 
lean::dec(x_491);
lean::dec(x_486);
lean::dec(x_485);
x_494 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_390, x_492, x_4);
lean::dec(x_492);
lean::dec(x_389);
if (lean::obj_tag(x_494) == 0)
{
obj* x_495; obj* x_496; obj* x_497; 
lean::dec(x_388);
lean::dec(x_1);
x_495 = lean::cnstr_get(x_494, 0);
lean::inc(x_495);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 x_496 = x_494;
} else {
 lean::dec_ref(x_494);
 x_496 = lean::box(0);
}
if (lean::is_scalar(x_496)) {
 x_497 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_497 = x_496;
}
lean::cnstr_set(x_497, 0, x_495);
return x_497;
}
else
{
obj* x_498; obj* x_499; 
x_498 = lean::cnstr_get(x_494, 0);
lean::inc(x_498);
lean::dec(x_494);
x_499 = lean::cnstr_get(x_498, 1);
lean::inc(x_499);
lean::dec(x_498);
x_2 = x_388;
x_3 = x_499;
goto _start;
}
}
else
{
obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; 
lean::dec(x_389);
x_501 = lean::cnstr_get(x_491, 0);
lean::inc(x_501);
if (lean::is_exclusive(x_491)) {
 lean::cnstr_release(x_491, 0);
 lean::cnstr_release(x_491, 1);
 x_502 = x_491;
} else {
 lean::dec_ref(x_491);
 x_502 = lean::box(0);
}
x_503 = lean::cnstr_get(x_492, 0);
lean::inc(x_503);
x_504 = lean::cnstr_get(x_492, 1);
lean::inc(x_504);
x_505 = lean::cnstr_get(x_492, 2);
lean::inc(x_505);
if (lean::is_exclusive(x_492)) {
 lean::cnstr_release(x_492, 0);
 lean::cnstr_release(x_492, 1);
 lean::cnstr_release(x_492, 2);
 lean::cnstr_release(x_492, 3);
 x_506 = x_492;
} else {
 lean::dec_ref(x_492);
 x_506 = lean::box(0);
}
x_507 = lean::cnstr_get(x_493, 0);
lean::inc(x_507);
x_508 = l_Lean_Parser_Term_lambda_HasView;
x_509 = lean::cnstr_get(x_508, 1);
lean::inc(x_509);
x_510 = lean::box(0);
x_511 = lean::cnstr_get(x_486, 3);
lean::inc(x_511);
x_512 = lean::box(0);
x_513 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_513, 0, x_511);
lean::cnstr_set(x_513, 1, x_512);
x_514 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_513);
x_515 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_515, 0, x_514);
lean::cnstr_set(x_515, 1, x_510);
x_516 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_516, 0, x_515);
x_517 = lean::cnstr_get(x_486, 5);
lean::inc(x_517);
lean::dec(x_486);
x_518 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_519 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_520 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_520, 0, x_518);
lean::cnstr_set(x_520, 1, x_516);
lean::cnstr_set(x_520, 2, x_519);
lean::cnstr_set(x_520, 3, x_517);
lean::inc(x_509);
x_521 = lean::apply_1(x_509, x_520);
x_522 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_522, 0, x_518);
lean::cnstr_set(x_522, 1, x_507);
lean::cnstr_set(x_522, 2, x_519);
lean::cnstr_set(x_522, 3, x_501);
x_523 = lean::apply_1(x_509, x_522);
x_524 = l_Lean_Parser_Term_app_HasView;
x_525 = lean::cnstr_get(x_524, 1);
lean::inc(x_525);
x_526 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_526, 0, x_521);
lean::cnstr_set(x_526, 1, x_523);
x_527 = lean::apply_1(x_525, x_526);
if (lean::is_scalar(x_502)) {
 x_528 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_528 = x_502;
}
lean::cnstr_set(x_528, 0, x_485);
lean::cnstr_set(x_528, 1, x_527);
x_529 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_529, 0, x_528);
lean::cnstr_set(x_529, 1, x_505);
if (lean::is_scalar(x_506)) {
 x_530 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_530 = x_506;
}
lean::cnstr_set(x_530, 0, x_503);
lean::cnstr_set(x_530, 1, x_504);
lean::cnstr_set(x_530, 2, x_529);
lean::cnstr_set(x_530, 3, x_493);
x_2 = x_388;
x_3 = x_530;
goto _start;
}
}
}
default: 
{
obj* x_532; obj* x_533; obj* x_534; 
lean::dec(x_464);
lean::dec(x_442);
x_532 = lean::cnstr_get(x_395, 1);
lean::inc(x_532);
lean::dec(x_395);
x_533 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_534 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_389, x_533, x_532, x_4);
lean::dec(x_532);
lean::dec(x_389);
if (lean::obj_tag(x_534) == 0)
{
obj* x_535; obj* x_536; obj* x_537; 
lean::dec(x_388);
lean::dec(x_1);
x_535 = lean::cnstr_get(x_534, 0);
lean::inc(x_535);
if (lean::is_exclusive(x_534)) {
 lean::cnstr_release(x_534, 0);
 x_536 = x_534;
} else {
 lean::dec_ref(x_534);
 x_536 = lean::box(0);
}
if (lean::is_scalar(x_536)) {
 x_537 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_537 = x_536;
}
lean::cnstr_set(x_537, 0, x_535);
return x_537;
}
else
{
obj* x_538; obj* x_539; 
x_538 = lean::cnstr_get(x_534, 0);
lean::inc(x_538);
lean::dec(x_534);
x_539 = lean::cnstr_get(x_538, 1);
lean::inc(x_539);
lean::dec(x_538);
x_2 = x_388;
x_3 = x_539;
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
else
{
uint8 x_541; 
lean::dec(x_10);
x_541 = !lean::is_exclusive(x_2);
if (x_541 == 0)
{
obj* x_542; obj* x_543; obj* x_544; 
x_542 = lean::cnstr_get(x_2, 1);
x_543 = lean::cnstr_get(x_2, 0);
lean::dec(x_543);
x_544 = l___private_init_lean_expander_1__popStxArg(x_3, x_4);
if (lean::obj_tag(x_544) == 0)
{
uint8 x_545; 
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_8);
lean::dec(x_1);
x_545 = !lean::is_exclusive(x_544);
if (x_545 == 0)
{
return x_544;
}
else
{
obj* x_546; obj* x_547; 
x_546 = lean::cnstr_get(x_544, 0);
lean::inc(x_546);
lean::dec(x_544);
x_547 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_547, 0, x_546);
return x_547;
}
}
else
{
obj* x_548; obj* x_549; 
x_548 = lean::cnstr_get(x_544, 0);
lean::inc(x_548);
lean::dec(x_544);
x_549 = lean::cnstr_get(x_8, 1);
lean::inc(x_549);
lean::dec(x_8);
if (lean::obj_tag(x_549) == 0)
{
obj* x_550; 
lean::free_heap_obj(x_2);
x_550 = lean::cnstr_get(x_548, 1);
lean::inc(x_550);
lean::dec(x_548);
x_2 = x_542;
x_3 = x_550;
goto _start;
}
else
{
uint8 x_552; 
x_552 = !lean::is_exclusive(x_549);
if (x_552 == 0)
{
obj* x_553; 
x_553 = lean::cnstr_get(x_549, 0);
switch (lean::obj_tag(x_553)) {
case 0:
{
obj* x_554; obj* x_555; 
lean::dec(x_553);
x_554 = lean::cnstr_get(x_548, 1);
lean::inc(x_554);
lean::dec(x_548);
x_555 = l___private_init_lean_expander_1__popStxArg(x_554, x_4);
if (lean::obj_tag(x_555) == 0)
{
uint8 x_556; 
lean::free_heap_obj(x_549);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_556 = !lean::is_exclusive(x_555);
if (x_556 == 0)
{
return x_555;
}
else
{
obj* x_557; obj* x_558; 
x_557 = lean::cnstr_get(x_555, 0);
lean::inc(x_557);
lean::dec(x_555);
x_558 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_558, 0, x_557);
return x_558;
}
}
else
{
obj* x_559; obj* x_560; obj* x_561; uint8 x_562; 
x_559 = lean::cnstr_get(x_555, 0);
lean::inc(x_559);
lean::dec(x_555);
x_560 = lean::cnstr_get(x_559, 1);
lean::inc(x_560);
x_561 = lean::cnstr_get(x_559, 0);
lean::inc(x_561);
lean::dec(x_559);
x_562 = !lean::is_exclusive(x_560);
if (x_562 == 0)
{
obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; 
x_563 = lean::cnstr_get(x_560, 3);
lean::dec(x_563);
x_564 = l_Lean_Parser_Term_binderIdent_HasView;
x_565 = lean::cnstr_get(x_564, 0);
lean::inc(x_565);
x_566 = lean::apply_1(x_565, x_561);
x_567 = lean::box(0);
lean::cnstr_set(x_2, 1, x_567);
lean::cnstr_set(x_2, 0, x_566);
x_568 = lean::box(0);
x_569 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_569, 0, x_2);
lean::cnstr_set(x_569, 1, x_568);
x_570 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_570, 0, x_569);
lean::cnstr_set(x_549, 0, x_570);
lean::cnstr_set(x_560, 3, x_549);
x_2 = x_542;
x_3 = x_560;
goto _start;
}
else
{
obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; 
x_572 = lean::cnstr_get(x_560, 0);
x_573 = lean::cnstr_get(x_560, 1);
x_574 = lean::cnstr_get(x_560, 2);
lean::inc(x_574);
lean::inc(x_573);
lean::inc(x_572);
lean::dec(x_560);
x_575 = l_Lean_Parser_Term_binderIdent_HasView;
x_576 = lean::cnstr_get(x_575, 0);
lean::inc(x_576);
x_577 = lean::apply_1(x_576, x_561);
x_578 = lean::box(0);
lean::cnstr_set(x_2, 1, x_578);
lean::cnstr_set(x_2, 0, x_577);
x_579 = lean::box(0);
x_580 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_580, 0, x_2);
lean::cnstr_set(x_580, 1, x_579);
x_581 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_549, 0, x_581);
x_582 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_582, 0, x_572);
lean::cnstr_set(x_582, 1, x_573);
lean::cnstr_set(x_582, 2, x_574);
lean::cnstr_set(x_582, 3, x_549);
x_2 = x_542;
x_3 = x_582;
goto _start;
}
}
}
case 1:
{
obj* x_584; obj* x_585; 
lean::dec(x_553);
lean::free_heap_obj(x_2);
x_584 = lean::cnstr_get(x_548, 1);
lean::inc(x_584);
lean::dec(x_548);
x_585 = l___private_init_lean_expander_1__popStxArg(x_584, x_4);
if (lean::obj_tag(x_585) == 0)
{
uint8 x_586; 
lean::free_heap_obj(x_549);
lean::dec(x_542);
lean::dec(x_1);
x_586 = !lean::is_exclusive(x_585);
if (x_586 == 0)
{
return x_585;
}
else
{
obj* x_587; obj* x_588; 
x_587 = lean::cnstr_get(x_585, 0);
lean::inc(x_587);
lean::dec(x_585);
x_588 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_588, 0, x_587);
return x_588;
}
}
else
{
obj* x_589; obj* x_590; obj* x_591; uint8 x_592; 
x_589 = lean::cnstr_get(x_585, 0);
lean::inc(x_589);
lean::dec(x_585);
x_590 = lean::cnstr_get(x_589, 1);
lean::inc(x_590);
x_591 = lean::cnstr_get(x_589, 0);
lean::inc(x_591);
lean::dec(x_589);
x_592 = !lean::is_exclusive(x_590);
if (x_592 == 0)
{
obj* x_593; obj* x_594; obj* x_595; obj* x_596; 
x_593 = lean::cnstr_get(x_590, 3);
lean::dec(x_593);
x_594 = l_Lean_Parser_Term_binders_HasView;
x_595 = lean::cnstr_get(x_594, 0);
lean::inc(x_595);
x_596 = lean::apply_1(x_595, x_591);
lean::cnstr_set(x_549, 0, x_596);
lean::cnstr_set(x_590, 3, x_549);
x_2 = x_542;
x_3 = x_590;
goto _start;
}
else
{
obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; 
x_598 = lean::cnstr_get(x_590, 0);
x_599 = lean::cnstr_get(x_590, 1);
x_600 = lean::cnstr_get(x_590, 2);
lean::inc(x_600);
lean::inc(x_599);
lean::inc(x_598);
lean::dec(x_590);
x_601 = l_Lean_Parser_Term_binders_HasView;
x_602 = lean::cnstr_get(x_601, 0);
lean::inc(x_602);
x_603 = lean::apply_1(x_602, x_591);
lean::cnstr_set(x_549, 0, x_603);
x_604 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_604, 0, x_598);
lean::cnstr_set(x_604, 1, x_599);
lean::cnstr_set(x_604, 2, x_600);
lean::cnstr_set(x_604, 3, x_549);
x_2 = x_542;
x_3 = x_604;
goto _start;
}
}
}
default: 
{
obj* x_606; obj* x_607; 
lean::free_heap_obj(x_549);
x_606 = lean::cnstr_get(x_553, 0);
lean::inc(x_606);
lean::dec(x_553);
x_607 = lean::cnstr_get(x_606, 1);
lean::inc(x_607);
if (lean::obj_tag(x_607) == 0)
{
obj* x_608; obj* x_609; obj* x_610; 
x_608 = lean::cnstr_get(x_548, 1);
lean::inc(x_608);
lean::dec(x_548);
x_609 = lean::cnstr_get(x_606, 0);
lean::inc(x_609);
lean::dec(x_606);
x_610 = l___private_init_lean_expander_1__popStxArg(x_608, x_4);
if (lean::obj_tag(x_610) == 0)
{
uint8 x_611; 
lean::dec(x_609);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_611 = !lean::is_exclusive(x_610);
if (x_611 == 0)
{
return x_610;
}
else
{
obj* x_612; obj* x_613; 
x_612 = lean::cnstr_get(x_610, 0);
lean::inc(x_612);
lean::dec(x_610);
x_613 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_613, 0, x_612);
return x_613;
}
}
else
{
obj* x_614; uint8 x_615; 
x_614 = lean::cnstr_get(x_610, 0);
lean::inc(x_614);
lean::dec(x_610);
x_615 = !lean::is_exclusive(x_614);
if (x_615 == 0)
{
obj* x_616; uint8 x_617; 
x_616 = lean::cnstr_get(x_614, 1);
x_617 = !lean::is_exclusive(x_616);
if (x_617 == 0)
{
obj* x_618; obj* x_619; 
x_618 = lean::cnstr_get(x_614, 0);
x_619 = lean::cnstr_get(x_616, 2);
lean::cnstr_set(x_614, 1, x_618);
lean::cnstr_set(x_614, 0, x_609);
lean::cnstr_set(x_2, 1, x_619);
lean::cnstr_set(x_2, 0, x_614);
lean::cnstr_set(x_616, 2, x_2);
x_2 = x_542;
x_3 = x_616;
goto _start;
}
else
{
obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; 
x_621 = lean::cnstr_get(x_614, 0);
x_622 = lean::cnstr_get(x_616, 0);
x_623 = lean::cnstr_get(x_616, 1);
x_624 = lean::cnstr_get(x_616, 2);
x_625 = lean::cnstr_get(x_616, 3);
lean::inc(x_625);
lean::inc(x_624);
lean::inc(x_623);
lean::inc(x_622);
lean::dec(x_616);
lean::cnstr_set(x_614, 1, x_621);
lean::cnstr_set(x_614, 0, x_609);
lean::cnstr_set(x_2, 1, x_624);
lean::cnstr_set(x_2, 0, x_614);
x_626 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_626, 0, x_622);
lean::cnstr_set(x_626, 1, x_623);
lean::cnstr_set(x_626, 2, x_2);
lean::cnstr_set(x_626, 3, x_625);
x_2 = x_542;
x_3 = x_626;
goto _start;
}
}
else
{
obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_636; 
x_628 = lean::cnstr_get(x_614, 1);
x_629 = lean::cnstr_get(x_614, 0);
lean::inc(x_628);
lean::inc(x_629);
lean::dec(x_614);
x_630 = lean::cnstr_get(x_628, 0);
lean::inc(x_630);
x_631 = lean::cnstr_get(x_628, 1);
lean::inc(x_631);
x_632 = lean::cnstr_get(x_628, 2);
lean::inc(x_632);
x_633 = lean::cnstr_get(x_628, 3);
lean::inc(x_633);
if (lean::is_exclusive(x_628)) {
 lean::cnstr_release(x_628, 0);
 lean::cnstr_release(x_628, 1);
 lean::cnstr_release(x_628, 2);
 lean::cnstr_release(x_628, 3);
 x_634 = x_628;
} else {
 lean::dec_ref(x_628);
 x_634 = lean::box(0);
}
x_635 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_635, 0, x_609);
lean::cnstr_set(x_635, 1, x_629);
lean::cnstr_set(x_2, 1, x_632);
lean::cnstr_set(x_2, 0, x_635);
if (lean::is_scalar(x_634)) {
 x_636 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_636 = x_634;
}
lean::cnstr_set(x_636, 0, x_630);
lean::cnstr_set(x_636, 1, x_631);
lean::cnstr_set(x_636, 2, x_2);
lean::cnstr_set(x_636, 3, x_633);
x_2 = x_542;
x_3 = x_636;
goto _start;
}
}
}
else
{
uint8 x_638; 
x_638 = !lean::is_exclusive(x_607);
if (x_638 == 0)
{
obj* x_639; obj* x_640; 
x_639 = lean::cnstr_get(x_607, 0);
x_640 = lean::cnstr_get(x_639, 1);
lean::inc(x_640);
lean::dec(x_639);
switch (lean::obj_tag(x_640)) {
case 0:
{
obj* x_641; obj* x_642; obj* x_643; 
lean::dec(x_640);
lean::free_heap_obj(x_607);
x_641 = lean::cnstr_get(x_548, 1);
lean::inc(x_641);
lean::dec(x_548);
x_642 = lean::cnstr_get(x_606, 0);
lean::inc(x_642);
lean::dec(x_606);
x_643 = l___private_init_lean_expander_1__popStxArg(x_641, x_4);
if (lean::obj_tag(x_643) == 0)
{
uint8 x_644; 
lean::dec(x_642);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_644 = !lean::is_exclusive(x_643);
if (x_644 == 0)
{
return x_643;
}
else
{
obj* x_645; obj* x_646; 
x_645 = lean::cnstr_get(x_643, 0);
lean::inc(x_645);
lean::dec(x_643);
x_646 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_646, 0, x_645);
return x_646;
}
}
else
{
obj* x_647; uint8 x_648; 
x_647 = lean::cnstr_get(x_643, 0);
lean::inc(x_647);
lean::dec(x_643);
x_648 = !lean::is_exclusive(x_647);
if (x_648 == 0)
{
obj* x_649; uint8 x_650; 
x_649 = lean::cnstr_get(x_647, 1);
x_650 = !lean::is_exclusive(x_649);
if (x_650 == 0)
{
obj* x_651; obj* x_652; 
x_651 = lean::cnstr_get(x_647, 0);
x_652 = lean::cnstr_get(x_649, 2);
lean::cnstr_set(x_647, 1, x_651);
lean::cnstr_set(x_647, 0, x_642);
lean::cnstr_set(x_2, 1, x_652);
lean::cnstr_set(x_2, 0, x_647);
lean::cnstr_set(x_649, 2, x_2);
x_2 = x_542;
x_3 = x_649;
goto _start;
}
else
{
obj* x_654; obj* x_655; obj* x_656; obj* x_657; obj* x_658; obj* x_659; 
x_654 = lean::cnstr_get(x_647, 0);
x_655 = lean::cnstr_get(x_649, 0);
x_656 = lean::cnstr_get(x_649, 1);
x_657 = lean::cnstr_get(x_649, 2);
x_658 = lean::cnstr_get(x_649, 3);
lean::inc(x_658);
lean::inc(x_657);
lean::inc(x_656);
lean::inc(x_655);
lean::dec(x_649);
lean::cnstr_set(x_647, 1, x_654);
lean::cnstr_set(x_647, 0, x_642);
lean::cnstr_set(x_2, 1, x_657);
lean::cnstr_set(x_2, 0, x_647);
x_659 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_659, 0, x_655);
lean::cnstr_set(x_659, 1, x_656);
lean::cnstr_set(x_659, 2, x_2);
lean::cnstr_set(x_659, 3, x_658);
x_2 = x_542;
x_3 = x_659;
goto _start;
}
}
else
{
obj* x_661; obj* x_662; obj* x_663; obj* x_664; obj* x_665; obj* x_666; obj* x_667; obj* x_668; obj* x_669; 
x_661 = lean::cnstr_get(x_647, 1);
x_662 = lean::cnstr_get(x_647, 0);
lean::inc(x_661);
lean::inc(x_662);
lean::dec(x_647);
x_663 = lean::cnstr_get(x_661, 0);
lean::inc(x_663);
x_664 = lean::cnstr_get(x_661, 1);
lean::inc(x_664);
x_665 = lean::cnstr_get(x_661, 2);
lean::inc(x_665);
x_666 = lean::cnstr_get(x_661, 3);
lean::inc(x_666);
if (lean::is_exclusive(x_661)) {
 lean::cnstr_release(x_661, 0);
 lean::cnstr_release(x_661, 1);
 lean::cnstr_release(x_661, 2);
 lean::cnstr_release(x_661, 3);
 x_667 = x_661;
} else {
 lean::dec_ref(x_661);
 x_667 = lean::box(0);
}
x_668 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_668, 0, x_642);
lean::cnstr_set(x_668, 1, x_662);
lean::cnstr_set(x_2, 1, x_665);
lean::cnstr_set(x_2, 0, x_668);
if (lean::is_scalar(x_667)) {
 x_669 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_669 = x_667;
}
lean::cnstr_set(x_669, 0, x_663);
lean::cnstr_set(x_669, 1, x_664);
lean::cnstr_set(x_669, 2, x_2);
lean::cnstr_set(x_669, 3, x_666);
x_2 = x_542;
x_3 = x_669;
goto _start;
}
}
}
case 2:
{
obj* x_671; obj* x_672; obj* x_673; obj* x_674; 
x_671 = lean::cnstr_get(x_548, 1);
lean::inc(x_671);
lean::dec(x_548);
x_672 = lean::cnstr_get(x_606, 0);
lean::inc(x_672);
lean::dec(x_606);
x_673 = lean::cnstr_get(x_640, 0);
lean::inc(x_673);
lean::dec(x_640);
x_674 = l___private_init_lean_expander_1__popStxArg(x_671, x_4);
if (lean::obj_tag(x_674) == 0)
{
uint8 x_675; 
lean::dec(x_673);
lean::dec(x_672);
lean::free_heap_obj(x_607);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_675 = !lean::is_exclusive(x_674);
if (x_675 == 0)
{
return x_674;
}
else
{
obj* x_676; obj* x_677; 
x_676 = lean::cnstr_get(x_674, 0);
lean::inc(x_676);
lean::dec(x_674);
x_677 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_677, 0, x_676);
return x_677;
}
}
else
{
obj* x_678; obj* x_679; obj* x_680; 
x_678 = lean::cnstr_get(x_674, 0);
lean::inc(x_678);
lean::dec(x_674);
x_679 = lean::cnstr_get(x_678, 1);
lean::inc(x_679);
x_680 = lean::cnstr_get(x_679, 3);
lean::inc(x_680);
if (lean::obj_tag(x_680) == 0)
{
obj* x_681; obj* x_682; 
lean::dec(x_678);
lean::dec(x_673);
lean::dec(x_672);
lean::free_heap_obj(x_2);
lean::inc(x_1);
lean::cnstr_set(x_607, 0, x_1);
x_681 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_682 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_607, x_681, x_679, x_4);
lean::dec(x_679);
lean::dec(x_607);
if (lean::obj_tag(x_682) == 0)
{
uint8 x_683; 
lean::dec(x_542);
lean::dec(x_1);
x_683 = !lean::is_exclusive(x_682);
if (x_683 == 0)
{
return x_682;
}
else
{
obj* x_684; obj* x_685; 
x_684 = lean::cnstr_get(x_682, 0);
lean::inc(x_684);
lean::dec(x_682);
x_685 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_685, 0, x_684);
return x_685;
}
}
else
{
obj* x_686; obj* x_687; 
x_686 = lean::cnstr_get(x_682, 0);
lean::inc(x_686);
lean::dec(x_682);
x_687 = lean::cnstr_get(x_686, 1);
lean::inc(x_687);
lean::dec(x_686);
x_2 = x_542;
x_3 = x_687;
goto _start;
}
}
else
{
uint8 x_689; 
lean::free_heap_obj(x_607);
x_689 = !lean::is_exclusive(x_678);
if (x_689 == 0)
{
obj* x_690; obj* x_691; uint8 x_692; 
x_690 = lean::cnstr_get(x_678, 0);
x_691 = lean::cnstr_get(x_678, 1);
lean::dec(x_691);
x_692 = !lean::is_exclusive(x_679);
if (x_692 == 0)
{
obj* x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; obj* x_710; obj* x_711; obj* x_712; obj* x_713; obj* x_714; obj* x_715; 
x_693 = lean::cnstr_get(x_679, 2);
x_694 = lean::cnstr_get(x_679, 3);
lean::dec(x_694);
x_695 = lean::cnstr_get(x_680, 0);
lean::inc(x_695);
x_696 = l_Lean_Parser_Term_lambda_HasView;
x_697 = lean::cnstr_get(x_696, 1);
lean::inc(x_697);
x_698 = lean::box(0);
x_699 = lean::cnstr_get(x_673, 3);
lean::inc(x_699);
x_700 = lean::box(0);
lean::cnstr_set(x_2, 1, x_700);
lean::cnstr_set(x_2, 0, x_699);
x_701 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_702 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_702, 0, x_701);
lean::cnstr_set(x_702, 1, x_698);
x_703 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_703, 0, x_702);
x_704 = lean::cnstr_get(x_673, 5);
lean::inc(x_704);
lean::dec(x_673);
x_705 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_706 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_707 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_707, 0, x_705);
lean::cnstr_set(x_707, 1, x_703);
lean::cnstr_set(x_707, 2, x_706);
lean::cnstr_set(x_707, 3, x_704);
lean::inc(x_697);
x_708 = lean::apply_1(x_697, x_707);
x_709 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_709, 0, x_705);
lean::cnstr_set(x_709, 1, x_695);
lean::cnstr_set(x_709, 2, x_706);
lean::cnstr_set(x_709, 3, x_690);
x_710 = lean::apply_1(x_697, x_709);
x_711 = l_Lean_Parser_Term_app_HasView;
x_712 = lean::cnstr_get(x_711, 1);
lean::inc(x_712);
x_713 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_713, 0, x_708);
lean::cnstr_set(x_713, 1, x_710);
x_714 = lean::apply_1(x_712, x_713);
lean::cnstr_set(x_678, 1, x_714);
lean::cnstr_set(x_678, 0, x_672);
x_715 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_715, 0, x_678);
lean::cnstr_set(x_715, 1, x_693);
lean::cnstr_set(x_679, 2, x_715);
x_2 = x_542;
x_3 = x_679;
goto _start;
}
else
{
obj* x_717; obj* x_718; obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; obj* x_725; obj* x_726; obj* x_727; obj* x_728; obj* x_729; obj* x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; 
x_717 = lean::cnstr_get(x_679, 0);
x_718 = lean::cnstr_get(x_679, 1);
x_719 = lean::cnstr_get(x_679, 2);
lean::inc(x_719);
lean::inc(x_718);
lean::inc(x_717);
lean::dec(x_679);
x_720 = lean::cnstr_get(x_680, 0);
lean::inc(x_720);
x_721 = l_Lean_Parser_Term_lambda_HasView;
x_722 = lean::cnstr_get(x_721, 1);
lean::inc(x_722);
x_723 = lean::box(0);
x_724 = lean::cnstr_get(x_673, 3);
lean::inc(x_724);
x_725 = lean::box(0);
lean::cnstr_set(x_2, 1, x_725);
lean::cnstr_set(x_2, 0, x_724);
x_726 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_727 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_727, 0, x_726);
lean::cnstr_set(x_727, 1, x_723);
x_728 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_728, 0, x_727);
x_729 = lean::cnstr_get(x_673, 5);
lean::inc(x_729);
lean::dec(x_673);
x_730 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_731 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_732 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_732, 0, x_730);
lean::cnstr_set(x_732, 1, x_728);
lean::cnstr_set(x_732, 2, x_731);
lean::cnstr_set(x_732, 3, x_729);
lean::inc(x_722);
x_733 = lean::apply_1(x_722, x_732);
x_734 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_734, 0, x_730);
lean::cnstr_set(x_734, 1, x_720);
lean::cnstr_set(x_734, 2, x_731);
lean::cnstr_set(x_734, 3, x_690);
x_735 = lean::apply_1(x_722, x_734);
x_736 = l_Lean_Parser_Term_app_HasView;
x_737 = lean::cnstr_get(x_736, 1);
lean::inc(x_737);
x_738 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_738, 0, x_733);
lean::cnstr_set(x_738, 1, x_735);
x_739 = lean::apply_1(x_737, x_738);
lean::cnstr_set(x_678, 1, x_739);
lean::cnstr_set(x_678, 0, x_672);
x_740 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_740, 0, x_678);
lean::cnstr_set(x_740, 1, x_719);
x_741 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_741, 0, x_717);
lean::cnstr_set(x_741, 1, x_718);
lean::cnstr_set(x_741, 2, x_740);
lean::cnstr_set(x_741, 3, x_680);
x_2 = x_542;
x_3 = x_741;
goto _start;
}
}
else
{
obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; obj* x_751; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; obj* x_761; obj* x_762; obj* x_763; obj* x_764; obj* x_765; obj* x_766; obj* x_767; obj* x_768; obj* x_769; obj* x_770; 
x_743 = lean::cnstr_get(x_678, 0);
lean::inc(x_743);
lean::dec(x_678);
x_744 = lean::cnstr_get(x_679, 0);
lean::inc(x_744);
x_745 = lean::cnstr_get(x_679, 1);
lean::inc(x_745);
x_746 = lean::cnstr_get(x_679, 2);
lean::inc(x_746);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_747 = x_679;
} else {
 lean::dec_ref(x_679);
 x_747 = lean::box(0);
}
x_748 = lean::cnstr_get(x_680, 0);
lean::inc(x_748);
x_749 = l_Lean_Parser_Term_lambda_HasView;
x_750 = lean::cnstr_get(x_749, 1);
lean::inc(x_750);
x_751 = lean::box(0);
x_752 = lean::cnstr_get(x_673, 3);
lean::inc(x_752);
x_753 = lean::box(0);
lean::cnstr_set(x_2, 1, x_753);
lean::cnstr_set(x_2, 0, x_752);
x_754 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_755 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_755, 0, x_754);
lean::cnstr_set(x_755, 1, x_751);
x_756 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_756, 0, x_755);
x_757 = lean::cnstr_get(x_673, 5);
lean::inc(x_757);
lean::dec(x_673);
x_758 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_759 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_760 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_760, 0, x_758);
lean::cnstr_set(x_760, 1, x_756);
lean::cnstr_set(x_760, 2, x_759);
lean::cnstr_set(x_760, 3, x_757);
lean::inc(x_750);
x_761 = lean::apply_1(x_750, x_760);
x_762 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_762, 0, x_758);
lean::cnstr_set(x_762, 1, x_748);
lean::cnstr_set(x_762, 2, x_759);
lean::cnstr_set(x_762, 3, x_743);
x_763 = lean::apply_1(x_750, x_762);
x_764 = l_Lean_Parser_Term_app_HasView;
x_765 = lean::cnstr_get(x_764, 1);
lean::inc(x_765);
x_766 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_766, 0, x_761);
lean::cnstr_set(x_766, 1, x_763);
x_767 = lean::apply_1(x_765, x_766);
x_768 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_768, 0, x_672);
lean::cnstr_set(x_768, 1, x_767);
x_769 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_769, 0, x_768);
lean::cnstr_set(x_769, 1, x_746);
if (lean::is_scalar(x_747)) {
 x_770 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_770 = x_747;
}
lean::cnstr_set(x_770, 0, x_744);
lean::cnstr_set(x_770, 1, x_745);
lean::cnstr_set(x_770, 2, x_769);
lean::cnstr_set(x_770, 3, x_680);
x_2 = x_542;
x_3 = x_770;
goto _start;
}
}
}
}
default: 
{
obj* x_772; obj* x_773; obj* x_774; 
lean::dec(x_640);
lean::dec(x_606);
lean::free_heap_obj(x_2);
x_772 = lean::cnstr_get(x_548, 1);
lean::inc(x_772);
lean::dec(x_548);
lean::inc(x_1);
lean::cnstr_set(x_607, 0, x_1);
x_773 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_774 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_607, x_773, x_772, x_4);
lean::dec(x_772);
lean::dec(x_607);
if (lean::obj_tag(x_774) == 0)
{
uint8 x_775; 
lean::dec(x_542);
lean::dec(x_1);
x_775 = !lean::is_exclusive(x_774);
if (x_775 == 0)
{
return x_774;
}
else
{
obj* x_776; obj* x_777; 
x_776 = lean::cnstr_get(x_774, 0);
lean::inc(x_776);
lean::dec(x_774);
x_777 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_777, 0, x_776);
return x_777;
}
}
else
{
obj* x_778; obj* x_779; 
x_778 = lean::cnstr_get(x_774, 0);
lean::inc(x_778);
lean::dec(x_774);
x_779 = lean::cnstr_get(x_778, 1);
lean::inc(x_779);
lean::dec(x_778);
x_2 = x_542;
x_3 = x_779;
goto _start;
}
}
}
}
else
{
obj* x_781; obj* x_782; 
x_781 = lean::cnstr_get(x_607, 0);
lean::inc(x_781);
lean::dec(x_607);
x_782 = lean::cnstr_get(x_781, 1);
lean::inc(x_782);
lean::dec(x_781);
switch (lean::obj_tag(x_782)) {
case 0:
{
obj* x_783; obj* x_784; obj* x_785; 
lean::dec(x_782);
x_783 = lean::cnstr_get(x_548, 1);
lean::inc(x_783);
lean::dec(x_548);
x_784 = lean::cnstr_get(x_606, 0);
lean::inc(x_784);
lean::dec(x_606);
x_785 = l___private_init_lean_expander_1__popStxArg(x_783, x_4);
if (lean::obj_tag(x_785) == 0)
{
obj* x_786; obj* x_787; obj* x_788; 
lean::dec(x_784);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_786 = lean::cnstr_get(x_785, 0);
lean::inc(x_786);
if (lean::is_exclusive(x_785)) {
 lean::cnstr_release(x_785, 0);
 x_787 = x_785;
} else {
 lean::dec_ref(x_785);
 x_787 = lean::box(0);
}
if (lean::is_scalar(x_787)) {
 x_788 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_788 = x_787;
}
lean::cnstr_set(x_788, 0, x_786);
return x_788;
}
else
{
obj* x_789; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; obj* x_796; obj* x_797; obj* x_798; obj* x_799; 
x_789 = lean::cnstr_get(x_785, 0);
lean::inc(x_789);
lean::dec(x_785);
x_790 = lean::cnstr_get(x_789, 1);
lean::inc(x_790);
x_791 = lean::cnstr_get(x_789, 0);
lean::inc(x_791);
if (lean::is_exclusive(x_789)) {
 lean::cnstr_release(x_789, 0);
 lean::cnstr_release(x_789, 1);
 x_792 = x_789;
} else {
 lean::dec_ref(x_789);
 x_792 = lean::box(0);
}
x_793 = lean::cnstr_get(x_790, 0);
lean::inc(x_793);
x_794 = lean::cnstr_get(x_790, 1);
lean::inc(x_794);
x_795 = lean::cnstr_get(x_790, 2);
lean::inc(x_795);
x_796 = lean::cnstr_get(x_790, 3);
lean::inc(x_796);
if (lean::is_exclusive(x_790)) {
 lean::cnstr_release(x_790, 0);
 lean::cnstr_release(x_790, 1);
 lean::cnstr_release(x_790, 2);
 lean::cnstr_release(x_790, 3);
 x_797 = x_790;
} else {
 lean::dec_ref(x_790);
 x_797 = lean::box(0);
}
if (lean::is_scalar(x_792)) {
 x_798 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_798 = x_792;
}
lean::cnstr_set(x_798, 0, x_784);
lean::cnstr_set(x_798, 1, x_791);
lean::cnstr_set(x_2, 1, x_795);
lean::cnstr_set(x_2, 0, x_798);
if (lean::is_scalar(x_797)) {
 x_799 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_799 = x_797;
}
lean::cnstr_set(x_799, 0, x_793);
lean::cnstr_set(x_799, 1, x_794);
lean::cnstr_set(x_799, 2, x_2);
lean::cnstr_set(x_799, 3, x_796);
x_2 = x_542;
x_3 = x_799;
goto _start;
}
}
case 2:
{
obj* x_801; obj* x_802; obj* x_803; obj* x_804; 
x_801 = lean::cnstr_get(x_548, 1);
lean::inc(x_801);
lean::dec(x_548);
x_802 = lean::cnstr_get(x_606, 0);
lean::inc(x_802);
lean::dec(x_606);
x_803 = lean::cnstr_get(x_782, 0);
lean::inc(x_803);
lean::dec(x_782);
x_804 = l___private_init_lean_expander_1__popStxArg(x_801, x_4);
if (lean::obj_tag(x_804) == 0)
{
obj* x_805; obj* x_806; obj* x_807; 
lean::dec(x_803);
lean::dec(x_802);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_805 = lean::cnstr_get(x_804, 0);
lean::inc(x_805);
if (lean::is_exclusive(x_804)) {
 lean::cnstr_release(x_804, 0);
 x_806 = x_804;
} else {
 lean::dec_ref(x_804);
 x_806 = lean::box(0);
}
if (lean::is_scalar(x_806)) {
 x_807 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_807 = x_806;
}
lean::cnstr_set(x_807, 0, x_805);
return x_807;
}
else
{
obj* x_808; obj* x_809; obj* x_810; 
x_808 = lean::cnstr_get(x_804, 0);
lean::inc(x_808);
lean::dec(x_804);
x_809 = lean::cnstr_get(x_808, 1);
lean::inc(x_809);
x_810 = lean::cnstr_get(x_809, 3);
lean::inc(x_810);
if (lean::obj_tag(x_810) == 0)
{
obj* x_811; obj* x_812; obj* x_813; 
lean::dec(x_808);
lean::dec(x_803);
lean::dec(x_802);
lean::free_heap_obj(x_2);
lean::inc(x_1);
x_811 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_811, 0, x_1);
x_812 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_813 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_811, x_812, x_809, x_4);
lean::dec(x_809);
lean::dec(x_811);
if (lean::obj_tag(x_813) == 0)
{
obj* x_814; obj* x_815; obj* x_816; 
lean::dec(x_542);
lean::dec(x_1);
x_814 = lean::cnstr_get(x_813, 0);
lean::inc(x_814);
if (lean::is_exclusive(x_813)) {
 lean::cnstr_release(x_813, 0);
 x_815 = x_813;
} else {
 lean::dec_ref(x_813);
 x_815 = lean::box(0);
}
if (lean::is_scalar(x_815)) {
 x_816 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_816 = x_815;
}
lean::cnstr_set(x_816, 0, x_814);
return x_816;
}
else
{
obj* x_817; obj* x_818; 
x_817 = lean::cnstr_get(x_813, 0);
lean::inc(x_817);
lean::dec(x_813);
x_818 = lean::cnstr_get(x_817, 1);
lean::inc(x_818);
lean::dec(x_817);
x_2 = x_542;
x_3 = x_818;
goto _start;
}
}
else
{
obj* x_820; obj* x_821; obj* x_822; obj* x_823; obj* x_824; obj* x_825; obj* x_826; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; obj* x_836; obj* x_837; obj* x_838; obj* x_839; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; obj* x_846; obj* x_847; obj* x_848; 
x_820 = lean::cnstr_get(x_808, 0);
lean::inc(x_820);
if (lean::is_exclusive(x_808)) {
 lean::cnstr_release(x_808, 0);
 lean::cnstr_release(x_808, 1);
 x_821 = x_808;
} else {
 lean::dec_ref(x_808);
 x_821 = lean::box(0);
}
x_822 = lean::cnstr_get(x_809, 0);
lean::inc(x_822);
x_823 = lean::cnstr_get(x_809, 1);
lean::inc(x_823);
x_824 = lean::cnstr_get(x_809, 2);
lean::inc(x_824);
if (lean::is_exclusive(x_809)) {
 lean::cnstr_release(x_809, 0);
 lean::cnstr_release(x_809, 1);
 lean::cnstr_release(x_809, 2);
 lean::cnstr_release(x_809, 3);
 x_825 = x_809;
} else {
 lean::dec_ref(x_809);
 x_825 = lean::box(0);
}
x_826 = lean::cnstr_get(x_810, 0);
lean::inc(x_826);
x_827 = l_Lean_Parser_Term_lambda_HasView;
x_828 = lean::cnstr_get(x_827, 1);
lean::inc(x_828);
x_829 = lean::box(0);
x_830 = lean::cnstr_get(x_803, 3);
lean::inc(x_830);
x_831 = lean::box(0);
lean::cnstr_set(x_2, 1, x_831);
lean::cnstr_set(x_2, 0, x_830);
x_832 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_833 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_833, 0, x_832);
lean::cnstr_set(x_833, 1, x_829);
x_834 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_834, 0, x_833);
x_835 = lean::cnstr_get(x_803, 5);
lean::inc(x_835);
lean::dec(x_803);
x_836 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_837 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_838 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_838, 0, x_836);
lean::cnstr_set(x_838, 1, x_834);
lean::cnstr_set(x_838, 2, x_837);
lean::cnstr_set(x_838, 3, x_835);
lean::inc(x_828);
x_839 = lean::apply_1(x_828, x_838);
x_840 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_840, 0, x_836);
lean::cnstr_set(x_840, 1, x_826);
lean::cnstr_set(x_840, 2, x_837);
lean::cnstr_set(x_840, 3, x_820);
x_841 = lean::apply_1(x_828, x_840);
x_842 = l_Lean_Parser_Term_app_HasView;
x_843 = lean::cnstr_get(x_842, 1);
lean::inc(x_843);
x_844 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_844, 0, x_839);
lean::cnstr_set(x_844, 1, x_841);
x_845 = lean::apply_1(x_843, x_844);
if (lean::is_scalar(x_821)) {
 x_846 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_846 = x_821;
}
lean::cnstr_set(x_846, 0, x_802);
lean::cnstr_set(x_846, 1, x_845);
x_847 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_847, 0, x_846);
lean::cnstr_set(x_847, 1, x_824);
if (lean::is_scalar(x_825)) {
 x_848 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_848 = x_825;
}
lean::cnstr_set(x_848, 0, x_822);
lean::cnstr_set(x_848, 1, x_823);
lean::cnstr_set(x_848, 2, x_847);
lean::cnstr_set(x_848, 3, x_810);
x_2 = x_542;
x_3 = x_848;
goto _start;
}
}
}
default: 
{
obj* x_850; obj* x_851; obj* x_852; obj* x_853; 
lean::dec(x_782);
lean::dec(x_606);
lean::free_heap_obj(x_2);
x_850 = lean::cnstr_get(x_548, 1);
lean::inc(x_850);
lean::dec(x_548);
lean::inc(x_1);
x_851 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_851, 0, x_1);
x_852 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_853 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_851, x_852, x_850, x_4);
lean::dec(x_850);
lean::dec(x_851);
if (lean::obj_tag(x_853) == 0)
{
obj* x_854; obj* x_855; obj* x_856; 
lean::dec(x_542);
lean::dec(x_1);
x_854 = lean::cnstr_get(x_853, 0);
lean::inc(x_854);
if (lean::is_exclusive(x_853)) {
 lean::cnstr_release(x_853, 0);
 x_855 = x_853;
} else {
 lean::dec_ref(x_853);
 x_855 = lean::box(0);
}
if (lean::is_scalar(x_855)) {
 x_856 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_856 = x_855;
}
lean::cnstr_set(x_856, 0, x_854);
return x_856;
}
else
{
obj* x_857; obj* x_858; 
x_857 = lean::cnstr_get(x_853, 0);
lean::inc(x_857);
lean::dec(x_853);
x_858 = lean::cnstr_get(x_857, 1);
lean::inc(x_858);
lean::dec(x_857);
x_2 = x_542;
x_3 = x_858;
goto _start;
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
obj* x_860; 
x_860 = lean::cnstr_get(x_549, 0);
lean::inc(x_860);
lean::dec(x_549);
switch (lean::obj_tag(x_860)) {
case 0:
{
obj* x_861; obj* x_862; 
lean::dec(x_860);
x_861 = lean::cnstr_get(x_548, 1);
lean::inc(x_861);
lean::dec(x_548);
x_862 = l___private_init_lean_expander_1__popStxArg(x_861, x_4);
if (lean::obj_tag(x_862) == 0)
{
obj* x_863; obj* x_864; obj* x_865; 
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_863 = lean::cnstr_get(x_862, 0);
lean::inc(x_863);
if (lean::is_exclusive(x_862)) {
 lean::cnstr_release(x_862, 0);
 x_864 = x_862;
} else {
 lean::dec_ref(x_862);
 x_864 = lean::box(0);
}
if (lean::is_scalar(x_864)) {
 x_865 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_865 = x_864;
}
lean::cnstr_set(x_865, 0, x_863);
return x_865;
}
else
{
obj* x_866; obj* x_867; obj* x_868; obj* x_869; obj* x_870; obj* x_871; obj* x_872; obj* x_873; obj* x_874; obj* x_875; obj* x_876; obj* x_877; obj* x_878; obj* x_879; obj* x_880; obj* x_881; 
x_866 = lean::cnstr_get(x_862, 0);
lean::inc(x_866);
lean::dec(x_862);
x_867 = lean::cnstr_get(x_866, 1);
lean::inc(x_867);
x_868 = lean::cnstr_get(x_866, 0);
lean::inc(x_868);
lean::dec(x_866);
x_869 = lean::cnstr_get(x_867, 0);
lean::inc(x_869);
x_870 = lean::cnstr_get(x_867, 1);
lean::inc(x_870);
x_871 = lean::cnstr_get(x_867, 2);
lean::inc(x_871);
if (lean::is_exclusive(x_867)) {
 lean::cnstr_release(x_867, 0);
 lean::cnstr_release(x_867, 1);
 lean::cnstr_release(x_867, 2);
 lean::cnstr_release(x_867, 3);
 x_872 = x_867;
} else {
 lean::dec_ref(x_867);
 x_872 = lean::box(0);
}
x_873 = l_Lean_Parser_Term_binderIdent_HasView;
x_874 = lean::cnstr_get(x_873, 0);
lean::inc(x_874);
x_875 = lean::apply_1(x_874, x_868);
x_876 = lean::box(0);
lean::cnstr_set(x_2, 1, x_876);
lean::cnstr_set(x_2, 0, x_875);
x_877 = lean::box(0);
x_878 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_878, 0, x_2);
lean::cnstr_set(x_878, 1, x_877);
x_879 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_879, 0, x_878);
x_880 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_880, 0, x_879);
if (lean::is_scalar(x_872)) {
 x_881 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_881 = x_872;
}
lean::cnstr_set(x_881, 0, x_869);
lean::cnstr_set(x_881, 1, x_870);
lean::cnstr_set(x_881, 2, x_871);
lean::cnstr_set(x_881, 3, x_880);
x_2 = x_542;
x_3 = x_881;
goto _start;
}
}
case 1:
{
obj* x_883; obj* x_884; 
lean::dec(x_860);
lean::free_heap_obj(x_2);
x_883 = lean::cnstr_get(x_548, 1);
lean::inc(x_883);
lean::dec(x_548);
x_884 = l___private_init_lean_expander_1__popStxArg(x_883, x_4);
if (lean::obj_tag(x_884) == 0)
{
obj* x_885; obj* x_886; obj* x_887; 
lean::dec(x_542);
lean::dec(x_1);
x_885 = lean::cnstr_get(x_884, 0);
lean::inc(x_885);
if (lean::is_exclusive(x_884)) {
 lean::cnstr_release(x_884, 0);
 x_886 = x_884;
} else {
 lean::dec_ref(x_884);
 x_886 = lean::box(0);
}
if (lean::is_scalar(x_886)) {
 x_887 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_887 = x_886;
}
lean::cnstr_set(x_887, 0, x_885);
return x_887;
}
else
{
obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_896; obj* x_897; obj* x_898; obj* x_899; 
x_888 = lean::cnstr_get(x_884, 0);
lean::inc(x_888);
lean::dec(x_884);
x_889 = lean::cnstr_get(x_888, 1);
lean::inc(x_889);
x_890 = lean::cnstr_get(x_888, 0);
lean::inc(x_890);
lean::dec(x_888);
x_891 = lean::cnstr_get(x_889, 0);
lean::inc(x_891);
x_892 = lean::cnstr_get(x_889, 1);
lean::inc(x_892);
x_893 = lean::cnstr_get(x_889, 2);
lean::inc(x_893);
if (lean::is_exclusive(x_889)) {
 lean::cnstr_release(x_889, 0);
 lean::cnstr_release(x_889, 1);
 lean::cnstr_release(x_889, 2);
 lean::cnstr_release(x_889, 3);
 x_894 = x_889;
} else {
 lean::dec_ref(x_889);
 x_894 = lean::box(0);
}
x_895 = l_Lean_Parser_Term_binders_HasView;
x_896 = lean::cnstr_get(x_895, 0);
lean::inc(x_896);
x_897 = lean::apply_1(x_896, x_890);
x_898 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_898, 0, x_897);
if (lean::is_scalar(x_894)) {
 x_899 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_899 = x_894;
}
lean::cnstr_set(x_899, 0, x_891);
lean::cnstr_set(x_899, 1, x_892);
lean::cnstr_set(x_899, 2, x_893);
lean::cnstr_set(x_899, 3, x_898);
x_2 = x_542;
x_3 = x_899;
goto _start;
}
}
default: 
{
obj* x_901; obj* x_902; 
x_901 = lean::cnstr_get(x_860, 0);
lean::inc(x_901);
lean::dec(x_860);
x_902 = lean::cnstr_get(x_901, 1);
lean::inc(x_902);
if (lean::obj_tag(x_902) == 0)
{
obj* x_903; obj* x_904; obj* x_905; 
x_903 = lean::cnstr_get(x_548, 1);
lean::inc(x_903);
lean::dec(x_548);
x_904 = lean::cnstr_get(x_901, 0);
lean::inc(x_904);
lean::dec(x_901);
x_905 = l___private_init_lean_expander_1__popStxArg(x_903, x_4);
if (lean::obj_tag(x_905) == 0)
{
obj* x_906; obj* x_907; obj* x_908; 
lean::dec(x_904);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_906 = lean::cnstr_get(x_905, 0);
lean::inc(x_906);
if (lean::is_exclusive(x_905)) {
 lean::cnstr_release(x_905, 0);
 x_907 = x_905;
} else {
 lean::dec_ref(x_905);
 x_907 = lean::box(0);
}
if (lean::is_scalar(x_907)) {
 x_908 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_908 = x_907;
}
lean::cnstr_set(x_908, 0, x_906);
return x_908;
}
else
{
obj* x_909; obj* x_910; obj* x_911; obj* x_912; obj* x_913; obj* x_914; obj* x_915; obj* x_916; obj* x_917; obj* x_918; obj* x_919; 
x_909 = lean::cnstr_get(x_905, 0);
lean::inc(x_909);
lean::dec(x_905);
x_910 = lean::cnstr_get(x_909, 1);
lean::inc(x_910);
x_911 = lean::cnstr_get(x_909, 0);
lean::inc(x_911);
if (lean::is_exclusive(x_909)) {
 lean::cnstr_release(x_909, 0);
 lean::cnstr_release(x_909, 1);
 x_912 = x_909;
} else {
 lean::dec_ref(x_909);
 x_912 = lean::box(0);
}
x_913 = lean::cnstr_get(x_910, 0);
lean::inc(x_913);
x_914 = lean::cnstr_get(x_910, 1);
lean::inc(x_914);
x_915 = lean::cnstr_get(x_910, 2);
lean::inc(x_915);
x_916 = lean::cnstr_get(x_910, 3);
lean::inc(x_916);
if (lean::is_exclusive(x_910)) {
 lean::cnstr_release(x_910, 0);
 lean::cnstr_release(x_910, 1);
 lean::cnstr_release(x_910, 2);
 lean::cnstr_release(x_910, 3);
 x_917 = x_910;
} else {
 lean::dec_ref(x_910);
 x_917 = lean::box(0);
}
if (lean::is_scalar(x_912)) {
 x_918 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_918 = x_912;
}
lean::cnstr_set(x_918, 0, x_904);
lean::cnstr_set(x_918, 1, x_911);
lean::cnstr_set(x_2, 1, x_915);
lean::cnstr_set(x_2, 0, x_918);
if (lean::is_scalar(x_917)) {
 x_919 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_919 = x_917;
}
lean::cnstr_set(x_919, 0, x_913);
lean::cnstr_set(x_919, 1, x_914);
lean::cnstr_set(x_919, 2, x_2);
lean::cnstr_set(x_919, 3, x_916);
x_2 = x_542;
x_3 = x_919;
goto _start;
}
}
else
{
obj* x_921; obj* x_922; obj* x_923; 
x_921 = lean::cnstr_get(x_902, 0);
lean::inc(x_921);
if (lean::is_exclusive(x_902)) {
 lean::cnstr_release(x_902, 0);
 x_922 = x_902;
} else {
 lean::dec_ref(x_902);
 x_922 = lean::box(0);
}
x_923 = lean::cnstr_get(x_921, 1);
lean::inc(x_923);
lean::dec(x_921);
switch (lean::obj_tag(x_923)) {
case 0:
{
obj* x_924; obj* x_925; obj* x_926; 
lean::dec(x_923);
lean::dec(x_922);
x_924 = lean::cnstr_get(x_548, 1);
lean::inc(x_924);
lean::dec(x_548);
x_925 = lean::cnstr_get(x_901, 0);
lean::inc(x_925);
lean::dec(x_901);
x_926 = l___private_init_lean_expander_1__popStxArg(x_924, x_4);
if (lean::obj_tag(x_926) == 0)
{
obj* x_927; obj* x_928; obj* x_929; 
lean::dec(x_925);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_927 = lean::cnstr_get(x_926, 0);
lean::inc(x_927);
if (lean::is_exclusive(x_926)) {
 lean::cnstr_release(x_926, 0);
 x_928 = x_926;
} else {
 lean::dec_ref(x_926);
 x_928 = lean::box(0);
}
if (lean::is_scalar(x_928)) {
 x_929 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_929 = x_928;
}
lean::cnstr_set(x_929, 0, x_927);
return x_929;
}
else
{
obj* x_930; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; 
x_930 = lean::cnstr_get(x_926, 0);
lean::inc(x_930);
lean::dec(x_926);
x_931 = lean::cnstr_get(x_930, 1);
lean::inc(x_931);
x_932 = lean::cnstr_get(x_930, 0);
lean::inc(x_932);
if (lean::is_exclusive(x_930)) {
 lean::cnstr_release(x_930, 0);
 lean::cnstr_release(x_930, 1);
 x_933 = x_930;
} else {
 lean::dec_ref(x_930);
 x_933 = lean::box(0);
}
x_934 = lean::cnstr_get(x_931, 0);
lean::inc(x_934);
x_935 = lean::cnstr_get(x_931, 1);
lean::inc(x_935);
x_936 = lean::cnstr_get(x_931, 2);
lean::inc(x_936);
x_937 = lean::cnstr_get(x_931, 3);
lean::inc(x_937);
if (lean::is_exclusive(x_931)) {
 lean::cnstr_release(x_931, 0);
 lean::cnstr_release(x_931, 1);
 lean::cnstr_release(x_931, 2);
 lean::cnstr_release(x_931, 3);
 x_938 = x_931;
} else {
 lean::dec_ref(x_931);
 x_938 = lean::box(0);
}
if (lean::is_scalar(x_933)) {
 x_939 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_939 = x_933;
}
lean::cnstr_set(x_939, 0, x_925);
lean::cnstr_set(x_939, 1, x_932);
lean::cnstr_set(x_2, 1, x_936);
lean::cnstr_set(x_2, 0, x_939);
if (lean::is_scalar(x_938)) {
 x_940 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_940 = x_938;
}
lean::cnstr_set(x_940, 0, x_934);
lean::cnstr_set(x_940, 1, x_935);
lean::cnstr_set(x_940, 2, x_2);
lean::cnstr_set(x_940, 3, x_937);
x_2 = x_542;
x_3 = x_940;
goto _start;
}
}
case 2:
{
obj* x_942; obj* x_943; obj* x_944; obj* x_945; 
x_942 = lean::cnstr_get(x_548, 1);
lean::inc(x_942);
lean::dec(x_548);
x_943 = lean::cnstr_get(x_901, 0);
lean::inc(x_943);
lean::dec(x_901);
x_944 = lean::cnstr_get(x_923, 0);
lean::inc(x_944);
lean::dec(x_923);
x_945 = l___private_init_lean_expander_1__popStxArg(x_942, x_4);
if (lean::obj_tag(x_945) == 0)
{
obj* x_946; obj* x_947; obj* x_948; 
lean::dec(x_944);
lean::dec(x_943);
lean::dec(x_922);
lean::free_heap_obj(x_2);
lean::dec(x_542);
lean::dec(x_1);
x_946 = lean::cnstr_get(x_945, 0);
lean::inc(x_946);
if (lean::is_exclusive(x_945)) {
 lean::cnstr_release(x_945, 0);
 x_947 = x_945;
} else {
 lean::dec_ref(x_945);
 x_947 = lean::box(0);
}
if (lean::is_scalar(x_947)) {
 x_948 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_948 = x_947;
}
lean::cnstr_set(x_948, 0, x_946);
return x_948;
}
else
{
obj* x_949; obj* x_950; obj* x_951; 
x_949 = lean::cnstr_get(x_945, 0);
lean::inc(x_949);
lean::dec(x_945);
x_950 = lean::cnstr_get(x_949, 1);
lean::inc(x_950);
x_951 = lean::cnstr_get(x_950, 3);
lean::inc(x_951);
if (lean::obj_tag(x_951) == 0)
{
obj* x_952; obj* x_953; obj* x_954; 
lean::dec(x_949);
lean::dec(x_944);
lean::dec(x_943);
lean::free_heap_obj(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_922)) {
 x_952 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_952 = x_922;
}
lean::cnstr_set(x_952, 0, x_1);
x_953 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_954 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_952, x_953, x_950, x_4);
lean::dec(x_950);
lean::dec(x_952);
if (lean::obj_tag(x_954) == 0)
{
obj* x_955; obj* x_956; obj* x_957; 
lean::dec(x_542);
lean::dec(x_1);
x_955 = lean::cnstr_get(x_954, 0);
lean::inc(x_955);
if (lean::is_exclusive(x_954)) {
 lean::cnstr_release(x_954, 0);
 x_956 = x_954;
} else {
 lean::dec_ref(x_954);
 x_956 = lean::box(0);
}
if (lean::is_scalar(x_956)) {
 x_957 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_957 = x_956;
}
lean::cnstr_set(x_957, 0, x_955);
return x_957;
}
else
{
obj* x_958; obj* x_959; 
x_958 = lean::cnstr_get(x_954, 0);
lean::inc(x_958);
lean::dec(x_954);
x_959 = lean::cnstr_get(x_958, 1);
lean::inc(x_959);
lean::dec(x_958);
x_2 = x_542;
x_3 = x_959;
goto _start;
}
}
else
{
obj* x_961; obj* x_962; obj* x_963; obj* x_964; obj* x_965; obj* x_966; obj* x_967; obj* x_968; obj* x_969; obj* x_970; obj* x_971; obj* x_972; obj* x_973; obj* x_974; obj* x_975; obj* x_976; obj* x_977; obj* x_978; obj* x_979; obj* x_980; obj* x_981; obj* x_982; obj* x_983; obj* x_984; obj* x_985; obj* x_986; obj* x_987; obj* x_988; obj* x_989; 
lean::dec(x_922);
x_961 = lean::cnstr_get(x_949, 0);
lean::inc(x_961);
if (lean::is_exclusive(x_949)) {
 lean::cnstr_release(x_949, 0);
 lean::cnstr_release(x_949, 1);
 x_962 = x_949;
} else {
 lean::dec_ref(x_949);
 x_962 = lean::box(0);
}
x_963 = lean::cnstr_get(x_950, 0);
lean::inc(x_963);
x_964 = lean::cnstr_get(x_950, 1);
lean::inc(x_964);
x_965 = lean::cnstr_get(x_950, 2);
lean::inc(x_965);
if (lean::is_exclusive(x_950)) {
 lean::cnstr_release(x_950, 0);
 lean::cnstr_release(x_950, 1);
 lean::cnstr_release(x_950, 2);
 lean::cnstr_release(x_950, 3);
 x_966 = x_950;
} else {
 lean::dec_ref(x_950);
 x_966 = lean::box(0);
}
x_967 = lean::cnstr_get(x_951, 0);
lean::inc(x_967);
x_968 = l_Lean_Parser_Term_lambda_HasView;
x_969 = lean::cnstr_get(x_968, 1);
lean::inc(x_969);
x_970 = lean::box(0);
x_971 = lean::cnstr_get(x_944, 3);
lean::inc(x_971);
x_972 = lean::box(0);
lean::cnstr_set(x_2, 1, x_972);
lean::cnstr_set(x_2, 0, x_971);
x_973 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_2);
x_974 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_974, 0, x_973);
lean::cnstr_set(x_974, 1, x_970);
x_975 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_975, 0, x_974);
x_976 = lean::cnstr_get(x_944, 5);
lean::inc(x_976);
lean::dec(x_944);
x_977 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_978 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_979 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_979, 0, x_977);
lean::cnstr_set(x_979, 1, x_975);
lean::cnstr_set(x_979, 2, x_978);
lean::cnstr_set(x_979, 3, x_976);
lean::inc(x_969);
x_980 = lean::apply_1(x_969, x_979);
x_981 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_981, 0, x_977);
lean::cnstr_set(x_981, 1, x_967);
lean::cnstr_set(x_981, 2, x_978);
lean::cnstr_set(x_981, 3, x_961);
x_982 = lean::apply_1(x_969, x_981);
x_983 = l_Lean_Parser_Term_app_HasView;
x_984 = lean::cnstr_get(x_983, 1);
lean::inc(x_984);
x_985 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_985, 0, x_980);
lean::cnstr_set(x_985, 1, x_982);
x_986 = lean::apply_1(x_984, x_985);
if (lean::is_scalar(x_962)) {
 x_987 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_987 = x_962;
}
lean::cnstr_set(x_987, 0, x_943);
lean::cnstr_set(x_987, 1, x_986);
x_988 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_988, 0, x_987);
lean::cnstr_set(x_988, 1, x_965);
if (lean::is_scalar(x_966)) {
 x_989 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_989 = x_966;
}
lean::cnstr_set(x_989, 0, x_963);
lean::cnstr_set(x_989, 1, x_964);
lean::cnstr_set(x_989, 2, x_988);
lean::cnstr_set(x_989, 3, x_951);
x_2 = x_542;
x_3 = x_989;
goto _start;
}
}
}
default: 
{
obj* x_991; obj* x_992; obj* x_993; obj* x_994; 
lean::dec(x_923);
lean::dec(x_901);
lean::free_heap_obj(x_2);
x_991 = lean::cnstr_get(x_548, 1);
lean::inc(x_991);
lean::dec(x_548);
lean::inc(x_1);
if (lean::is_scalar(x_922)) {
 x_992 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_992 = x_922;
}
lean::cnstr_set(x_992, 0, x_1);
x_993 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_994 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_992, x_993, x_991, x_4);
lean::dec(x_991);
lean::dec(x_992);
if (lean::obj_tag(x_994) == 0)
{
obj* x_995; obj* x_996; obj* x_997; 
lean::dec(x_542);
lean::dec(x_1);
x_995 = lean::cnstr_get(x_994, 0);
lean::inc(x_995);
if (lean::is_exclusive(x_994)) {
 lean::cnstr_release(x_994, 0);
 x_996 = x_994;
} else {
 lean::dec_ref(x_994);
 x_996 = lean::box(0);
}
if (lean::is_scalar(x_996)) {
 x_997 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_997 = x_996;
}
lean::cnstr_set(x_997, 0, x_995);
return x_997;
}
else
{
obj* x_998; obj* x_999; 
x_998 = lean::cnstr_get(x_994, 0);
lean::inc(x_998);
lean::dec(x_994);
x_999 = lean::cnstr_get(x_998, 1);
lean::inc(x_999);
lean::dec(x_998);
x_2 = x_542;
x_3 = x_999;
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
else
{
obj* x_1001; obj* x_1002; 
x_1001 = lean::cnstr_get(x_2, 1);
lean::inc(x_1001);
lean::dec(x_2);
x_1002 = l___private_init_lean_expander_1__popStxArg(x_3, x_4);
if (lean::obj_tag(x_1002) == 0)
{
obj* x_1003; obj* x_1004; obj* x_1005; 
lean::dec(x_1001);
lean::dec(x_8);
lean::dec(x_1);
x_1003 = lean::cnstr_get(x_1002, 0);
lean::inc(x_1003);
if (lean::is_exclusive(x_1002)) {
 lean::cnstr_release(x_1002, 0);
 x_1004 = x_1002;
} else {
 lean::dec_ref(x_1002);
 x_1004 = lean::box(0);
}
if (lean::is_scalar(x_1004)) {
 x_1005 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1005 = x_1004;
}
lean::cnstr_set(x_1005, 0, x_1003);
return x_1005;
}
else
{
obj* x_1006; obj* x_1007; 
x_1006 = lean::cnstr_get(x_1002, 0);
lean::inc(x_1006);
lean::dec(x_1002);
x_1007 = lean::cnstr_get(x_8, 1);
lean::inc(x_1007);
lean::dec(x_8);
if (lean::obj_tag(x_1007) == 0)
{
obj* x_1008; 
x_1008 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1008);
lean::dec(x_1006);
x_2 = x_1001;
x_3 = x_1008;
goto _start;
}
else
{
obj* x_1010; obj* x_1011; 
x_1010 = lean::cnstr_get(x_1007, 0);
lean::inc(x_1010);
if (lean::is_exclusive(x_1007)) {
 lean::cnstr_release(x_1007, 0);
 x_1011 = x_1007;
} else {
 lean::dec_ref(x_1007);
 x_1011 = lean::box(0);
}
switch (lean::obj_tag(x_1010)) {
case 0:
{
obj* x_1012; obj* x_1013; 
lean::dec(x_1010);
x_1012 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1012);
lean::dec(x_1006);
x_1013 = l___private_init_lean_expander_1__popStxArg(x_1012, x_4);
if (lean::obj_tag(x_1013) == 0)
{
obj* x_1014; obj* x_1015; obj* x_1016; 
lean::dec(x_1011);
lean::dec(x_1001);
lean::dec(x_1);
x_1014 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1014);
if (lean::is_exclusive(x_1013)) {
 lean::cnstr_release(x_1013, 0);
 x_1015 = x_1013;
} else {
 lean::dec_ref(x_1013);
 x_1015 = lean::box(0);
}
if (lean::is_scalar(x_1015)) {
 x_1016 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1016 = x_1015;
}
lean::cnstr_set(x_1016, 0, x_1014);
return x_1016;
}
else
{
obj* x_1017; obj* x_1018; obj* x_1019; obj* x_1020; obj* x_1021; obj* x_1022; obj* x_1023; obj* x_1024; obj* x_1025; obj* x_1026; obj* x_1027; obj* x_1028; obj* x_1029; obj* x_1030; obj* x_1031; obj* x_1032; obj* x_1033; 
x_1017 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1017);
lean::dec(x_1013);
x_1018 = lean::cnstr_get(x_1017, 1);
lean::inc(x_1018);
x_1019 = lean::cnstr_get(x_1017, 0);
lean::inc(x_1019);
lean::dec(x_1017);
x_1020 = lean::cnstr_get(x_1018, 0);
lean::inc(x_1020);
x_1021 = lean::cnstr_get(x_1018, 1);
lean::inc(x_1021);
x_1022 = lean::cnstr_get(x_1018, 2);
lean::inc(x_1022);
if (lean::is_exclusive(x_1018)) {
 lean::cnstr_release(x_1018, 0);
 lean::cnstr_release(x_1018, 1);
 lean::cnstr_release(x_1018, 2);
 lean::cnstr_release(x_1018, 3);
 x_1023 = x_1018;
} else {
 lean::dec_ref(x_1018);
 x_1023 = lean::box(0);
}
x_1024 = l_Lean_Parser_Term_binderIdent_HasView;
x_1025 = lean::cnstr_get(x_1024, 0);
lean::inc(x_1025);
x_1026 = lean::apply_1(x_1025, x_1019);
x_1027 = lean::box(0);
x_1028 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1028, 0, x_1026);
lean::cnstr_set(x_1028, 1, x_1027);
x_1029 = lean::box(0);
x_1030 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1030, 0, x_1028);
lean::cnstr_set(x_1030, 1, x_1029);
x_1031 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1031, 0, x_1030);
if (lean::is_scalar(x_1011)) {
 x_1032 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1032 = x_1011;
}
lean::cnstr_set(x_1032, 0, x_1031);
if (lean::is_scalar(x_1023)) {
 x_1033 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1033 = x_1023;
}
lean::cnstr_set(x_1033, 0, x_1020);
lean::cnstr_set(x_1033, 1, x_1021);
lean::cnstr_set(x_1033, 2, x_1022);
lean::cnstr_set(x_1033, 3, x_1032);
x_2 = x_1001;
x_3 = x_1033;
goto _start;
}
}
case 1:
{
obj* x_1035; obj* x_1036; 
lean::dec(x_1010);
x_1035 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1035);
lean::dec(x_1006);
x_1036 = l___private_init_lean_expander_1__popStxArg(x_1035, x_4);
if (lean::obj_tag(x_1036) == 0)
{
obj* x_1037; obj* x_1038; obj* x_1039; 
lean::dec(x_1011);
lean::dec(x_1001);
lean::dec(x_1);
x_1037 = lean::cnstr_get(x_1036, 0);
lean::inc(x_1037);
if (lean::is_exclusive(x_1036)) {
 lean::cnstr_release(x_1036, 0);
 x_1038 = x_1036;
} else {
 lean::dec_ref(x_1036);
 x_1038 = lean::box(0);
}
if (lean::is_scalar(x_1038)) {
 x_1039 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1039 = x_1038;
}
lean::cnstr_set(x_1039, 0, x_1037);
return x_1039;
}
else
{
obj* x_1040; obj* x_1041; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; obj* x_1046; obj* x_1047; obj* x_1048; obj* x_1049; obj* x_1050; obj* x_1051; 
x_1040 = lean::cnstr_get(x_1036, 0);
lean::inc(x_1040);
lean::dec(x_1036);
x_1041 = lean::cnstr_get(x_1040, 1);
lean::inc(x_1041);
x_1042 = lean::cnstr_get(x_1040, 0);
lean::inc(x_1042);
lean::dec(x_1040);
x_1043 = lean::cnstr_get(x_1041, 0);
lean::inc(x_1043);
x_1044 = lean::cnstr_get(x_1041, 1);
lean::inc(x_1044);
x_1045 = lean::cnstr_get(x_1041, 2);
lean::inc(x_1045);
if (lean::is_exclusive(x_1041)) {
 lean::cnstr_release(x_1041, 0);
 lean::cnstr_release(x_1041, 1);
 lean::cnstr_release(x_1041, 2);
 lean::cnstr_release(x_1041, 3);
 x_1046 = x_1041;
} else {
 lean::dec_ref(x_1041);
 x_1046 = lean::box(0);
}
x_1047 = l_Lean_Parser_Term_binders_HasView;
x_1048 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1048);
x_1049 = lean::apply_1(x_1048, x_1042);
if (lean::is_scalar(x_1011)) {
 x_1050 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1050 = x_1011;
}
lean::cnstr_set(x_1050, 0, x_1049);
if (lean::is_scalar(x_1046)) {
 x_1051 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1051 = x_1046;
}
lean::cnstr_set(x_1051, 0, x_1043);
lean::cnstr_set(x_1051, 1, x_1044);
lean::cnstr_set(x_1051, 2, x_1045);
lean::cnstr_set(x_1051, 3, x_1050);
x_2 = x_1001;
x_3 = x_1051;
goto _start;
}
}
default: 
{
obj* x_1053; obj* x_1054; 
lean::dec(x_1011);
x_1053 = lean::cnstr_get(x_1010, 0);
lean::inc(x_1053);
lean::dec(x_1010);
x_1054 = lean::cnstr_get(x_1053, 1);
lean::inc(x_1054);
if (lean::obj_tag(x_1054) == 0)
{
obj* x_1055; obj* x_1056; obj* x_1057; 
x_1055 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1055);
lean::dec(x_1006);
x_1056 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1056);
lean::dec(x_1053);
x_1057 = l___private_init_lean_expander_1__popStxArg(x_1055, x_4);
if (lean::obj_tag(x_1057) == 0)
{
obj* x_1058; obj* x_1059; obj* x_1060; 
lean::dec(x_1056);
lean::dec(x_1001);
lean::dec(x_1);
x_1058 = lean::cnstr_get(x_1057, 0);
lean::inc(x_1058);
if (lean::is_exclusive(x_1057)) {
 lean::cnstr_release(x_1057, 0);
 x_1059 = x_1057;
} else {
 lean::dec_ref(x_1057);
 x_1059 = lean::box(0);
}
if (lean::is_scalar(x_1059)) {
 x_1060 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1060 = x_1059;
}
lean::cnstr_set(x_1060, 0, x_1058);
return x_1060;
}
else
{
obj* x_1061; obj* x_1062; obj* x_1063; obj* x_1064; obj* x_1065; obj* x_1066; obj* x_1067; obj* x_1068; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; 
x_1061 = lean::cnstr_get(x_1057, 0);
lean::inc(x_1061);
lean::dec(x_1057);
x_1062 = lean::cnstr_get(x_1061, 1);
lean::inc(x_1062);
x_1063 = lean::cnstr_get(x_1061, 0);
lean::inc(x_1063);
if (lean::is_exclusive(x_1061)) {
 lean::cnstr_release(x_1061, 0);
 lean::cnstr_release(x_1061, 1);
 x_1064 = x_1061;
} else {
 lean::dec_ref(x_1061);
 x_1064 = lean::box(0);
}
x_1065 = lean::cnstr_get(x_1062, 0);
lean::inc(x_1065);
x_1066 = lean::cnstr_get(x_1062, 1);
lean::inc(x_1066);
x_1067 = lean::cnstr_get(x_1062, 2);
lean::inc(x_1067);
x_1068 = lean::cnstr_get(x_1062, 3);
lean::inc(x_1068);
if (lean::is_exclusive(x_1062)) {
 lean::cnstr_release(x_1062, 0);
 lean::cnstr_release(x_1062, 1);
 lean::cnstr_release(x_1062, 2);
 lean::cnstr_release(x_1062, 3);
 x_1069 = x_1062;
} else {
 lean::dec_ref(x_1062);
 x_1069 = lean::box(0);
}
if (lean::is_scalar(x_1064)) {
 x_1070 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1070 = x_1064;
}
lean::cnstr_set(x_1070, 0, x_1056);
lean::cnstr_set(x_1070, 1, x_1063);
x_1071 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1071, 0, x_1070);
lean::cnstr_set(x_1071, 1, x_1067);
if (lean::is_scalar(x_1069)) {
 x_1072 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1072 = x_1069;
}
lean::cnstr_set(x_1072, 0, x_1065);
lean::cnstr_set(x_1072, 1, x_1066);
lean::cnstr_set(x_1072, 2, x_1071);
lean::cnstr_set(x_1072, 3, x_1068);
x_2 = x_1001;
x_3 = x_1072;
goto _start;
}
}
else
{
obj* x_1074; obj* x_1075; obj* x_1076; 
x_1074 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1074);
if (lean::is_exclusive(x_1054)) {
 lean::cnstr_release(x_1054, 0);
 x_1075 = x_1054;
} else {
 lean::dec_ref(x_1054);
 x_1075 = lean::box(0);
}
x_1076 = lean::cnstr_get(x_1074, 1);
lean::inc(x_1076);
lean::dec(x_1074);
switch (lean::obj_tag(x_1076)) {
case 0:
{
obj* x_1077; obj* x_1078; obj* x_1079; 
lean::dec(x_1076);
lean::dec(x_1075);
x_1077 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1077);
lean::dec(x_1006);
x_1078 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1078);
lean::dec(x_1053);
x_1079 = l___private_init_lean_expander_1__popStxArg(x_1077, x_4);
if (lean::obj_tag(x_1079) == 0)
{
obj* x_1080; obj* x_1081; obj* x_1082; 
lean::dec(x_1078);
lean::dec(x_1001);
lean::dec(x_1);
x_1080 = lean::cnstr_get(x_1079, 0);
lean::inc(x_1080);
if (lean::is_exclusive(x_1079)) {
 lean::cnstr_release(x_1079, 0);
 x_1081 = x_1079;
} else {
 lean::dec_ref(x_1079);
 x_1081 = lean::box(0);
}
if (lean::is_scalar(x_1081)) {
 x_1082 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1082 = x_1081;
}
lean::cnstr_set(x_1082, 0, x_1080);
return x_1082;
}
else
{
obj* x_1083; obj* x_1084; obj* x_1085; obj* x_1086; obj* x_1087; obj* x_1088; obj* x_1089; obj* x_1090; obj* x_1091; obj* x_1092; obj* x_1093; obj* x_1094; 
x_1083 = lean::cnstr_get(x_1079, 0);
lean::inc(x_1083);
lean::dec(x_1079);
x_1084 = lean::cnstr_get(x_1083, 1);
lean::inc(x_1084);
x_1085 = lean::cnstr_get(x_1083, 0);
lean::inc(x_1085);
if (lean::is_exclusive(x_1083)) {
 lean::cnstr_release(x_1083, 0);
 lean::cnstr_release(x_1083, 1);
 x_1086 = x_1083;
} else {
 lean::dec_ref(x_1083);
 x_1086 = lean::box(0);
}
x_1087 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1087);
x_1088 = lean::cnstr_get(x_1084, 1);
lean::inc(x_1088);
x_1089 = lean::cnstr_get(x_1084, 2);
lean::inc(x_1089);
x_1090 = lean::cnstr_get(x_1084, 3);
lean::inc(x_1090);
if (lean::is_exclusive(x_1084)) {
 lean::cnstr_release(x_1084, 0);
 lean::cnstr_release(x_1084, 1);
 lean::cnstr_release(x_1084, 2);
 lean::cnstr_release(x_1084, 3);
 x_1091 = x_1084;
} else {
 lean::dec_ref(x_1084);
 x_1091 = lean::box(0);
}
if (lean::is_scalar(x_1086)) {
 x_1092 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1092 = x_1086;
}
lean::cnstr_set(x_1092, 0, x_1078);
lean::cnstr_set(x_1092, 1, x_1085);
x_1093 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1093, 0, x_1092);
lean::cnstr_set(x_1093, 1, x_1089);
if (lean::is_scalar(x_1091)) {
 x_1094 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1094 = x_1091;
}
lean::cnstr_set(x_1094, 0, x_1087);
lean::cnstr_set(x_1094, 1, x_1088);
lean::cnstr_set(x_1094, 2, x_1093);
lean::cnstr_set(x_1094, 3, x_1090);
x_2 = x_1001;
x_3 = x_1094;
goto _start;
}
}
case 2:
{
obj* x_1096; obj* x_1097; obj* x_1098; obj* x_1099; 
x_1096 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1096);
lean::dec(x_1006);
x_1097 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1097);
lean::dec(x_1053);
x_1098 = lean::cnstr_get(x_1076, 0);
lean::inc(x_1098);
lean::dec(x_1076);
x_1099 = l___private_init_lean_expander_1__popStxArg(x_1096, x_4);
if (lean::obj_tag(x_1099) == 0)
{
obj* x_1100; obj* x_1101; obj* x_1102; 
lean::dec(x_1098);
lean::dec(x_1097);
lean::dec(x_1075);
lean::dec(x_1001);
lean::dec(x_1);
x_1100 = lean::cnstr_get(x_1099, 0);
lean::inc(x_1100);
if (lean::is_exclusive(x_1099)) {
 lean::cnstr_release(x_1099, 0);
 x_1101 = x_1099;
} else {
 lean::dec_ref(x_1099);
 x_1101 = lean::box(0);
}
if (lean::is_scalar(x_1101)) {
 x_1102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1102 = x_1101;
}
lean::cnstr_set(x_1102, 0, x_1100);
return x_1102;
}
else
{
obj* x_1103; obj* x_1104; obj* x_1105; 
x_1103 = lean::cnstr_get(x_1099, 0);
lean::inc(x_1103);
lean::dec(x_1099);
x_1104 = lean::cnstr_get(x_1103, 1);
lean::inc(x_1104);
x_1105 = lean::cnstr_get(x_1104, 3);
lean::inc(x_1105);
if (lean::obj_tag(x_1105) == 0)
{
obj* x_1106; obj* x_1107; obj* x_1108; 
lean::dec(x_1103);
lean::dec(x_1098);
lean::dec(x_1097);
lean::inc(x_1);
if (lean::is_scalar(x_1075)) {
 x_1106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1106 = x_1075;
}
lean::cnstr_set(x_1106, 0, x_1);
x_1107 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_1108 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_1106, x_1107, x_1104, x_4);
lean::dec(x_1104);
lean::dec(x_1106);
if (lean::obj_tag(x_1108) == 0)
{
obj* x_1109; obj* x_1110; obj* x_1111; 
lean::dec(x_1001);
lean::dec(x_1);
x_1109 = lean::cnstr_get(x_1108, 0);
lean::inc(x_1109);
if (lean::is_exclusive(x_1108)) {
 lean::cnstr_release(x_1108, 0);
 x_1110 = x_1108;
} else {
 lean::dec_ref(x_1108);
 x_1110 = lean::box(0);
}
if (lean::is_scalar(x_1110)) {
 x_1111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1111 = x_1110;
}
lean::cnstr_set(x_1111, 0, x_1109);
return x_1111;
}
else
{
obj* x_1112; obj* x_1113; 
x_1112 = lean::cnstr_get(x_1108, 0);
lean::inc(x_1112);
lean::dec(x_1108);
x_1113 = lean::cnstr_get(x_1112, 1);
lean::inc(x_1113);
lean::dec(x_1112);
x_2 = x_1001;
x_3 = x_1113;
goto _start;
}
}
else
{
obj* x_1115; obj* x_1116; obj* x_1117; obj* x_1118; obj* x_1119; obj* x_1120; obj* x_1121; obj* x_1122; obj* x_1123; obj* x_1124; obj* x_1125; obj* x_1126; obj* x_1127; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; obj* x_1132; obj* x_1133; obj* x_1134; obj* x_1135; obj* x_1136; obj* x_1137; obj* x_1138; obj* x_1139; obj* x_1140; obj* x_1141; obj* x_1142; obj* x_1143; obj* x_1144; 
lean::dec(x_1075);
x_1115 = lean::cnstr_get(x_1103, 0);
lean::inc(x_1115);
if (lean::is_exclusive(x_1103)) {
 lean::cnstr_release(x_1103, 0);
 lean::cnstr_release(x_1103, 1);
 x_1116 = x_1103;
} else {
 lean::dec_ref(x_1103);
 x_1116 = lean::box(0);
}
x_1117 = lean::cnstr_get(x_1104, 0);
lean::inc(x_1117);
x_1118 = lean::cnstr_get(x_1104, 1);
lean::inc(x_1118);
x_1119 = lean::cnstr_get(x_1104, 2);
lean::inc(x_1119);
if (lean::is_exclusive(x_1104)) {
 lean::cnstr_release(x_1104, 0);
 lean::cnstr_release(x_1104, 1);
 lean::cnstr_release(x_1104, 2);
 lean::cnstr_release(x_1104, 3);
 x_1120 = x_1104;
} else {
 lean::dec_ref(x_1104);
 x_1120 = lean::box(0);
}
x_1121 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1121);
x_1122 = l_Lean_Parser_Term_lambda_HasView;
x_1123 = lean::cnstr_get(x_1122, 1);
lean::inc(x_1123);
x_1124 = lean::box(0);
x_1125 = lean::cnstr_get(x_1098, 3);
lean::inc(x_1125);
x_1126 = lean::box(0);
x_1127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1127, 0, x_1125);
lean::cnstr_set(x_1127, 1, x_1126);
x_1128 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__3(x_1127);
x_1129 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1129, 0, x_1128);
lean::cnstr_set(x_1129, 1, x_1124);
x_1130 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1130, 0, x_1129);
x_1131 = lean::cnstr_get(x_1098, 5);
lean::inc(x_1131);
lean::dec(x_1098);
x_1132 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_1133 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_1134 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_1134, 0, x_1132);
lean::cnstr_set(x_1134, 1, x_1130);
lean::cnstr_set(x_1134, 2, x_1133);
lean::cnstr_set(x_1134, 3, x_1131);
lean::inc(x_1123);
x_1135 = lean::apply_1(x_1123, x_1134);
x_1136 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_1136, 0, x_1132);
lean::cnstr_set(x_1136, 1, x_1121);
lean::cnstr_set(x_1136, 2, x_1133);
lean::cnstr_set(x_1136, 3, x_1115);
x_1137 = lean::apply_1(x_1123, x_1136);
x_1138 = l_Lean_Parser_Term_app_HasView;
x_1139 = lean::cnstr_get(x_1138, 1);
lean::inc(x_1139);
x_1140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1140, 0, x_1135);
lean::cnstr_set(x_1140, 1, x_1137);
x_1141 = lean::apply_1(x_1139, x_1140);
if (lean::is_scalar(x_1116)) {
 x_1142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1142 = x_1116;
}
lean::cnstr_set(x_1142, 0, x_1097);
lean::cnstr_set(x_1142, 1, x_1141);
x_1143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1143, 0, x_1142);
lean::cnstr_set(x_1143, 1, x_1119);
if (lean::is_scalar(x_1120)) {
 x_1144 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_1144 = x_1120;
}
lean::cnstr_set(x_1144, 0, x_1117);
lean::cnstr_set(x_1144, 1, x_1118);
lean::cnstr_set(x_1144, 2, x_1143);
lean::cnstr_set(x_1144, 3, x_1105);
x_2 = x_1001;
x_3 = x_1144;
goto _start;
}
}
}
default: 
{
obj* x_1146; obj* x_1147; obj* x_1148; obj* x_1149; 
lean::dec(x_1076);
lean::dec(x_1053);
x_1146 = lean::cnstr_get(x_1006, 1);
lean::inc(x_1146);
lean::dec(x_1006);
lean::inc(x_1);
if (lean::is_scalar(x_1075)) {
 x_1147 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1147 = x_1075;
}
lean::cnstr_set(x_1147, 0, x_1);
x_1148 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__1;
x_1149 = l_Lean_Expander_error___at___private_init_lean_expander_1__popStxArg___spec__1___rarg(x_1147, x_1148, x_1146, x_4);
lean::dec(x_1146);
lean::dec(x_1147);
if (lean::obj_tag(x_1149) == 0)
{
obj* x_1150; obj* x_1151; obj* x_1152; 
lean::dec(x_1001);
lean::dec(x_1);
x_1150 = lean::cnstr_get(x_1149, 0);
lean::inc(x_1150);
if (lean::is_exclusive(x_1149)) {
 lean::cnstr_release(x_1149, 0);
 x_1151 = x_1149;
} else {
 lean::dec_ref(x_1149);
 x_1151 = lean::box(0);
}
if (lean::is_scalar(x_1151)) {
 x_1152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1152 = x_1151;
}
lean::cnstr_set(x_1152, 0, x_1150);
return x_1152;
}
else
{
obj* x_1153; obj* x_1154; 
x_1153 = lean::cnstr_get(x_1149, 0);
lean::inc(x_1153);
lean::dec(x_1149);
x_1154 = lean::cnstr_get(x_1153, 1);
lean::inc(x_1154);
lean::dec(x_1153);
x_2 = x_1001;
x_3 = x_1154;
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
}
obj* l_Lean_Expander_mkNotationTransformer___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_identUnivs;
x_4 = l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_8, 2);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(x_9, x_1);
lean::dec(x_9);
return x_10;
}
else
{
obj* x_11; 
lean::dec(x_7);
lean::dec(x_6);
x_11 = lean::box(0);
return x_11;
}
}
}
}
obj* l_Lean_Expander_mkNotationTransformer(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
x_6 = l___private_init_lean_expander_1__popStxArg___closed__1;
x_7 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_5, x_6, x_3);
lean::dec(x_5);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::box(0);
x_12 = lean::box(0);
lean::inc(x_2);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_14, 2);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
lean::dec(x_15);
x_18 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(x_2, x_17, x_13, x_3);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
lean::dec(x_14);
lean::free_heap_obj(x_4);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
lean::dec(x_18);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_18);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
x_25 = lean::cnstr_get(x_24, 2);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::cnstr_get(x_14, 4);
lean::inc(x_28);
lean::dec(x_14);
x_29 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_27, x_28);
lean::cnstr_set(x_4, 0, x_29);
lean::cnstr_set(x_18, 0, x_4);
return x_18;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_18, 0);
lean::inc(x_30);
lean::dec(x_18);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_32 = lean::cnstr_get(x_31, 2);
lean::inc(x_32);
lean::dec(x_31);
x_33 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_34, 0, x_33);
x_35 = lean::cnstr_get(x_14, 4);
lean::inc(x_35);
lean::dec(x_14);
x_36 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_34, x_35);
lean::cnstr_set(x_4, 0, x_36);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_4);
return x_37;
}
}
}
else
{
uint8 x_38; 
lean::free_heap_obj(x_4);
x_38 = !lean::is_exclusive(x_16);
if (x_38 == 0)
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_16, 0);
x_40 = l___private_init_lean_expander_1__popStxArg(x_13, x_3);
if (lean::obj_tag(x_40) == 0)
{
uint8 x_41; 
lean::free_heap_obj(x_16);
lean::dec(x_39);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_2);
x_41 = !lean::is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_40, 0);
lean::inc(x_42);
lean::dec(x_40);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
else
{
obj* x_44; uint8 x_45; 
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
lean::dec(x_40);
x_45 = !lean::is_exclusive(x_44);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::cnstr_get(x_44, 1);
x_47 = !lean::is_exclusive(x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_44, 0);
x_49 = lean::cnstr_get(x_46, 2);
lean::cnstr_set(x_44, 1, x_48);
lean::cnstr_set(x_44, 0, x_39);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_46, 2, x_50);
x_51 = lean::cnstr_get(x_15, 1);
lean::inc(x_51);
lean::dec(x_15);
x_52 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_2, x_51, x_46, x_3);
if (lean::obj_tag(x_52) == 0)
{
uint8 x_53; 
lean::free_heap_obj(x_16);
lean::dec(x_14);
x_53 = !lean::is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_52, 0);
lean::inc(x_54);
lean::dec(x_52);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
else
{
uint8 x_56; 
x_56 = !lean::is_exclusive(x_52);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_57 = lean::cnstr_get(x_52, 0);
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
lean::dec(x_57);
x_59 = lean::cnstr_get(x_58, 2);
lean::inc(x_59);
lean::dec(x_58);
x_60 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_61, 0, x_60);
x_62 = lean::cnstr_get(x_14, 4);
lean::inc(x_62);
lean::dec(x_14);
x_63 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_61, x_62);
lean::cnstr_set(x_16, 0, x_63);
lean::cnstr_set(x_52, 0, x_16);
return x_52;
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_64 = lean::cnstr_get(x_52, 0);
lean::inc(x_64);
lean::dec(x_52);
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
lean::dec(x_64);
x_66 = lean::cnstr_get(x_65, 2);
lean::inc(x_66);
lean::dec(x_65);
x_67 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_66);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_68, 0, x_67);
x_69 = lean::cnstr_get(x_14, 4);
lean::inc(x_69);
lean::dec(x_14);
x_70 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_68, x_69);
lean::cnstr_set(x_16, 0, x_70);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_16);
return x_71;
}
}
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_72 = lean::cnstr_get(x_44, 0);
x_73 = lean::cnstr_get(x_46, 0);
x_74 = lean::cnstr_get(x_46, 1);
x_75 = lean::cnstr_get(x_46, 2);
x_76 = lean::cnstr_get(x_46, 3);
lean::inc(x_76);
lean::inc(x_75);
lean::inc(x_74);
lean::inc(x_73);
lean::dec(x_46);
lean::cnstr_set(x_44, 1, x_72);
lean::cnstr_set(x_44, 0, x_39);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_44);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_78, 0, x_73);
lean::cnstr_set(x_78, 1, x_74);
lean::cnstr_set(x_78, 2, x_77);
lean::cnstr_set(x_78, 3, x_76);
x_79 = lean::cnstr_get(x_15, 1);
lean::inc(x_79);
lean::dec(x_15);
x_80 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_2, x_79, x_78, x_3);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_82; obj* x_83; 
lean::free_heap_obj(x_16);
lean::dec(x_14);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_82 = x_80;
} else {
 lean::dec_ref(x_80);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_81);
return x_83;
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_85 = x_80;
} else {
 lean::dec_ref(x_80);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_84, 1);
lean::inc(x_86);
lean::dec(x_84);
x_87 = lean::cnstr_get(x_86, 2);
lean::inc(x_87);
lean::dec(x_86);
x_88 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_87);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_89, 0, x_88);
x_90 = lean::cnstr_get(x_14, 4);
lean::inc(x_90);
lean::dec(x_14);
x_91 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_89, x_90);
lean::cnstr_set(x_16, 0, x_91);
if (lean::is_scalar(x_85)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_85;
}
lean::cnstr_set(x_92, 0, x_16);
return x_92;
}
}
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_93 = lean::cnstr_get(x_44, 1);
x_94 = lean::cnstr_get(x_44, 0);
lean::inc(x_93);
lean::inc(x_94);
lean::dec(x_44);
x_95 = lean::cnstr_get(x_93, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_93, 2);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_93, 3);
lean::inc(x_98);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 lean::cnstr_release(x_93, 2);
 lean::cnstr_release(x_93, 3);
 x_99 = x_93;
} else {
 lean::dec_ref(x_93);
 x_99 = lean::box(0);
}
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_39);
lean::cnstr_set(x_100, 1, x_94);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
if (lean::is_scalar(x_99)) {
 x_102 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_102 = x_99;
}
lean::cnstr_set(x_102, 0, x_95);
lean::cnstr_set(x_102, 1, x_96);
lean::cnstr_set(x_102, 2, x_101);
lean::cnstr_set(x_102, 3, x_98);
x_103 = lean::cnstr_get(x_15, 1);
lean::inc(x_103);
lean::dec(x_15);
x_104 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_2, x_103, x_102, x_3);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; 
lean::free_heap_obj(x_16);
lean::dec(x_14);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 x_106 = x_104;
} else {
 lean::dec_ref(x_104);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 x_109 = x_104;
} else {
 lean::dec_ref(x_104);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
lean::dec(x_108);
x_111 = lean::cnstr_get(x_110, 2);
lean::inc(x_111);
lean::dec(x_110);
x_112 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_111);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_113, 0, x_112);
x_114 = lean::cnstr_get(x_14, 4);
lean::inc(x_114);
lean::dec(x_14);
x_115 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_113, x_114);
lean::cnstr_set(x_16, 0, x_115);
if (lean::is_scalar(x_109)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_109;
}
lean::cnstr_set(x_116, 0, x_16);
return x_116;
}
}
}
}
else
{
obj* x_117; obj* x_118; 
x_117 = lean::cnstr_get(x_16, 0);
lean::inc(x_117);
lean::dec(x_16);
x_118 = l___private_init_lean_expander_1__popStxArg(x_13, x_3);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_117);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_2);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_release(x_118, 0);
 x_120 = x_118;
} else {
 lean::dec_ref(x_118);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_119);
return x_121;
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_122 = lean::cnstr_get(x_118, 0);
lean::inc(x_122);
lean::dec(x_118);
x_123 = lean::cnstr_get(x_122, 1);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_122, 0);
lean::inc(x_124);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 lean::cnstr_release(x_122, 1);
 x_125 = x_122;
} else {
 lean::dec_ref(x_122);
 x_125 = lean::box(0);
}
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_123, 1);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_123, 2);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_123, 3);
lean::inc(x_129);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 lean::cnstr_release(x_123, 2);
 lean::cnstr_release(x_123, 3);
 x_130 = x_123;
} else {
 lean::dec_ref(x_123);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_125;
}
lean::cnstr_set(x_131, 0, x_117);
lean::cnstr_set(x_131, 1, x_124);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_128);
if (lean::is_scalar(x_130)) {
 x_133 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_133 = x_130;
}
lean::cnstr_set(x_133, 0, x_126);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_132);
lean::cnstr_set(x_133, 3, x_129);
x_134 = lean::cnstr_get(x_15, 1);
lean::inc(x_134);
lean::dec(x_15);
x_135 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_2, x_134, x_133, x_3);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_14);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_137 = x_135;
} else {
 lean::dec_ref(x_135);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_136);
return x_138;
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_139 = lean::cnstr_get(x_135, 0);
lean::inc(x_139);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_140 = x_135;
} else {
 lean::dec_ref(x_135);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_139, 1);
lean::inc(x_141);
lean::dec(x_139);
x_142 = lean::cnstr_get(x_141, 2);
lean::inc(x_142);
lean::dec(x_141);
x_143 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_142);
x_144 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_144, 0, x_143);
x_145 = lean::cnstr_get(x_14, 4);
lean::inc(x_145);
lean::dec(x_14);
x_146 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_144, x_145);
x_147 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_147, 0, x_146);
if (lean::is_scalar(x_140)) {
 x_148 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_148 = x_140;
}
lean::cnstr_set(x_148, 0, x_147);
return x_148;
}
}
}
}
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_149 = lean::cnstr_get(x_4, 0);
lean::inc(x_149);
lean::dec(x_4);
x_150 = lean::cnstr_get(x_149, 1);
lean::inc(x_150);
lean::dec(x_149);
x_151 = lean::box(0);
x_152 = lean::box(0);
lean::inc(x_2);
x_153 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_153, 0, x_2);
lean::cnstr_set(x_153, 1, x_150);
lean::cnstr_set(x_153, 2, x_151);
lean::cnstr_set(x_153, 3, x_152);
x_154 = lean::cnstr_get(x_1, 1);
lean::inc(x_154);
lean::dec(x_1);
x_155 = lean::cnstr_get(x_154, 2);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_155, 0);
lean::inc(x_156);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; 
x_157 = lean::cnstr_get(x_155, 1);
lean::inc(x_157);
lean::dec(x_155);
x_158 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(x_2, x_157, x_153, x_3);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_154);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 x_160 = x_158;
} else {
 lean::dec_ref(x_158);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_159);
return x_161;
}
else
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_162 = lean::cnstr_get(x_158, 0);
lean::inc(x_162);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 x_163 = x_158;
} else {
 lean::dec_ref(x_158);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_162, 1);
lean::inc(x_164);
lean::dec(x_162);
x_165 = lean::cnstr_get(x_164, 2);
lean::inc(x_165);
lean::dec(x_164);
x_166 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_165);
x_167 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_167, 0, x_166);
x_168 = lean::cnstr_get(x_154, 4);
lean::inc(x_168);
lean::dec(x_154);
x_169 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_167, x_168);
x_170 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
if (lean::is_scalar(x_163)) {
 x_171 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_171 = x_163;
}
lean::cnstr_set(x_171, 0, x_170);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; 
x_172 = lean::cnstr_get(x_156, 0);
lean::inc(x_172);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 x_173 = x_156;
} else {
 lean::dec_ref(x_156);
 x_173 = lean::box(0);
}
x_174 = l___private_init_lean_expander_1__popStxArg(x_153, x_3);
if (lean::obj_tag(x_174) == 0)
{
obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_173);
lean::dec(x_172);
lean::dec(x_155);
lean::dec(x_154);
lean::dec(x_2);
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 x_176 = x_174;
} else {
 lean::dec_ref(x_174);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_175);
return x_177;
}
else
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_178 = lean::cnstr_get(x_174, 0);
lean::inc(x_178);
lean::dec(x_174);
x_179 = lean::cnstr_get(x_178, 1);
lean::inc(x_179);
x_180 = lean::cnstr_get(x_178, 0);
lean::inc(x_180);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 x_181 = x_178;
} else {
 lean::dec_ref(x_178);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_179, 0);
lean::inc(x_182);
x_183 = lean::cnstr_get(x_179, 1);
lean::inc(x_183);
x_184 = lean::cnstr_get(x_179, 2);
lean::inc(x_184);
x_185 = lean::cnstr_get(x_179, 3);
lean::inc(x_185);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 lean::cnstr_release(x_179, 1);
 lean::cnstr_release(x_179, 2);
 lean::cnstr_release(x_179, 3);
 x_186 = x_179;
} else {
 lean::dec_ref(x_179);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_181;
}
lean::cnstr_set(x_187, 0, x_172);
lean::cnstr_set(x_187, 1, x_180);
x_188 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_184);
if (lean::is_scalar(x_186)) {
 x_189 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_189 = x_186;
}
lean::cnstr_set(x_189, 0, x_182);
lean::cnstr_set(x_189, 1, x_183);
lean::cnstr_set(x_189, 2, x_188);
lean::cnstr_set(x_189, 3, x_185);
x_190 = lean::cnstr_get(x_155, 1);
lean::inc(x_190);
lean::dec(x_155);
x_191 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_2, x_190, x_189, x_3);
if (lean::obj_tag(x_191) == 0)
{
obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_173);
lean::dec(x_154);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_193 = x_191;
} else {
 lean::dec_ref(x_191);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_192);
return x_194;
}
else
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_195 = lean::cnstr_get(x_191, 0);
lean::inc(x_195);
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_196 = x_191;
} else {
 lean::dec_ref(x_191);
 x_196 = lean::box(0);
}
x_197 = lean::cnstr_get(x_195, 1);
lean::inc(x_197);
lean::dec(x_195);
x_198 = lean::cnstr_get(x_197, 2);
lean::inc(x_198);
lean::dec(x_197);
x_199 = l_List_map___main___at_Lean_Expander_mkNotationTransformer___spec__5(x_198);
x_200 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mkNotationTransformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_200, 0, x_199);
x_201 = lean::cnstr_get(x_154, 4);
lean::inc(x_201);
lean::dec(x_154);
x_202 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_200, x_201);
if (lean::is_scalar(x_173)) {
 x_203 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_203 = x_173;
}
lean::cnstr_set(x_203, 0, x_202);
if (lean::is_scalar(x_196)) {
 x_204 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_204 = x_196;
}
lean::cnstr_set(x_204, 0, x_203);
return x_204;
}
}
}
}
}
}
}
obj* l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_tryView___at_Lean_Expander_mkNotationTransformer___spec__6(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_lookup___main___at_Lean_Expander_mkNotationTransformer___spec__7(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__8(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Expander_mkNotationTransformer___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_mkNotationTransformer___lambda__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Expander_mkNotationTransformer___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_mkNotationTransformer(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::box(0);
x_4 = lean::mk_string("b");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string(".");
lean::inc(x_5);
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
lean::dec(x_6);
x_8 = l_Lean_Parser_Substring_ofString(x_7);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_2);
lean::cnstr_set(x_9, 4, x_2);
return x_9;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::mk_string("a");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::box(0);
x_4 = lean::mk_string("b");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string(".");
lean::inc(x_5);
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
lean::dec(x_6);
x_8 = l_Lean_Parser_Substring_ofString(x_7);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_2);
lean::cnstr_set(x_9, 4, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(":");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("b");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("b");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
obj* _init_l_Lean_Expander_mixfixToNotationSpec___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid `infixr` declaration, given precedence must greater than zero");
return x_1;
}
}
obj* l_Lean_Expander_mixfixToNotationSpec(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_2, 3);
lean::inc(x_16);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_56; obj* x_57; 
x_56 = lean::box(0);
x_57 = lean::box(0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_58 = l_Lean_Expander_mixfixToNotationSpec___closed__5;
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_2);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_57);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
else
{
uint8 x_63; 
x_63 = !lean::is_exclusive(x_16);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_64 = lean::cnstr_get(x_16, 0);
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
lean::dec(x_64);
x_66 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
lean::cnstr_set(x_16, 0, x_68);
x_69 = l_Lean_Expander_mixfixToNotationSpec___closed__6;
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_16);
x_71 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_2);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_57);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_56);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_77 = lean::cnstr_get(x_16, 0);
lean::inc(x_77);
lean::dec(x_16);
x_78 = lean::cnstr_get(x_77, 1);
lean::inc(x_78);
lean::dec(x_77);
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_83 = l_Lean_Expander_mixfixToNotationSpec___closed__6;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
x_85 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_2);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_57);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_56);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
}
}
case 3:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_91; 
x_91 = lean::box(0);
x_4 = x_91;
goto block_15;
}
else
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_16);
if (x_92 == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; uint8 x_97; 
x_93 = lean::cnstr_get(x_16, 0);
x_94 = lean::cnstr_get(x_93, 1);
lean::inc(x_94);
x_95 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_94);
x_96 = lean::mk_nat_obj(0u);
x_97 = lean::nat_dec_eq(x_95, x_96);
if (x_97 == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_93);
x_98 = lean::mk_nat_obj(1u);
x_99 = lean::nat_sub(x_95, x_98);
lean::dec(x_95);
x_100 = l_Lean_Parser_number_View_ofNat(x_99);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
x_102 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_103 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
x_104 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_103);
lean::cnstr_set(x_16, 0, x_105);
x_4 = x_16;
goto block_15;
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_95);
x_106 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_107 = lean::cnstr_get(x_106, 1);
lean::inc(x_107);
x_108 = lean::apply_1(x_107, x_93);
lean::cnstr_set(x_16, 0, x_108);
x_109 = l_Lean_Expander_mixfixToNotationSpec___closed__7;
x_110 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_16, x_109, x_3);
lean::dec(x_16);
if (lean::obj_tag(x_110) == 0)
{
uint8 x_111; 
lean::dec(x_2);
x_111 = !lean::is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
obj* x_112; obj* x_113; 
x_112 = lean::cnstr_get(x_110, 0);
lean::inc(x_112);
lean::dec(x_110);
x_113 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_113, 0, x_112);
return x_113;
}
}
else
{
obj* x_114; 
x_114 = lean::cnstr_get(x_110, 0);
lean::inc(x_114);
lean::dec(x_110);
x_4 = x_114;
goto block_15;
}
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; uint8 x_119; 
x_115 = lean::cnstr_get(x_16, 0);
lean::inc(x_115);
lean::dec(x_16);
x_116 = lean::cnstr_get(x_115, 1);
lean::inc(x_116);
x_117 = l_Lean_Parser_command_NotationSpec_precedenceTerm_View_toNat___main(x_116);
x_118 = lean::mk_nat_obj(0u);
x_119 = lean::nat_dec_eq(x_117, x_118);
if (x_119 == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_115);
x_120 = lean::mk_nat_obj(1u);
x_121 = lean::nat_sub(x_117, x_120);
lean::dec(x_117);
x_122 = l_Lean_Parser_number_View_ofNat(x_121);
x_123 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
x_124 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_124, 0, x_123);
x_125 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_125, 0, x_124);
x_126 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_125);
x_128 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_128, 0, x_127);
x_4 = x_128;
goto block_15;
}
else
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_117);
x_129 = l_Lean_Parser_command_NotationSpec_precedence_HasView;
x_130 = lean::cnstr_get(x_129, 1);
lean::inc(x_130);
x_131 = lean::apply_1(x_130, x_115);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
x_133 = l_Lean_Expander_mixfixToNotationSpec___closed__7;
x_134 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_132, x_133, x_3);
lean::dec(x_132);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_2);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_136 = x_134;
} else {
 lean::dec_ref(x_134);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_135);
return x_137;
}
else
{
obj* x_138; 
x_138 = lean::cnstr_get(x_134, 0);
lean::inc(x_138);
lean::dec(x_134);
x_4 = x_138;
goto block_15;
}
}
}
}
}
case 4:
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_16);
x_139 = lean::box(0);
x_140 = lean::box(0);
x_141 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_141, 0, x_2);
lean::cnstr_set(x_141, 1, x_139);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_140);
x_143 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_144 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_142);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
return x_145;
}
default: 
{
obj* x_146; 
x_146 = lean::box(0);
x_17 = x_146;
goto block_55;
}
}
block_15:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::box(0);
x_6 = l_Lean_Expander_mixfixToNotationSpec___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_5);
x_12 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
block_55:
{
obj* x_18; 
lean::dec(x_17);
x_18 = lean::box(0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = l_Lean_Expander_mixfixToNotationSpec___closed__3;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_2);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
x_22 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_16);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_26 = lean::cnstr_get(x_16, 0);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_16, 0, x_30);
x_31 = l_Lean_Expander_mixfixToNotationSpec___closed__1;
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_16);
x_33 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_18);
x_37 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_40 = lean::cnstr_get(x_16, 0);
lean::inc(x_40);
lean::dec(x_16);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
x_43 = l_Lean_Expander_mixfixToNotationSpec___closed__4;
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = l_Lean_Expander_mixfixToNotationSpec___closed__1;
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_2);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_18);
x_52 = l_Lean_Expander_mixfixToNotationSpec___closed__2;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
obj* l_Lean_Expander_mixfixToNotationSpec___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Expander_mixfixToNotationSpec(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_identUnivs_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::box(0);
x_5 = lean::mk_string("a");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
lean::dec(x_7);
x_9 = l_Lean_Parser_Substring_ofString(x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_10);
lean::cnstr_set(x_11, 4, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_1);
x_13 = lean::apply_1(x_3, x_12);
return x_13;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_identUnivs_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::box(0);
x_5 = lean::box(0);
x_6 = lean::mk_string("b");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string(".");
lean::inc(x_7);
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
lean::dec(x_8);
x_10 = l_Lean_Parser_Substring_ofString(x_9);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_7);
lean::cnstr_set(x_11, 3, x_4);
lean::cnstr_set(x_11, 4, x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_1);
x_13 = lean::apply_1(x_3, x_12);
return x_13;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("notation");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(":=");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_identUnivs_HasView;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_4 = lean::box(0);
x_5 = lean::mk_string("b");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
lean::dec(x_7);
x_9 = l_Lean_Parser_Substring_ofString(x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_10);
lean::cnstr_set(x_11, 4, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_1);
x_13 = lean::apply_1(x_3, x_12);
return x_13;
}
}
obj* _init_l_Lean_Expander_mixfix_transform___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("`");
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_Expander_mixfix_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = l_Lean_Parser_command_mixfix_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 4);
lean::inc(x_9);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_59; 
x_59 = lean::cnstr_get(x_8, 0);
lean::inc(x_59);
lean::dec(x_8);
x_10 = x_59;
goto block_58;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_8, 0);
lean::inc(x_60);
lean::dec(x_8);
x_61 = lean::box(0);
x_62 = l_Lean_Expander_mixfix_transform___closed__6;
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set(x_63, 2, x_62);
lean::cnstr_set(x_63, 3, x_61);
x_10 = x_63;
goto block_58;
}
block_58:
{
obj* x_11; 
x_11 = l_Lean_Expander_mixfixToNotationSpec(x_7, x_10, x_2);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_6);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_16 = x_11;
} else {
 lean::dec_ref(x_11);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Parser_command_notation_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
switch (lean::obj_tag(x_7)) {
case 0:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_16);
lean::dec(x_7);
x_35 = l_Lean_Parser_Term_app_HasView;
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
x_37 = l_Lean_Expander_mixfix_transform___closed__5;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_9);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::apply_1(x_36, x_38);
x_40 = l_Lean_Expander_mixfix_transform___closed__3;
x_41 = l_Lean_Expander_mixfix_transform___closed__4;
x_42 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_42, 0, x_6);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_15);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set(x_42, 4, x_39);
x_43 = lean::apply_1(x_18, x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
case 4:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_16);
lean::dec(x_7);
x_46 = l_Lean_Parser_Term_app_HasView;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_48 = l_Lean_Expander_mixfix_transform___closed__1;
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_9);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::apply_1(x_47, x_49);
x_51 = l_Lean_Expander_mixfix_transform___closed__3;
x_52 = l_Lean_Expander_mixfix_transform___closed__4;
x_53 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_53, 0, x_6);
lean::cnstr_set(x_53, 1, x_51);
lean::cnstr_set(x_53, 2, x_15);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set(x_53, 4, x_50);
x_54 = lean::apply_1(x_18, x_53);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
default: 
{
obj* x_57; 
lean::dec(x_7);
x_57 = lean::box(0);
x_19 = x_57;
goto block_34;
}
}
block_34:
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_19);
x_20 = l_Lean_Parser_Term_app_HasView;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_22 = l_Lean_Expander_mixfix_transform___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_9);
lean::cnstr_set(x_23, 1, x_22);
lean::inc(x_21);
x_24 = lean::apply_1(x_21, x_23);
x_25 = l_Lean_Expander_mixfix_transform___closed__2;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::apply_1(x_21, x_26);
x_28 = l_Lean_Expander_mixfix_transform___closed__3;
x_29 = l_Lean_Expander_mixfix_transform___closed__4;
x_30 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_15);
lean::cnstr_set(x_30, 3, x_29);
lean::cnstr_set(x_30, 4, x_27);
x_31 = lean::apply_1(x_18, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_16)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_16;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
obj* l_Lean_Expander_mixfix_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_mixfix_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_reserveMixfix_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("reserve");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_reserveMixfix_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = l_Lean_Parser_command_reserveMixfix_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 2);
lean::inc(x_7);
lean::dec(x_5);
x_8 = l_Lean_Expander_mixfixToNotationSpec(x_6, x_7, x_2);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_8);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = l_Lean_Parser_command_reserveNotation_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = l_Lean_Expander_reserveMixfix_transform___closed__1;
x_17 = l_Lean_Expander_mixfix_transform___closed__3;
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_13);
x_19 = lean::apply_1(x_15, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_8, 0, x_20);
return x_8;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_22 = l_Lean_Parser_command_reserveNotation_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_24 = l_Lean_Expander_reserveMixfix_transform___closed__1;
x_25 = l_Lean_Expander_mixfix_transform___closed__3;
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set(x_26, 2, x_21);
x_27 = lean::apply_1(x_23, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
obj* l_Lean_Expander_reserveMixfix_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_reserveMixfix_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("{");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("}");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("⦃");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("⦄");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("[");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Expander_mkSimpleBinder___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("]");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_mkSimpleBinder(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
switch (x_2) {
case 0:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_5 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_6 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_3);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = l_Lean_Expander_mkSimpleBinder___closed__2;
x_10 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_11 = l_Lean_Expander_mkSimpleBinder___closed__3;
x_12 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_10);
lean::cnstr_set(x_12, 3, x_3);
lean::cnstr_set(x_12, 4, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
case 2:
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Expander_mkSimpleBinder___closed__4;
x_15 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_16 = l_Lean_Expander_mkSimpleBinder___closed__5;
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_15);
lean::cnstr_set(x_17, 3, x_3);
lean::cnstr_set(x_17, 4, x_16);
x_18 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
case 3:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = l_Lean_Expander_mkSimpleBinder___closed__6;
x_20 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_21 = l_Lean_Expander_mkSimpleBinder___closed__7;
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_20);
lean::cnstr_set(x_22, 3, x_3);
lean::cnstr_set(x_22, 4, x_21);
x_23 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
default: 
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_25 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_26 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_1);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_27, 3, x_3);
lean::cnstr_set(x_27, 4, x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
}
}
obj* l_Lean_Expander_mkSimpleBinder___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_Expander_mkSimpleBinder(x_1, x_4, x_3);
return x_5;
}
}
obj* _init_l_Lean_Expander_binderIdentToIdent___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("a");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
obj* l_Lean_Expander_binderIdentToIdent___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Expander_binderIdentToIdent___main___closed__1;
return x_3;
}
}
}
obj* l_Lean_Expander_binderIdentToIdent___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_binderIdentToIdent___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_binderIdentToIdent(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_binderIdentToIdent___main(x_1);
return x_2;
}
}
obj* l_Lean_Expander_binderIdentToIdent___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_binderIdentToIdent(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_getOptType___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Term_hole_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_3 = lean::box(0);
x_4 = lean::mk_string("_");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::apply_1(x_2, x_7);
return x_8;
}
}
obj* l_Lean_Expander_getOptType___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Expander_getOptType___main___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
return x_4;
}
}
}
obj* l_Lean_Expander_getOptType___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_getOptType___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Expander_getOptType(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_getOptType___main(x_1);
return x_2;
}
}
obj* l_Lean_Expander_getOptType___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_getOptType(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 0;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 0;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 0;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 0;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 0;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 0;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 0;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 0;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 1;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 1;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 1;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 1;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 1;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 1;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 1;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 1;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 2;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 2;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 2;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 2;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 2;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 2;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_Expander_binderIdentToIdent___main(x_5);
lean::dec(x_5);
x_8 = 2;
lean::inc(x_1);
x_9 = l_Lean_Expander_mkSimpleBinder(x_7, x_8, x_1);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_1, x_6);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
x_14 = 2;
lean::inc(x_1);
x_15 = l_Lean_Expander_mkSimpleBinder(x_13, x_14, x_1);
x_16 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_6);
lean::dec(x_6);
lean::inc(x_2);
x_9 = l_Lean_Expander_mkSimpleBinder(x_8, x_1, x_2);
x_10 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_1, x_2, x_7);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_13 = l_Lean_Expander_binderIdentToIdent___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_14 = l_Lean_Expander_mkSimpleBinder(x_13, x_1, x_2);
x_15 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_1, x_2, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("optParam");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("autoParam");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected auto Param after Type annotation");
return x_1;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("_inst_");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
}
obj* _init_l_Lean_Expander_expandBracketedBinder___main___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected anonymous Constructor");
return x_1;
}
}
obj* l_Lean_Expander_expandBracketedBinder___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_71; obj* x_72; 
x_71 = lean::cnstr_get(x_1, 0);
lean::inc(x_71);
lean::dec(x_1);
x_72 = lean::cnstr_get(x_71, 1);
lean::inc(x_72);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; 
lean::dec(x_72);
x_73 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_72, 0);
lean::inc(x_74);
lean::dec(x_72);
x_75 = lean::cnstr_get(x_74, 1);
lean::inc(x_75);
x_76 = l_Lean_Expander_getOptType___main(x_75);
x_77 = lean::cnstr_get(x_74, 2);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_75);
x_78 = lean::cnstr_get(x_74, 0);
lean::inc(x_78);
lean::dec(x_74);
x_79 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__5(x_76, x_78);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_77, 0);
lean::inc(x_81);
lean::dec(x_77);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_75);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
lean::dec(x_81);
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
lean::dec(x_82);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_76);
lean::cnstr_set(x_86, 1, x_85);
x_87 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_88 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_87, x_86);
x_89 = lean::cnstr_get(x_74, 0);
lean::inc(x_89);
lean::dec(x_74);
x_90 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__6(x_88, x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
else
{
lean::dec(x_76);
if (lean::obj_tag(x_75) == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_81, 0);
lean::inc(x_92);
lean::dec(x_81);
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
lean::dec(x_92);
x_94 = lean::box(0);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_94);
x_96 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_97 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_96, x_95);
x_98 = lean::cnstr_get(x_74, 0);
lean::inc(x_98);
lean::dec(x_74);
x_99 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__7(x_97, x_98);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
return x_100;
}
else
{
uint8 x_101; 
x_101 = !lean::is_exclusive(x_75);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_102 = lean::cnstr_get(x_75, 0);
lean::dec(x_102);
x_103 = l_Lean_Parser_Term_binderDefault_HasView;
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
x_105 = lean::apply_1(x_104, x_81);
lean::cnstr_set(x_75, 0, x_105);
x_106 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_107 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_75, x_106, x_2);
lean::dec(x_75);
if (lean::obj_tag(x_107) == 0)
{
uint8 x_108; 
lean::dec(x_74);
x_108 = !lean::is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
obj* x_109; obj* x_110; 
x_109 = lean::cnstr_get(x_107, 0);
lean::inc(x_109);
lean::dec(x_107);
x_110 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
else
{
uint8 x_111; 
x_111 = !lean::is_exclusive(x_107);
if (x_111 == 0)
{
obj* x_112; obj* x_113; obj* x_114; 
x_112 = lean::cnstr_get(x_107, 0);
x_113 = lean::cnstr_get(x_74, 0);
lean::inc(x_113);
lean::dec(x_74);
x_114 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_112, x_113);
lean::cnstr_set(x_107, 0, x_114);
return x_107;
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
x_116 = lean::cnstr_get(x_74, 0);
lean::inc(x_116);
lean::dec(x_74);
x_117 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_115, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_75);
x_119 = l_Lean_Parser_Term_binderDefault_HasView;
x_120 = lean::cnstr_get(x_119, 1);
lean::inc(x_120);
x_121 = lean::apply_1(x_120, x_81);
x_122 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_122, 0, x_121);
x_123 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_124 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_122, x_123, x_2);
lean::dec(x_122);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_74);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 x_126 = x_124;
} else {
 lean::dec_ref(x_124);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_125);
return x_127;
}
else
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_128 = lean::cnstr_get(x_124, 0);
lean::inc(x_128);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 x_129 = x_124;
} else {
 lean::dec_ref(x_124);
 x_129 = lean::box(0);
}
x_130 = lean::cnstr_get(x_74, 0);
lean::inc(x_130);
lean::dec(x_74);
x_131 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__8(x_128, x_130);
if (lean::is_scalar(x_129)) {
 x_132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_132 = x_129;
}
lean::cnstr_set(x_132, 0, x_131);
return x_132;
}
}
}
}
}
}
}
case 1:
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_133 = lean::cnstr_get(x_1, 0);
lean::inc(x_133);
lean::dec(x_1);
x_134 = lean::cnstr_get(x_133, 1);
lean::inc(x_134);
lean::dec(x_133);
x_135 = lean::cnstr_get(x_134, 1);
lean::inc(x_135);
x_136 = l_Lean_Expander_getOptType___main(x_135);
x_137 = lean::cnstr_get(x_134, 2);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_135);
x_138 = lean::cnstr_get(x_134, 0);
lean::inc(x_138);
lean::dec(x_134);
x_139 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__9(x_136, x_138);
x_140 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_140, 0, x_139);
return x_140;
}
else
{
obj* x_141; 
x_141 = lean::cnstr_get(x_137, 0);
lean::inc(x_141);
lean::dec(x_137);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_135);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
lean::dec(x_141);
x_143 = lean::cnstr_get(x_142, 1);
lean::inc(x_143);
lean::dec(x_142);
x_144 = lean::box(0);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_136);
lean::cnstr_set(x_146, 1, x_145);
x_147 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_148 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_147, x_146);
x_149 = lean::cnstr_get(x_134, 0);
lean::inc(x_149);
lean::dec(x_134);
x_150 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__10(x_148, x_149);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
else
{
lean::dec(x_136);
if (lean::obj_tag(x_135) == 0)
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_152 = lean::cnstr_get(x_141, 0);
lean::inc(x_152);
lean::dec(x_141);
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
lean::dec(x_152);
x_154 = lean::box(0);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_154);
x_156 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_157 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_156, x_155);
x_158 = lean::cnstr_get(x_134, 0);
lean::inc(x_158);
lean::dec(x_134);
x_159 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__11(x_157, x_158);
x_160 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_160, 0, x_159);
return x_160;
}
else
{
uint8 x_161; 
x_161 = !lean::is_exclusive(x_135);
if (x_161 == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_162 = lean::cnstr_get(x_135, 0);
lean::dec(x_162);
x_163 = l_Lean_Parser_Term_binderDefault_HasView;
x_164 = lean::cnstr_get(x_163, 1);
lean::inc(x_164);
x_165 = lean::apply_1(x_164, x_141);
lean::cnstr_set(x_135, 0, x_165);
x_166 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_167 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_135, x_166, x_2);
lean::dec(x_135);
if (lean::obj_tag(x_167) == 0)
{
uint8 x_168; 
lean::dec(x_134);
x_168 = !lean::is_exclusive(x_167);
if (x_168 == 0)
{
return x_167;
}
else
{
obj* x_169; obj* x_170; 
x_169 = lean::cnstr_get(x_167, 0);
lean::inc(x_169);
lean::dec(x_167);
x_170 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
return x_170;
}
}
else
{
uint8 x_171; 
x_171 = !lean::is_exclusive(x_167);
if (x_171 == 0)
{
obj* x_172; obj* x_173; obj* x_174; 
x_172 = lean::cnstr_get(x_167, 0);
x_173 = lean::cnstr_get(x_134, 0);
lean::inc(x_173);
lean::dec(x_134);
x_174 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_172, x_173);
lean::cnstr_set(x_167, 0, x_174);
return x_167;
}
else
{
obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_175 = lean::cnstr_get(x_167, 0);
lean::inc(x_175);
lean::dec(x_167);
x_176 = lean::cnstr_get(x_134, 0);
lean::inc(x_176);
lean::dec(x_134);
x_177 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_175, x_176);
x_178 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_178, 0, x_177);
return x_178;
}
}
}
else
{
obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
lean::dec(x_135);
x_179 = l_Lean_Parser_Term_binderDefault_HasView;
x_180 = lean::cnstr_get(x_179, 1);
lean::inc(x_180);
x_181 = lean::apply_1(x_180, x_141);
x_182 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_182, 0, x_181);
x_183 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_184 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_182, x_183, x_2);
lean::dec(x_182);
if (lean::obj_tag(x_184) == 0)
{
obj* x_185; obj* x_186; obj* x_187; 
lean::dec(x_134);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_186 = x_184;
} else {
 lean::dec_ref(x_184);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_185);
return x_187;
}
else
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_188 = lean::cnstr_get(x_184, 0);
lean::inc(x_188);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_189 = x_184;
} else {
 lean::dec_ref(x_184);
 x_189 = lean::box(0);
}
x_190 = lean::cnstr_get(x_134, 0);
lean::inc(x_190);
lean::dec(x_134);
x_191 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__12(x_188, x_190);
if (lean::is_scalar(x_189)) {
 x_192 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_192 = x_189;
}
lean::cnstr_set(x_192, 0, x_191);
return x_192;
}
}
}
}
}
}
case 2:
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_193 = lean::cnstr_get(x_1, 0);
lean::inc(x_193);
lean::dec(x_1);
x_194 = lean::cnstr_get(x_193, 1);
lean::inc(x_194);
lean::dec(x_193);
x_195 = lean::cnstr_get(x_194, 1);
lean::inc(x_195);
x_196 = l_Lean_Expander_getOptType___main(x_195);
x_197 = lean::cnstr_get(x_194, 2);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; obj* x_199; obj* x_200; 
lean::dec(x_195);
x_198 = lean::cnstr_get(x_194, 0);
lean::inc(x_198);
lean::dec(x_194);
x_199 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__13(x_196, x_198);
x_200 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_200, 0, x_199);
return x_200;
}
else
{
obj* x_201; 
x_201 = lean::cnstr_get(x_197, 0);
lean::inc(x_201);
lean::dec(x_197);
if (lean::obj_tag(x_201) == 0)
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_195);
x_202 = lean::cnstr_get(x_201, 0);
lean::inc(x_202);
lean::dec(x_201);
x_203 = lean::cnstr_get(x_202, 1);
lean::inc(x_203);
lean::dec(x_202);
x_204 = lean::box(0);
x_205 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_205, 0, x_203);
lean::cnstr_set(x_205, 1, x_204);
x_206 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_206, 0, x_196);
lean::cnstr_set(x_206, 1, x_205);
x_207 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_208 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_207, x_206);
x_209 = lean::cnstr_get(x_194, 0);
lean::inc(x_209);
lean::dec(x_194);
x_210 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__14(x_208, x_209);
x_211 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_211, 0, x_210);
return x_211;
}
else
{
lean::dec(x_196);
if (lean::obj_tag(x_195) == 0)
{
obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_212 = lean::cnstr_get(x_201, 0);
lean::inc(x_212);
lean::dec(x_201);
x_213 = lean::cnstr_get(x_212, 1);
lean::inc(x_213);
lean::dec(x_212);
x_214 = lean::box(0);
x_215 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_215, 0, x_213);
lean::cnstr_set(x_215, 1, x_214);
x_216 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_217 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_216, x_215);
x_218 = lean::cnstr_get(x_194, 0);
lean::inc(x_218);
lean::dec(x_194);
x_219 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__15(x_217, x_218);
x_220 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_220, 0, x_219);
return x_220;
}
else
{
uint8 x_221; 
x_221 = !lean::is_exclusive(x_195);
if (x_221 == 0)
{
obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
x_222 = lean::cnstr_get(x_195, 0);
lean::dec(x_222);
x_223 = l_Lean_Parser_Term_binderDefault_HasView;
x_224 = lean::cnstr_get(x_223, 1);
lean::inc(x_224);
x_225 = lean::apply_1(x_224, x_201);
lean::cnstr_set(x_195, 0, x_225);
x_226 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_227 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_195, x_226, x_2);
lean::dec(x_195);
if (lean::obj_tag(x_227) == 0)
{
uint8 x_228; 
lean::dec(x_194);
x_228 = !lean::is_exclusive(x_227);
if (x_228 == 0)
{
return x_227;
}
else
{
obj* x_229; obj* x_230; 
x_229 = lean::cnstr_get(x_227, 0);
lean::inc(x_229);
lean::dec(x_227);
x_230 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_230, 0, x_229);
return x_230;
}
}
else
{
uint8 x_231; 
x_231 = !lean::is_exclusive(x_227);
if (x_231 == 0)
{
obj* x_232; obj* x_233; obj* x_234; 
x_232 = lean::cnstr_get(x_227, 0);
x_233 = lean::cnstr_get(x_194, 0);
lean::inc(x_233);
lean::dec(x_194);
x_234 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_232, x_233);
lean::cnstr_set(x_227, 0, x_234);
return x_227;
}
else
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
x_235 = lean::cnstr_get(x_227, 0);
lean::inc(x_235);
lean::dec(x_227);
x_236 = lean::cnstr_get(x_194, 0);
lean::inc(x_236);
lean::dec(x_194);
x_237 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_235, x_236);
x_238 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_238, 0, x_237);
return x_238;
}
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_195);
x_239 = l_Lean_Parser_Term_binderDefault_HasView;
x_240 = lean::cnstr_get(x_239, 1);
lean::inc(x_240);
x_241 = lean::apply_1(x_240, x_201);
x_242 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_242, 0, x_241);
x_243 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_244 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_242, x_243, x_2);
lean::dec(x_242);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_246; obj* x_247; 
lean::dec(x_194);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_release(x_244, 0);
 x_246 = x_244;
} else {
 lean::dec_ref(x_244);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_245);
return x_247;
}
else
{
obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
x_248 = lean::cnstr_get(x_244, 0);
lean::inc(x_248);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_release(x_244, 0);
 x_249 = x_244;
} else {
 lean::dec_ref(x_244);
 x_249 = lean::box(0);
}
x_250 = lean::cnstr_get(x_194, 0);
lean::inc(x_250);
lean::dec(x_194);
x_251 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__16(x_248, x_250);
if (lean::is_scalar(x_249)) {
 x_252 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_252 = x_249;
}
lean::cnstr_set(x_252, 0, x_251);
return x_252;
}
}
}
}
}
}
case 3:
{
obj* x_253; obj* x_254; 
x_253 = lean::cnstr_get(x_1, 0);
lean::inc(x_253);
lean::dec(x_1);
x_254 = lean::cnstr_get(x_253, 1);
lean::inc(x_254);
lean::dec(x_253);
if (lean::obj_tag(x_254) == 0)
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; uint8 x_266; obj* x_267; obj* x_268; 
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
lean::dec(x_254);
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_257 = lean::cnstr_get(x_255, 2);
lean::inc(x_257);
lean::dec(x_255);
x_258 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_258, 0, x_256);
x_259 = lean::box(0);
x_260 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_260, 0, x_258);
lean::cnstr_set(x_260, 1, x_259);
x_261 = lean::box(0);
x_262 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_263 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_257);
x_264 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_264, 0, x_263);
x_265 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_265, 0, x_260);
lean::cnstr_set(x_265, 1, x_264);
lean::cnstr_set(x_265, 2, x_261);
x_266 = 3;
x_267 = lean::box(x_266);
x_268 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_265);
x_3 = x_268;
goto block_70;
}
else
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; uint8 x_276; obj* x_277; obj* x_278; 
x_269 = lean::cnstr_get(x_254, 0);
lean::inc(x_269);
lean::dec(x_254);
x_270 = lean::box(0);
x_271 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_272 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_269);
x_273 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_273, 0, x_272);
x_274 = l_Lean_Expander_expandBracketedBinder___main___closed__5;
x_275 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_273);
lean::cnstr_set(x_275, 2, x_270);
x_276 = 3;
x_277 = lean::box(x_276);
x_278 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_275);
x_3 = x_278;
goto block_70;
}
}
default: 
{
obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
x_279 = lean::cnstr_get(x_1, 0);
lean::inc(x_279);
lean::dec(x_1);
x_280 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_281 = lean::cnstr_get(x_280, 1);
lean::inc(x_281);
x_282 = lean::apply_1(x_281, x_279);
x_283 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_283, 0, x_282);
x_284 = l_Lean_Expander_expandBracketedBinder___main___closed__6;
x_285 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_283, x_284, x_2);
lean::dec(x_283);
if (lean::obj_tag(x_285) == 0)
{
uint8 x_286; 
x_286 = !lean::is_exclusive(x_285);
if (x_286 == 0)
{
return x_285;
}
else
{
obj* x_287; obj* x_288; 
x_287 = lean::cnstr_get(x_285, 0);
lean::inc(x_287);
lean::dec(x_285);
x_288 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_288, 0, x_287);
return x_288;
}
}
else
{
uint8 x_289; 
x_289 = !lean::is_exclusive(x_285);
if (x_289 == 0)
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
x_290 = lean::cnstr_get(x_285, 0);
x_291 = lean::cnstr_get(x_290, 0);
lean::inc(x_291);
x_292 = lean::cnstr_get(x_290, 1);
lean::inc(x_292);
lean::dec(x_290);
x_293 = lean::cnstr_get(x_292, 1);
lean::inc(x_293);
x_294 = l_Lean_Expander_getOptType___main(x_293);
x_295 = lean::cnstr_get(x_292, 2);
lean::inc(x_295);
if (lean::obj_tag(x_295) == 0)
{
obj* x_296; uint8 x_297; obj* x_298; 
lean::dec(x_293);
x_296 = lean::cnstr_get(x_292, 0);
lean::inc(x_296);
lean::dec(x_292);
x_297 = lean::unbox(x_291);
lean::dec(x_291);
x_298 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_297, x_294, x_296);
lean::cnstr_set(x_285, 0, x_298);
return x_285;
}
else
{
obj* x_299; 
x_299 = lean::cnstr_get(x_295, 0);
lean::inc(x_299);
lean::dec(x_295);
if (lean::obj_tag(x_299) == 0)
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; uint8 x_308; obj* x_309; 
lean::dec(x_293);
x_300 = lean::cnstr_get(x_299, 0);
lean::inc(x_300);
lean::dec(x_299);
x_301 = lean::cnstr_get(x_300, 1);
lean::inc(x_301);
lean::dec(x_300);
x_302 = lean::box(0);
x_303 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_303, 0, x_301);
lean::cnstr_set(x_303, 1, x_302);
x_304 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_304, 0, x_294);
lean::cnstr_set(x_304, 1, x_303);
x_305 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_306 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_305, x_304);
x_307 = lean::cnstr_get(x_292, 0);
lean::inc(x_307);
lean::dec(x_292);
x_308 = lean::unbox(x_291);
lean::dec(x_291);
x_309 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_308, x_306, x_307);
lean::cnstr_set(x_285, 0, x_309);
return x_285;
}
else
{
lean::dec(x_294);
if (lean::obj_tag(x_293) == 0)
{
obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; uint8 x_317; obj* x_318; 
x_310 = lean::cnstr_get(x_299, 0);
lean::inc(x_310);
lean::dec(x_299);
x_311 = lean::cnstr_get(x_310, 1);
lean::inc(x_311);
lean::dec(x_310);
x_312 = lean::box(0);
x_313 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_312);
x_314 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_315 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_314, x_313);
x_316 = lean::cnstr_get(x_292, 0);
lean::inc(x_316);
lean::dec(x_292);
x_317 = lean::unbox(x_291);
lean::dec(x_291);
x_318 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_317, x_315, x_316);
lean::cnstr_set(x_285, 0, x_318);
return x_285;
}
else
{
uint8 x_319; 
lean::free_heap_obj(x_285);
x_319 = !lean::is_exclusive(x_293);
if (x_319 == 0)
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; 
x_320 = lean::cnstr_get(x_293, 0);
lean::dec(x_320);
x_321 = l_Lean_Parser_Term_binderDefault_HasView;
x_322 = lean::cnstr_get(x_321, 1);
lean::inc(x_322);
x_323 = lean::apply_1(x_322, x_299);
lean::cnstr_set(x_293, 0, x_323);
x_324 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_325 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_293, x_324, x_2);
lean::dec(x_293);
if (lean::obj_tag(x_325) == 0)
{
uint8 x_326; 
lean::dec(x_292);
lean::dec(x_291);
x_326 = !lean::is_exclusive(x_325);
if (x_326 == 0)
{
return x_325;
}
else
{
obj* x_327; obj* x_328; 
x_327 = lean::cnstr_get(x_325, 0);
lean::inc(x_327);
lean::dec(x_325);
x_328 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_328, 0, x_327);
return x_328;
}
}
else
{
uint8 x_329; 
x_329 = !lean::is_exclusive(x_325);
if (x_329 == 0)
{
obj* x_330; obj* x_331; uint8 x_332; obj* x_333; 
x_330 = lean::cnstr_get(x_325, 0);
x_331 = lean::cnstr_get(x_292, 0);
lean::inc(x_331);
lean::dec(x_292);
x_332 = lean::unbox(x_291);
lean::dec(x_291);
x_333 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_332, x_330, x_331);
lean::cnstr_set(x_325, 0, x_333);
return x_325;
}
else
{
obj* x_334; obj* x_335; uint8 x_336; obj* x_337; obj* x_338; 
x_334 = lean::cnstr_get(x_325, 0);
lean::inc(x_334);
lean::dec(x_325);
x_335 = lean::cnstr_get(x_292, 0);
lean::inc(x_335);
lean::dec(x_292);
x_336 = lean::unbox(x_291);
lean::dec(x_291);
x_337 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_336, x_334, x_335);
x_338 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_338, 0, x_337);
return x_338;
}
}
}
else
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; 
lean::dec(x_293);
x_339 = l_Lean_Parser_Term_binderDefault_HasView;
x_340 = lean::cnstr_get(x_339, 1);
lean::inc(x_340);
x_341 = lean::apply_1(x_340, x_299);
x_342 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_342, 0, x_341);
x_343 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_344 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_342, x_343, x_2);
lean::dec(x_342);
if (lean::obj_tag(x_344) == 0)
{
obj* x_345; obj* x_346; obj* x_347; 
lean::dec(x_292);
lean::dec(x_291);
x_345 = lean::cnstr_get(x_344, 0);
lean::inc(x_345);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_release(x_344, 0);
 x_346 = x_344;
} else {
 lean::dec_ref(x_344);
 x_346 = lean::box(0);
}
if (lean::is_scalar(x_346)) {
 x_347 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_347 = x_346;
}
lean::cnstr_set(x_347, 0, x_345);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_344, 0);
lean::inc(x_348);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_release(x_344, 0);
 x_349 = x_344;
} else {
 lean::dec_ref(x_344);
 x_349 = lean::box(0);
}
x_350 = lean::cnstr_get(x_292, 0);
lean::inc(x_350);
lean::dec(x_292);
x_351 = lean::unbox(x_291);
lean::dec(x_291);
x_352 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_351, x_348, x_350);
if (lean::is_scalar(x_349)) {
 x_353 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_353 = x_349;
}
lean::cnstr_set(x_353, 0, x_352);
return x_353;
}
}
}
}
}
}
else
{
obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; 
x_354 = lean::cnstr_get(x_285, 0);
lean::inc(x_354);
lean::dec(x_285);
x_355 = lean::cnstr_get(x_354, 0);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_354, 1);
lean::inc(x_356);
lean::dec(x_354);
x_357 = lean::cnstr_get(x_356, 1);
lean::inc(x_357);
x_358 = l_Lean_Expander_getOptType___main(x_357);
x_359 = lean::cnstr_get(x_356, 2);
lean::inc(x_359);
if (lean::obj_tag(x_359) == 0)
{
obj* x_360; uint8 x_361; obj* x_362; obj* x_363; 
lean::dec(x_357);
x_360 = lean::cnstr_get(x_356, 0);
lean::inc(x_360);
lean::dec(x_356);
x_361 = lean::unbox(x_355);
lean::dec(x_355);
x_362 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_361, x_358, x_360);
x_363 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_363, 0, x_362);
return x_363;
}
else
{
obj* x_364; 
x_364 = lean::cnstr_get(x_359, 0);
lean::inc(x_364);
lean::dec(x_359);
if (lean::obj_tag(x_364) == 0)
{
obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; uint8 x_373; obj* x_374; obj* x_375; 
lean::dec(x_357);
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
lean::dec(x_364);
x_366 = lean::cnstr_get(x_365, 1);
lean::inc(x_366);
lean::dec(x_365);
x_367 = lean::box(0);
x_368 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_368, 0, x_366);
lean::cnstr_set(x_368, 1, x_367);
x_369 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_369, 0, x_358);
lean::cnstr_set(x_369, 1, x_368);
x_370 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_371 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_370, x_369);
x_372 = lean::cnstr_get(x_356, 0);
lean::inc(x_372);
lean::dec(x_356);
x_373 = lean::unbox(x_355);
lean::dec(x_355);
x_374 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_373, x_371, x_372);
x_375 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_375, 0, x_374);
return x_375;
}
else
{
lean::dec(x_358);
if (lean::obj_tag(x_357) == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; uint8 x_383; obj* x_384; obj* x_385; 
x_376 = lean::cnstr_get(x_364, 0);
lean::inc(x_376);
lean::dec(x_364);
x_377 = lean::cnstr_get(x_376, 1);
lean::inc(x_377);
lean::dec(x_376);
x_378 = lean::box(0);
x_379 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_379, 0, x_377);
lean::cnstr_set(x_379, 1, x_378);
x_380 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_381 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_380, x_379);
x_382 = lean::cnstr_get(x_356, 0);
lean::inc(x_382);
lean::dec(x_356);
x_383 = lean::unbox(x_355);
lean::dec(x_355);
x_384 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_383, x_381, x_382);
x_385 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_385, 0, x_384);
return x_385;
}
else
{
obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
if (lean::is_exclusive(x_357)) {
 lean::cnstr_release(x_357, 0);
 x_386 = x_357;
} else {
 lean::dec_ref(x_357);
 x_386 = lean::box(0);
}
x_387 = l_Lean_Parser_Term_binderDefault_HasView;
x_388 = lean::cnstr_get(x_387, 1);
lean::inc(x_388);
x_389 = lean::apply_1(x_388, x_364);
if (lean::is_scalar(x_386)) {
 x_390 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_390 = x_386;
}
lean::cnstr_set(x_390, 0, x_389);
x_391 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_392 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_390, x_391, x_2);
lean::dec(x_390);
if (lean::obj_tag(x_392) == 0)
{
obj* x_393; obj* x_394; obj* x_395; 
lean::dec(x_356);
lean::dec(x_355);
x_393 = lean::cnstr_get(x_392, 0);
lean::inc(x_393);
if (lean::is_exclusive(x_392)) {
 lean::cnstr_release(x_392, 0);
 x_394 = x_392;
} else {
 lean::dec_ref(x_392);
 x_394 = lean::box(0);
}
if (lean::is_scalar(x_394)) {
 x_395 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_395 = x_394;
}
lean::cnstr_set(x_395, 0, x_393);
return x_395;
}
else
{
obj* x_396; obj* x_397; obj* x_398; uint8 x_399; obj* x_400; obj* x_401; 
x_396 = lean::cnstr_get(x_392, 0);
lean::inc(x_396);
if (lean::is_exclusive(x_392)) {
 lean::cnstr_release(x_392, 0);
 x_397 = x_392;
} else {
 lean::dec_ref(x_392);
 x_397 = lean::box(0);
}
x_398 = lean::cnstr_get(x_356, 0);
lean::inc(x_398);
lean::dec(x_356);
x_399 = lean::unbox(x_355);
lean::dec(x_355);
x_400 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_399, x_396, x_398);
if (lean::is_scalar(x_397)) {
 x_401 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_401 = x_397;
}
lean::cnstr_set(x_401, 0, x_400);
return x_401;
}
}
}
}
}
}
}
}
block_70:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = l_Lean_Expander_getOptType___main(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
lean::dec(x_6);
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_10, x_7, x_9);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Expander_expandBracketedBinder___main___closed__1;
x_20 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_19, x_18);
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_22 = lean::unbox(x_4);
lean::dec(x_4);
x_23 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_22, x_20, x_21);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
lean::dec(x_7);
if (lean::obj_tag(x_6) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
lean::dec(x_13);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Expander_expandBracketedBinder___main___closed__2;
x_30 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_29, x_28);
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_32 = lean::unbox(x_4);
lean::dec(x_4);
x_33 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_32, x_30, x_31);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_6);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_36 = lean::cnstr_get(x_6, 0);
lean::dec(x_36);
x_37 = l_Lean_Parser_Term_binderDefault_HasView;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_39 = lean::apply_1(x_38, x_13);
lean::cnstr_set(x_6, 0, x_39);
x_40 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_41 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_6, x_40, x_2);
lean::dec(x_6);
if (lean::obj_tag(x_41) == 0)
{
uint8 x_42; 
lean::dec(x_5);
lean::dec(x_4);
x_42 = !lean::is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
lean::dec(x_41);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_41);
if (x_45 == 0)
{
obj* x_46; obj* x_47; uint8 x_48; obj* x_49; 
x_46 = lean::cnstr_get(x_41, 0);
x_47 = lean::cnstr_get(x_5, 0);
lean::inc(x_47);
lean::dec(x_5);
x_48 = lean::unbox(x_4);
lean::dec(x_4);
x_49 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_48, x_46, x_47);
lean::cnstr_set(x_41, 0, x_49);
return x_41;
}
else
{
obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_51 = lean::cnstr_get(x_5, 0);
lean::inc(x_51);
lean::dec(x_5);
x_52 = lean::unbox(x_4);
lean::dec(x_4);
x_53 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_52, x_50, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_6);
x_55 = l_Lean_Parser_Term_binderDefault_HasView;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_57 = lean::apply_1(x_56, x_13);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = l_Lean_Expander_expandBracketedBinder___main___closed__3;
x_60 = l_Lean_Expander_error___at_Lean_Expander_mkNotationTransformer___spec__1___rarg(x_58, x_59, x_2);
lean::dec(x_58);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_5);
lean::dec(x_4);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_62 = x_60;
} else {
 lean::dec_ref(x_60);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_60, 0);
lean::inc(x_64);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_65 = x_60;
} else {
 lean::dec_ref(x_60);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_5, 0);
lean::inc(x_66);
lean::dec(x_5);
x_67 = lean::unbox(x_4);
lean::dec(x_4);
x_68 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_67, x_64, x_66);
if (lean::is_scalar(x_65)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_65;
}
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
}
}
}
}
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__1(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__2(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__3(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__4(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__17(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__18(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__19(x_4, x_2, x_3);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Expander_expandBracketedBinder___main___spec__20(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Expander_expandBracketedBinder___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_expandBracketedBinder___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_expandBracketedBinder(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_expandBracketedBinder___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expander_expandBracketedBinder___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_expandBracketedBinder(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_1, x_2, x_3, x_6);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_5);
x_9 = 0;
x_10 = l_Lean_Expander_mkSimpleBinder(x_8, x_9, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_2(x_1, x_11, x_7);
return x_12;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_1, x_2, x_3, x_6);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_5);
x_9 = 0;
x_10 = l_Lean_Expander_mkSimpleBinder(x_8, x_9, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_2(x_1, x_11, x_7);
return x_12;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
x_6 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_2, x_5);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::apply_2(x_1, x_7, x_6);
return x_8;
}
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("match ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::box(0);
x_2 = lean::mk_string("x");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_Lean_Parser_identUnivs_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_4);
x_13 = lean::apply_1(x_11, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_4);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" with ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_1 = lean::box(0);
x_2 = lean::mk_string("x");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_Lean_Parser_Term_hole_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::mk_string("_");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_1(x_11, x_15);
x_17 = 0;
x_18 = l_Lean_Expander_mkSimpleBinder(x_9, x_17, x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_1);
x_9 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_1, x_2, x_8, x_4);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
lean::free_heap_obj(x_3);
lean::dec(x_7);
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
else
{
if (lean::obj_tag(x_7) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_9);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_9, 0);
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
if (lean::obj_tag(x_15) == 4)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_28 = lean::cnstr_get(x_15, 0);
lean::inc(x_28);
lean::dec(x_15);
x_29 = lean::box(0);
x_30 = lean::box(0);
x_31 = l_Lean_Parser_Term_match_HasView;
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_33 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
x_35 = lean::apply_1(x_34, x_28);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_29);
lean::cnstr_set(x_3, 1, x_30);
lean::cnstr_set(x_3, 0, x_36);
x_37 = l_Lean_Expander_mixfix_transform___closed__4;
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_3);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set(x_38, 2, x_14);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_29);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_30);
x_41 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_42 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2;
x_43 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_44 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_29);
lean::cnstr_set(x_44, 3, x_43);
lean::cnstr_set(x_44, 4, x_29);
lean::cnstr_set(x_44, 5, x_40);
x_45 = lean::apply_1(x_32, x_44);
x_46 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
x_47 = lean::apply_2(x_1, x_46, x_45);
lean::cnstr_set(x_9, 0, x_47);
return x_9;
}
else
{
obj* x_48; 
lean::free_heap_obj(x_9);
lean::free_heap_obj(x_3);
x_48 = lean::box(0);
x_16 = x_48;
goto block_27;
}
block_27:
{
obj* x_17; 
lean::dec(x_16);
x_17 = l_Lean_Expander_expandBracketedBinder___main(x_15, x_4);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
lean::dec(x_14);
lean::dec(x_1);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_17);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_14, x_22);
lean::dec(x_22);
lean::dec(x_14);
lean::cnstr_set(x_17, 0, x_23);
return x_17;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
lean::dec(x_17);
x_25 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_14, x_24);
lean::dec(x_24);
lean::dec(x_14);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
}
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_9, 0);
lean::inc(x_49);
lean::dec(x_9);
x_50 = lean::cnstr_get(x_7, 0);
lean::inc(x_50);
lean::dec(x_7);
if (lean::obj_tag(x_50) == 4)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_61 = lean::cnstr_get(x_50, 0);
lean::inc(x_61);
lean::dec(x_50);
x_62 = lean::box(0);
x_63 = lean::box(0);
x_64 = l_Lean_Parser_Term_match_HasView;
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
x_66 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_68 = lean::apply_1(x_67, x_61);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_62);
lean::cnstr_set(x_3, 1, x_63);
lean::cnstr_set(x_3, 0, x_69);
x_70 = l_Lean_Expander_mixfix_transform___closed__4;
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_3);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set(x_71, 2, x_49);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_62);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_63);
x_74 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_75 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2;
x_76 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_77 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
lean::cnstr_set(x_77, 2, x_62);
lean::cnstr_set(x_77, 3, x_76);
lean::cnstr_set(x_77, 4, x_62);
lean::cnstr_set(x_77, 5, x_73);
x_78 = lean::apply_1(x_65, x_77);
x_79 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
x_80 = lean::apply_2(x_1, x_79, x_78);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
else
{
obj* x_82; 
lean::free_heap_obj(x_3);
x_82 = lean::box(0);
x_51 = x_82;
goto block_60;
}
block_60:
{
obj* x_52; 
lean::dec(x_51);
x_52 = l_Lean_Expander_expandBracketedBinder___main(x_50, x_4);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_49);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_54 = x_52;
} else {
 lean::dec_ref(x_52);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_53);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_52, 0);
lean::inc(x_56);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 x_57 = x_52;
} else {
 lean::dec_ref(x_52);
 x_57 = lean::box(0);
}
x_58 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_49, x_56);
lean::dec(x_56);
lean::dec(x_49);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
uint8 x_83; 
lean::free_heap_obj(x_3);
x_83 = !lean::is_exclusive(x_9);
if (x_83 == 0)
{
obj* x_84; obj* x_85; obj* x_86; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_84 = lean::cnstr_get(x_9, 0);
x_85 = lean::cnstr_get(x_7, 0);
lean::inc(x_85);
lean::dec(x_7);
x_86 = l_Lean_Expander_binderIdentToIdent___main(x_85);
lean::dec(x_85);
x_87 = 0;
x_88 = l_Lean_Expander_getOptType___main___closed__1;
x_89 = l_Lean_Expander_mkSimpleBinder(x_86, x_87, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::apply_2(x_1, x_90, x_84);
lean::cnstr_set(x_9, 0, x_91);
return x_9;
}
else
{
obj* x_92; obj* x_93; obj* x_94; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_9, 0);
lean::inc(x_92);
lean::dec(x_9);
x_93 = lean::cnstr_get(x_7, 0);
lean::inc(x_93);
lean::dec(x_7);
x_94 = l_Lean_Expander_binderIdentToIdent___main(x_93);
lean::dec(x_93);
x_95 = 0;
x_96 = l_Lean_Expander_getOptType___main___closed__1;
x_97 = l_Lean_Expander_mkSimpleBinder(x_94, x_95, x_96);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
x_99 = lean::apply_2(x_1, x_98, x_92);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
return x_100;
}
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_3, 0);
x_102 = lean::cnstr_get(x_3, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_3);
lean::inc(x_1);
x_103 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_1, x_2, x_102, x_4);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_101);
lean::dec(x_1);
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_105 = x_103;
} else {
 lean::dec_ref(x_103);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_104);
return x_106;
}
else
{
if (lean::obj_tag(x_101) == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_107 = lean::cnstr_get(x_103, 0);
lean::inc(x_107);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_108 = x_103;
} else {
 lean::dec_ref(x_103);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_101, 0);
lean::inc(x_109);
lean::dec(x_101);
if (lean::obj_tag(x_109) == 4)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_120 = lean::cnstr_get(x_109, 0);
lean::inc(x_120);
lean::dec(x_109);
x_121 = lean::box(0);
x_122 = lean::box(0);
x_123 = l_Lean_Parser_Term_match_HasView;
x_124 = lean::cnstr_get(x_123, 1);
lean::inc(x_124);
x_125 = l_Lean_Parser_Term_anonymousConstructor_HasView;
x_126 = lean::cnstr_get(x_125, 1);
lean::inc(x_126);
x_127 = lean::apply_1(x_126, x_120);
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_122);
x_130 = l_Lean_Expander_mixfix_transform___closed__4;
x_131 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_131, 0, x_129);
lean::cnstr_set(x_131, 1, x_130);
lean::cnstr_set(x_131, 2, x_107);
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_121);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_122);
x_134 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_135 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__2;
x_136 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_137 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_137, 0, x_134);
lean::cnstr_set(x_137, 1, x_135);
lean::cnstr_set(x_137, 2, x_121);
lean::cnstr_set(x_137, 3, x_136);
lean::cnstr_set(x_137, 4, x_121);
lean::cnstr_set(x_137, 5, x_133);
x_138 = lean::apply_1(x_124, x_137);
x_139 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__4;
x_140 = lean::apply_2(x_1, x_139, x_138);
if (lean::is_scalar(x_108)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_108;
}
lean::cnstr_set(x_141, 0, x_140);
return x_141;
}
else
{
obj* x_142; 
lean::dec(x_108);
x_142 = lean::box(0);
x_110 = x_142;
goto block_119;
}
block_119:
{
obj* x_111; 
lean::dec(x_110);
x_111 = l_Lean_Expander_expandBracketedBinder___main(x_109, x_4);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_107);
lean::dec(x_1);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 x_113 = x_111;
} else {
 lean::dec_ref(x_111);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_112);
return x_114;
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_115 = lean::cnstr_get(x_111, 0);
lean::inc(x_115);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 x_116 = x_111;
} else {
 lean::dec_ref(x_111);
 x_116 = lean::box(0);
}
x_117 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_107, x_115);
lean::dec(x_115);
lean::dec(x_107);
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_103, 0);
lean::inc(x_143);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_144 = x_103;
} else {
 lean::dec_ref(x_103);
 x_144 = lean::box(0);
}
x_145 = lean::cnstr_get(x_101, 0);
lean::inc(x_145);
lean::dec(x_101);
x_146 = l_Lean_Expander_binderIdentToIdent___main(x_145);
lean::dec(x_145);
x_147 = 0;
x_148 = l_Lean_Expander_getOptType___main___closed__1;
x_149 = l_Lean_Expander_mkSimpleBinder(x_146, x_147, x_148);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_151 = lean::apply_2(x_1, x_150, x_143);
if (lean::is_scalar(x_144)) {
 x_152 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_152 = x_144;
}
lean::cnstr_set(x_152, 0, x_151);
return x_152;
}
}
}
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_1, x_2, x_3, x_6);
x_8 = l_Lean_Expander_binderIdentToIdent___main(x_5);
x_9 = 0;
x_10 = l_Lean_Expander_mkSimpleBinder(x_8, x_9, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_2(x_1, x_11, x_7);
return x_12;
}
}
}
obj* l_Lean_Expander_expandBinders(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = l_Lean_Expander_getOptType___main___closed__1;
x_9 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_1, x_8, x_3, x_7);
lean::dec(x_7);
lean::dec(x_3);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_6);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_6, 0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_14, 1);
lean::inc(x_16);
lean::dec(x_14);
x_17 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_1, x_16, x_3, x_15);
lean::dec(x_15);
lean::dec(x_3);
lean::cnstr_set(x_6, 0, x_17);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_6);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
lean::inc(x_1);
x_20 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_1, x_3, x_19, x_4);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; 
lean::free_heap_obj(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_20);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
x_26 = lean::cnstr_get(x_5, 0);
lean::inc(x_26);
lean::dec(x_5);
x_27 = l_Lean_Expander_getOptType___main___closed__1;
x_28 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_1, x_27, x_25, x_26);
lean::dec(x_26);
lean::dec(x_25);
lean::cnstr_set(x_6, 0, x_28);
lean::cnstr_set(x_20, 0, x_6);
return x_20;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_5, 0);
lean::inc(x_30);
lean::dec(x_5);
x_31 = l_Lean_Expander_getOptType___main___closed__1;
x_32 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_1, x_31, x_29, x_30);
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_6, 0, x_32);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_6);
return x_33;
}
}
}
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_6, 0);
lean::inc(x_34);
lean::dec(x_6);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::dec(x_34);
x_36 = lean::cnstr_get(x_5, 0);
lean::inc(x_36);
lean::dec(x_5);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
lean::dec(x_35);
x_38 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_1, x_37, x_3, x_36);
lean::dec(x_36);
lean::dec(x_3);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
lean::inc(x_1);
x_42 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_1, x_3, x_41, x_4);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_5);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_44 = x_42;
} else {
 lean::dec_ref(x_42);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_43);
return x_45;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_47 = x_42;
} else {
 lean::dec_ref(x_42);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_5, 0);
lean::inc(x_48);
lean::dec(x_5);
x_49 = l_Lean_Expander_getOptType___main___closed__1;
x_50 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_1, x_49, x_46, x_48);
lean::dec(x_48);
lean::dec(x_46);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
if (lean::is_scalar(x_47)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_47;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
else
{
obj* x_53; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_53 = l_Lean_Expander_noExpansion(x_4);
return x_53;
}
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__3(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_foldr___main___at_Lean_Expander_expandBinders___spec__5(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Expander_expandBinders___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_expandBinders(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_Lean_Expander_expandBracketedBinder___main(x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::free_heap_obj(x_1);
lean::dec(x_6);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_12 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_6, x_2);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
lean::dec(x_11);
lean::free_heap_obj(x_1);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_12);
if (x_16 == 0)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_1, 1, x_17);
lean::cnstr_set(x_1, 0, x_11);
lean::cnstr_set(x_12, 0, x_1);
return x_12;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
lean::dec(x_12);
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_11);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_1);
return x_19;
}
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_22 = l_Lean_Expander_expandBracketedBinder___main(x_20, x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_21);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_24 = x_22;
} else {
 lean::dec_ref(x_22);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_23);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_27 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_21, x_2);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_26);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_29 = x_27;
} else {
 lean::dec_ref(x_27);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_32 = x_27;
} else {
 lean::dec_ref(x_27);
 x_32 = lean::box(0);
}
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_26);
lean::cnstr_set(x_33, 1, x_31);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
obj* l_Lean_Expander_bracketedBinders_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_7, x_2);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
lean::free_heap_obj(x_5);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_8);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
x_15 = l_List_join___main___rarg(x_13);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_15);
x_16 = lean::apply_1(x_14, x_5);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_8, 0, x_17);
return x_8;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
lean::dec(x_8);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_20 = l_List_join___main___rarg(x_18);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_20);
x_21 = lean::apply_1(x_19, x_5);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
lean::dec(x_5);
x_25 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_24, x_2);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_27 = x_25;
} else {
 lean::dec_ref(x_25);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_26);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_25, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_30 = x_25;
} else {
 lean::dec_ref(x_25);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_3, 1);
lean::inc(x_31);
x_32 = l_List_join___main___rarg(x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::apply_1(x_31, x_33);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
if (lean::is_scalar(x_30)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_30;
}
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
obj* x_37; 
lean::dec(x_5);
x_37 = l_Lean_Expander_noExpansion(x_2);
return x_37;
}
}
}
obj* l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mmap___main___at_Lean_Expander_bracketedBinders_transform___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_bracketedBinders_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_bracketedBinders_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_lambda_transform___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = l_Lean_Parser_Term_lambda_HasView;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_6 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_6);
lean::cnstr_set(x_7, 3, x_2);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
}
obj* _init_l_Lean_Expander_lambda_transform___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_lambda_transform___lambda__1), 2, 0);
return x_1;
}
}
obj* l_Lean_Expander_lambda_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = l_Lean_Parser_Term_lambda_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
x_8 = l_Lean_Expander_lambda_transform___closed__1;
x_9 = l_Lean_Expander_expandBinders(x_8, x_6, x_7, x_2);
return x_9;
}
}
obj* l_Lean_Expander_lambda_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_lambda_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_pi_transform___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_Lean_Parser_Term_pi_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 3);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_1, 2);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_1, 1);
lean::dec(x_9);
x_10 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::cnstr_set(x_1, 3, x_3);
lean::cnstr_set(x_1, 2, x_10);
lean::cnstr_set(x_1, 1, x_2);
x_11 = lean::apply_1(x_5, x_1);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_13 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_13);
lean::cnstr_set(x_14, 3, x_3);
x_15 = lean::apply_1(x_5, x_14);
return x_15;
}
}
}
obj* l_Lean_Expander_pi_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = l_Lean_Parser_Term_pi_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_pi_transform___lambda__1), 3, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 3);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_Lean_Expander_expandBinders(x_6, x_7, x_8, x_2);
return x_9;
}
}
obj* l_Lean_Expander_pi_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_pi_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_coe___at_Lean_Expander_depArrow_transform___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(obj* x_1) {
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
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* _init_l_Lean_Expander_depArrow_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Π");
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_Expander_depArrow_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_3 = l_Lean_Parser_Term_depArrow_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = l_Lean_Parser_Term_pi_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 2);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = l_Lean_Expander_depArrow_transform___closed__1;
x_18 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set(x_19, 2, x_18);
lean::cnstr_set(x_19, 3, x_9);
x_20 = lean::apply_1(x_7, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
obj* l_Lean_Expander_depArrow_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_depArrow_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_arrow_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("a");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
obj* l_Lean_Expander_arrow_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_3 = l_Lean_Parser_Term_arrow_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = l_Lean_Parser_Term_pi_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_9 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_10 = l_Lean_Expander_arrow_transform___closed__1;
x_11 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_12 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_8);
lean::cnstr_set(x_13, 4, x_12);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::cnstr_get(x_5, 2);
lean::inc(x_16);
lean::dec(x_5);
x_17 = l_Lean_Expander_depArrow_transform___closed__1;
x_18 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set(x_19, 2, x_18);
lean::cnstr_set(x_19, 3, x_16);
x_20 = lean::apply_1(x_7, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
obj* l_Lean_Expander_arrow_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_arrow_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_map___main___at_Lean_Expander_paren_transform___spec__1(obj* x_1) {
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
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* _init_l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Prod");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("mk");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_Expander_globId(x_5);
return x_6;
}
}
obj* l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::dec(x_6);
lean::inc(x_3);
x_7 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_3, lean::box(0));
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 1);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_3, 0);
lean::dec(x_10);
x_11 = lean::box(0);
lean::cnstr_set(x_3, 1, x_11);
lean::cnstr_set(x_3, 0, x_7);
x_12 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
x_13 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_12, x_1);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_3);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_1, 1, x_15);
x_16 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
x_17 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_16, x_1);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
lean::inc(x_3);
x_19 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_3, lean::box(0));
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_20 = x_3;
} else {
 lean::dec_ref(x_3);
 x_20 = lean::box(0);
}
x_21 = lean::box(0);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3___closed__1;
x_25 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_24, x_23);
return x_25;
}
}
}
}
obj* l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(obj* x_1) {
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
obj* x_3; obj* x_4; 
x_3 = l_List_foldr1___main___at_Lean_Expander_paren_transform___spec__3(x_1, lean::box(0));
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
}
obj* _init_l_Lean_Expander_paren_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Unit");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("unit");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_Expander_globId(x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_Lean_Expander_paren_transform___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("typedExpr");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* l_Lean_Expander_paren_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_Term_paren_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_Lean_Expander_paren_transform___closed__1;
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
lean::cnstr_set(x_6, 0, x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_6);
return x_12;
}
else
{
uint8 x_13; 
lean::free_heap_obj(x_6);
x_13 = !lean::is_exclusive(x_10);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_10, 0);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::free_heap_obj(x_10);
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
x_18 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_9, 0);
lean::inc(x_22);
lean::dec(x_9);
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Expander_paren_transform___closed__2;
x_29 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_28, x_27);
lean::cnstr_set(x_10, 0, x_29);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_10);
return x_30;
}
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_10, 0);
lean::inc(x_31);
lean::dec(x_10);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
lean::dec(x_9);
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_35 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_39 = lean::cnstr_get(x_9, 0);
lean::inc(x_39);
lean::dec(x_9);
x_40 = lean::cnstr_get(x_31, 0);
lean::inc(x_40);
lean::dec(x_31);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Expander_paren_transform___closed__2;
x_46 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_45, x_44);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_6, 0);
lean::inc(x_49);
lean::dec(x_6);
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
lean::dec(x_49);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_55 = x_50;
} else {
 lean::dec_ref(x_50);
 x_55 = lean::box(0);
}
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_55);
x_56 = lean::cnstr_get(x_49, 0);
lean::inc(x_56);
lean::dec(x_49);
x_57 = lean::cnstr_get(x_54, 0);
lean::inc(x_57);
lean::dec(x_54);
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
lean::dec(x_57);
x_59 = l_List_map___main___at_Lean_Expander_paren_transform___spec__1(x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set(x_60, 1, x_59);
x_61 = l_List_foldr1Opt___main___at_Lean_Expander_paren_transform___spec__2(x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_63 = lean::cnstr_get(x_49, 0);
lean::inc(x_63);
lean::dec(x_49);
x_64 = lean::cnstr_get(x_54, 0);
lean::inc(x_64);
lean::dec(x_54);
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
lean::dec(x_64);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_67);
x_69 = l_Lean_Expander_paren_transform___closed__2;
x_70 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_69, x_68);
if (lean::is_scalar(x_55)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_55;
}
lean::cnstr_set(x_71, 0, x_70);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
}
}
}
}
}
obj* l_Lean_Expander_paren_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_paren_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_assume_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("this");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
obj* l_Lean_Expander_assume_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = l_Lean_Parser_Term_assume_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
x_8 = l_Lean_Parser_Term_lambda_HasView;
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_13 = l_Lean_Expander_assume_transform___closed__1;
x_14 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_15 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_16 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_11);
lean::cnstr_set(x_16, 4, x_15);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_20 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set(x_21, 3, x_7);
x_22 = lean::apply_1(x_9, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_8, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_6, 0);
lean::inc(x_26);
lean::dec(x_6);
x_27 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_28 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_28);
lean::cnstr_set(x_29, 3, x_7);
x_30 = lean::apply_1(x_25, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
}
obj* l_Lean_Expander_assume_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_assume_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("ite");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Not");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expander_if_transform___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("dite");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* l_Lean_Expander_if_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_Term_if_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_5, 2);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 4);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 6);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_Lean_Expander_if_transform___closed__1;
x_15 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_14, x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_6);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_19 = lean::cnstr_get(x_6, 0);
x_20 = lean::cnstr_get(x_5, 2);
lean::inc(x_20);
x_21 = l_Lean_Parser_Term_lambda_HasView;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_19, 0);
lean::inc(x_23);
lean::dec(x_19);
x_24 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_25 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_26 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
lean::inc(x_20);
lean::inc(x_23);
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_23);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_27, 3, x_20);
lean::cnstr_set(x_27, 4, x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::cnstr_get(x_5, 4);
lean::inc(x_30);
x_31 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_32 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_32);
lean::cnstr_set(x_33, 3, x_30);
lean::inc(x_22);
x_34 = lean::apply_1(x_22, x_33);
x_35 = lean::box(0);
lean::inc(x_20);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_20);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Expander_if_transform___closed__2;
x_38 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_37, x_36);
x_39 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_39, 0, x_24);
lean::cnstr_set(x_39, 1, x_23);
lean::cnstr_set(x_39, 2, x_25);
lean::cnstr_set(x_39, 3, x_38);
lean::cnstr_set(x_39, 4, x_26);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::cnstr_get(x_5, 6);
lean::inc(x_42);
lean::dec(x_5);
x_43 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_43, 0, x_31);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set(x_43, 2, x_32);
lean::cnstr_set(x_43, 3, x_42);
x_44 = lean::apply_1(x_22, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_35);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_34);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Expander_if_transform___closed__3;
x_49 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_48, x_47);
lean::cnstr_set(x_6, 0, x_49);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_6);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_51 = lean::cnstr_get(x_6, 0);
lean::inc(x_51);
lean::dec(x_6);
x_52 = lean::cnstr_get(x_5, 2);
lean::inc(x_52);
x_53 = l_Lean_Parser_Term_lambda_HasView;
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_51, 0);
lean::inc(x_55);
lean::dec(x_51);
x_56 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_57 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_58 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
lean::inc(x_52);
lean::inc(x_55);
x_59 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_55);
lean::cnstr_set(x_59, 2, x_57);
lean::cnstr_set(x_59, 3, x_52);
lean::cnstr_set(x_59, 4, x_58);
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::cnstr_get(x_5, 4);
lean::inc(x_62);
x_63 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_64 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_65 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_61);
lean::cnstr_set(x_65, 2, x_64);
lean::cnstr_set(x_65, 3, x_62);
lean::inc(x_54);
x_66 = lean::apply_1(x_54, x_65);
x_67 = lean::box(0);
lean::inc(x_52);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_52);
lean::cnstr_set(x_68, 1, x_67);
x_69 = l_Lean_Expander_if_transform___closed__2;
x_70 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_69, x_68);
x_71 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_71, 0, x_56);
lean::cnstr_set(x_71, 1, x_55);
lean::cnstr_set(x_71, 2, x_57);
lean::cnstr_set(x_71, 3, x_70);
lean::cnstr_set(x_71, 4, x_58);
x_72 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::cnstr_get(x_5, 6);
lean::inc(x_74);
lean::dec(x_5);
x_75 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_75, 0, x_63);
lean::cnstr_set(x_75, 1, x_73);
lean::cnstr_set(x_75, 2, x_64);
lean::cnstr_set(x_75, 3, x_74);
x_76 = lean::apply_1(x_54, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_67);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_66);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_52);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_Lean_Expander_if_transform___closed__3;
x_81 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_80, x_79);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
}
}
}
obj* l_Lean_Expander_if_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_if_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_let_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_Term_hole_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::mk_string("_");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_1(x_7, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
obj* l_Lean_Expander_let_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_Term_let_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_8, 2);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_5);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_5, 1);
lean::dec(x_12);
x_13 = !lean::is_exclusive(x_8);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_8, 2);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_8, 1);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
x_17 = l_Lean_Expander_let_transform___closed__1;
lean::cnstr_set(x_8, 2, x_17);
x_18 = lean::apply_1(x_16, x_5);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_23 = l_Lean_Expander_let_transform___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_9);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set(x_6, 0, x_24);
x_25 = lean::apply_1(x_22, x_5);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_28 = lean::cnstr_get(x_5, 0);
x_29 = lean::cnstr_get(x_5, 2);
x_30 = lean::cnstr_get(x_5, 3);
x_31 = lean::cnstr_get(x_5, 4);
x_32 = lean::cnstr_get(x_5, 5);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_5);
x_33 = lean::cnstr_get(x_8, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_34 = x_8;
} else {
 lean::dec_ref(x_8);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_3, 1);
lean::inc(x_35);
x_36 = l_Lean_Expander_let_transform___closed__1;
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set(x_37, 1, x_9);
lean::cnstr_set(x_37, 2, x_36);
lean::cnstr_set(x_6, 0, x_37);
x_38 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set(x_38, 1, x_6);
lean::cnstr_set(x_38, 2, x_29);
lean::cnstr_set(x_38, 3, x_30);
lean::cnstr_set(x_38, 4, x_31);
lean::cnstr_set(x_38, 5, x_32);
x_39 = lean::apply_1(x_35, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
}
else
{
obj* x_42; 
lean::dec(x_10);
lean::free_heap_obj(x_6);
lean::dec(x_8);
lean::dec(x_5);
x_42 = l_Lean_Expander_noExpansion(x_2);
return x_42;
}
}
else
{
uint8 x_43; 
x_43 = !lean::is_exclusive(x_5);
if (x_43 == 0)
{
obj* x_44; obj* x_45; uint8 x_46; 
x_44 = lean::cnstr_get(x_5, 3);
x_45 = lean::cnstr_get(x_5, 1);
lean::dec(x_45);
x_46 = !lean::is_exclusive(x_8);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_47 = lean::cnstr_get(x_8, 2);
x_48 = lean::cnstr_get(x_8, 1);
lean::dec(x_48);
x_49 = lean::box(0);
x_50 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_9);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::cnstr_get(x_3, 1);
lean::inc(x_55);
x_56 = l_Lean_Parser_Term_pi_HasView;
x_57 = lean::cnstr_get(x_56, 1);
lean::inc(x_57);
x_58 = l_Lean_Expander_getOptType___main(x_47);
lean::dec(x_47);
x_59 = l_Lean_Expander_depArrow_transform___closed__1;
x_60 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::inc(x_54);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_54);
lean::cnstr_set(x_61, 2, x_60);
lean::cnstr_set(x_61, 3, x_58);
x_62 = lean::apply_1(x_57, x_61);
x_63 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_8, 2, x_65);
lean::cnstr_set(x_8, 1, x_49);
x_66 = l_Lean_Parser_Term_lambda_HasView;
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_68 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_54);
lean::cnstr_set(x_69, 2, x_60);
lean::cnstr_set(x_69, 3, x_44);
x_70 = lean::apply_1(x_67, x_69);
lean::cnstr_set(x_5, 3, x_70);
x_71 = lean::apply_1(x_55, x_5);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_74 = lean::cnstr_get(x_8, 0);
x_75 = lean::cnstr_get(x_8, 2);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_8);
x_76 = lean::box(0);
x_77 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_9);
x_78 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::cnstr_get(x_3, 1);
lean::inc(x_82);
x_83 = l_Lean_Parser_Term_pi_HasView;
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_85 = l_Lean_Expander_getOptType___main(x_75);
lean::dec(x_75);
x_86 = l_Lean_Expander_depArrow_transform___closed__1;
x_87 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::inc(x_81);
x_88 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_81);
lean::cnstr_set(x_88, 2, x_87);
lean::cnstr_set(x_88, 3, x_85);
x_89 = lean::apply_1(x_84, x_88);
x_90 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_93, 0, x_74);
lean::cnstr_set(x_93, 1, x_76);
lean::cnstr_set(x_93, 2, x_92);
lean::cnstr_set(x_6, 0, x_93);
x_94 = l_Lean_Parser_Term_lambda_HasView;
x_95 = lean::cnstr_get(x_94, 1);
lean::inc(x_95);
x_96 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_97 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_81);
lean::cnstr_set(x_97, 2, x_87);
lean::cnstr_set(x_97, 3, x_44);
x_98 = lean::apply_1(x_95, x_97);
lean::cnstr_set(x_5, 3, x_98);
x_99 = lean::apply_1(x_82, x_5);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_102 = lean::cnstr_get(x_5, 0);
x_103 = lean::cnstr_get(x_5, 2);
x_104 = lean::cnstr_get(x_5, 3);
x_105 = lean::cnstr_get(x_5, 4);
x_106 = lean::cnstr_get(x_5, 5);
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_5);
x_107 = lean::cnstr_get(x_8, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_8, 2);
lean::inc(x_108);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_109 = x_8;
} else {
 lean::dec_ref(x_8);
 x_109 = lean::box(0);
}
x_110 = lean::box(0);
x_111 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_9);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_113, 0, x_112);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_110);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_115, 0, x_114);
x_116 = lean::cnstr_get(x_3, 1);
lean::inc(x_116);
x_117 = l_Lean_Parser_Term_pi_HasView;
x_118 = lean::cnstr_get(x_117, 1);
lean::inc(x_118);
x_119 = l_Lean_Expander_getOptType___main(x_108);
lean::dec(x_108);
x_120 = l_Lean_Expander_depArrow_transform___closed__1;
x_121 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::inc(x_115);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_115);
lean::cnstr_set(x_122, 2, x_121);
lean::cnstr_set(x_122, 3, x_119);
x_123 = lean::apply_1(x_118, x_122);
x_124 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_123);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
if (lean::is_scalar(x_109)) {
 x_127 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_127 = x_109;
}
lean::cnstr_set(x_127, 0, x_107);
lean::cnstr_set(x_127, 1, x_110);
lean::cnstr_set(x_127, 2, x_126);
lean::cnstr_set(x_6, 0, x_127);
x_128 = l_Lean_Parser_Term_lambda_HasView;
x_129 = lean::cnstr_get(x_128, 1);
lean::inc(x_129);
x_130 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_131 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_115);
lean::cnstr_set(x_131, 2, x_121);
lean::cnstr_set(x_131, 3, x_104);
x_132 = lean::apply_1(x_129, x_131);
x_133 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_133, 0, x_102);
lean::cnstr_set(x_133, 1, x_6);
lean::cnstr_set(x_133, 2, x_103);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set(x_133, 4, x_105);
lean::cnstr_set(x_133, 5, x_106);
x_134 = lean::apply_1(x_116, x_133);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_134);
x_136 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_136, 0, x_135);
return x_136;
}
}
}
else
{
obj* x_137; obj* x_138; 
x_137 = lean::cnstr_get(x_6, 0);
lean::inc(x_137);
lean::dec(x_6);
x_138 = lean::cnstr_get(x_137, 1);
lean::inc(x_138);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; 
x_139 = lean::cnstr_get(x_137, 2);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_140 = lean::cnstr_get(x_5, 0);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_5, 2);
lean::inc(x_141);
x_142 = lean::cnstr_get(x_5, 3);
lean::inc(x_142);
x_143 = lean::cnstr_get(x_5, 4);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_5, 5);
lean::inc(x_144);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 lean::cnstr_release(x_5, 4);
 lean::cnstr_release(x_5, 5);
 x_145 = x_5;
} else {
 lean::dec_ref(x_5);
 x_145 = lean::box(0);
}
x_146 = lean::cnstr_get(x_137, 0);
lean::inc(x_146);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 lean::cnstr_release(x_137, 2);
 x_147 = x_137;
} else {
 lean::dec_ref(x_137);
 x_147 = lean::box(0);
}
x_148 = lean::cnstr_get(x_3, 1);
lean::inc(x_148);
x_149 = l_Lean_Expander_let_transform___closed__1;
if (lean::is_scalar(x_147)) {
 x_150 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_150 = x_147;
}
lean::cnstr_set(x_150, 0, x_146);
lean::cnstr_set(x_150, 1, x_138);
lean::cnstr_set(x_150, 2, x_149);
x_151 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
if (lean::is_scalar(x_145)) {
 x_152 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_152 = x_145;
}
lean::cnstr_set(x_152, 0, x_140);
lean::cnstr_set(x_152, 1, x_151);
lean::cnstr_set(x_152, 2, x_141);
lean::cnstr_set(x_152, 3, x_142);
lean::cnstr_set(x_152, 4, x_143);
lean::cnstr_set(x_152, 5, x_144);
x_153 = lean::apply_1(x_148, x_152);
x_154 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_154, 0, x_153);
x_155 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
return x_155;
}
else
{
obj* x_156; 
lean::dec(x_139);
lean::dec(x_137);
lean::dec(x_5);
x_156 = l_Lean_Expander_noExpansion(x_2);
return x_156;
}
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_157 = lean::cnstr_get(x_5, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_5, 2);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_5, 3);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_5, 4);
lean::inc(x_160);
x_161 = lean::cnstr_get(x_5, 5);
lean::inc(x_161);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 lean::cnstr_release(x_5, 4);
 lean::cnstr_release(x_5, 5);
 x_162 = x_5;
} else {
 lean::dec_ref(x_5);
 x_162 = lean::box(0);
}
x_163 = lean::cnstr_get(x_137, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_137, 2);
lean::inc(x_164);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 lean::cnstr_release(x_137, 2);
 x_165 = x_137;
} else {
 lean::dec_ref(x_137);
 x_165 = lean::box(0);
}
x_166 = lean::box(0);
x_167 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_138);
x_168 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_168, 0, x_167);
x_169 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_169, 0, x_168);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set(x_170, 1, x_169);
x_171 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
x_172 = lean::cnstr_get(x_3, 1);
lean::inc(x_172);
x_173 = l_Lean_Parser_Term_pi_HasView;
x_174 = lean::cnstr_get(x_173, 1);
lean::inc(x_174);
x_175 = l_Lean_Expander_getOptType___main(x_164);
lean::dec(x_164);
x_176 = l_Lean_Expander_depArrow_transform___closed__1;
x_177 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
lean::inc(x_171);
x_178 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_171);
lean::cnstr_set(x_178, 2, x_177);
lean::cnstr_set(x_178, 3, x_175);
x_179 = lean::apply_1(x_174, x_178);
x_180 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_181 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_179);
x_182 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_182, 0, x_181);
if (lean::is_scalar(x_165)) {
 x_183 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_183 = x_165;
}
lean::cnstr_set(x_183, 0, x_163);
lean::cnstr_set(x_183, 1, x_166);
lean::cnstr_set(x_183, 2, x_182);
x_184 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_184, 0, x_183);
x_185 = l_Lean_Parser_Term_lambda_HasView;
x_186 = lean::cnstr_get(x_185, 1);
lean::inc(x_186);
x_187 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_188 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_171);
lean::cnstr_set(x_188, 2, x_177);
lean::cnstr_set(x_188, 3, x_159);
x_189 = lean::apply_1(x_186, x_188);
if (lean::is_scalar(x_162)) {
 x_190 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_190 = x_162;
}
lean::cnstr_set(x_190, 0, x_157);
lean::cnstr_set(x_190, 1, x_184);
lean::cnstr_set(x_190, 2, x_158);
lean::cnstr_set(x_190, 3, x_189);
lean::cnstr_set(x_190, 4, x_160);
lean::cnstr_set(x_190, 5, x_161);
x_191 = lean::apply_1(x_172, x_190);
x_192 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_192, 0, x_191);
x_193 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_193, 0, x_192);
return x_193;
}
}
}
else
{
obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
x_194 = lean::cnstr_get(x_5, 3);
lean::inc(x_194);
x_195 = lean::cnstr_get(x_5, 5);
lean::inc(x_195);
lean::dec(x_5);
x_196 = lean::cnstr_get(x_6, 0);
lean::inc(x_196);
lean::dec(x_6);
x_197 = l_Lean_Parser_Term_match_HasView;
x_198 = lean::cnstr_get(x_197, 1);
lean::inc(x_198);
x_199 = lean::box(0);
x_200 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_200, 0, x_194);
lean::cnstr_set(x_200, 1, x_199);
x_201 = lean::box(0);
x_202 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_201);
x_203 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_203, 0, x_196);
lean::cnstr_set(x_203, 1, x_199);
x_204 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_201);
x_205 = l_Lean_Expander_mixfix_transform___closed__4;
x_206 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_206, 0, x_204);
lean::cnstr_set(x_206, 1, x_205);
lean::cnstr_set(x_206, 2, x_195);
x_207 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_199);
x_208 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_201);
x_209 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__1;
x_210 = l_List_mfoldr___main___at_Lean_Expander_expandBinders___spec__4___closed__3;
x_211 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_211, 0, x_209);
lean::cnstr_set(x_211, 1, x_202);
lean::cnstr_set(x_211, 2, x_199);
lean::cnstr_set(x_211, 3, x_210);
lean::cnstr_set(x_211, 4, x_199);
lean::cnstr_set(x_211, 5, x_208);
x_212 = lean::apply_1(x_198, x_211);
x_213 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_213, 0, x_212);
x_214 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_214, 0, x_213);
return x_214;
}
}
}
obj* l_Lean_Expander_let_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_let_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_axiom_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Expander_axiom_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Lean_Parser_command_axiom_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_5, 2);
lean::dec(x_9);
x_10 = !lean::is_exclusive(x_6);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_11 = lean::cnstr_get(x_6, 1);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_14 = lean::box(0);
x_15 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_3, 1);
lean::inc(x_20);
x_21 = l_Lean_Parser_Term_pi_HasView;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_11, 1);
lean::inc(x_23);
lean::dec(x_11);
x_24 = l_Lean_Expander_depArrow_transform___closed__1;
x_25 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_19);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set(x_26, 3, x_23);
x_27 = lean::apply_1(x_22, x_26);
x_28 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = l_Lean_Expander_axiom_transform___closed__1;
lean::cnstr_set(x_6, 1, x_29);
lean::cnstr_set(x_6, 0, x_30);
x_31 = lean::apply_1(x_20, x_5);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_34 = lean::cnstr_get(x_6, 1);
lean::inc(x_34);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_7, 0);
lean::inc(x_35);
lean::dec(x_7);
x_36 = lean::box(0);
x_37 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_35);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::cnstr_get(x_3, 1);
lean::inc(x_42);
x_43 = l_Lean_Parser_Term_pi_HasView;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_34, 1);
lean::inc(x_45);
lean::dec(x_34);
x_46 = l_Lean_Expander_depArrow_transform___closed__1;
x_47 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_41);
lean::cnstr_set(x_48, 2, x_47);
lean::cnstr_set(x_48, 3, x_45);
x_49 = lean::apply_1(x_44, x_48);
x_50 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_49);
x_52 = l_Lean_Expander_axiom_transform___closed__1;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
lean::cnstr_set(x_5, 2, x_53);
x_54 = lean::apply_1(x_42, x_5);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_57 = lean::cnstr_get(x_5, 0);
x_58 = lean::cnstr_get(x_5, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_5);
x_59 = lean::cnstr_get(x_6, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_60 = x_6;
} else {
 lean::dec_ref(x_6);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_7, 0);
lean::inc(x_61);
lean::dec(x_7);
x_62 = lean::box(0);
x_63 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_61);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::cnstr_get(x_3, 1);
lean::inc(x_68);
x_69 = l_Lean_Parser_Term_pi_HasView;
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_59, 1);
lean::inc(x_71);
lean::dec(x_59);
x_72 = l_Lean_Expander_depArrow_transform___closed__1;
x_73 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_67);
lean::cnstr_set(x_74, 2, x_73);
lean::cnstr_set(x_74, 3, x_71);
x_75 = lean::apply_1(x_70, x_74);
x_76 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_75);
x_78 = l_Lean_Expander_axiom_transform___closed__1;
if (lean::is_scalar(x_60)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_60;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_77);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_57);
lean::cnstr_set(x_80, 1, x_58);
lean::cnstr_set(x_80, 2, x_79);
x_81 = lean::apply_1(x_68, x_80);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
}
else
{
obj* x_84; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_84 = l_Lean_Expander_noExpansion(x_2);
return x_84;
}
}
}
obj* l_Lean_Expander_axiom_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_axiom_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_declaration_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::box(0);
x_2 = lean::mk_string("class");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
x_12 = lean::mk_string("@[");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::mk_string("]");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_8);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_15);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_19);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
obj* _init_l_Lean_Expander_declaration_transform___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("class");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_3);
lean::dec(x_5);
x_7 = l_Lean_Parser_Substring_ofString(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* _init_l_Lean_Expander_declaration_transform___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::mk_string("structure");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_Lean_Expander_declaration_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_command_declaration_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
switch (lean::obj_tag(x_6)) {
case 4:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::free_heap_obj(x_6);
lean::dec(x_8);
lean::dec(x_5);
x_10 = l_Lean_Expander_noExpansion(x_2);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_9, 0);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_14 = !lean::is_exclusive(x_8);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_8, 0);
lean::dec(x_15);
x_16 = !lean::is_exclusive(x_13);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 1);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
x_19 = lean::box(0);
lean::cnstr_set(x_8, 0, x_19);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = l_Lean_Expander_declaration_transform___closed__1;
lean::cnstr_set(x_13, 1, x_20);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_6);
x_22 = lean::apply_1(x_18, x_21);
lean::cnstr_set(x_9, 0, x_22);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_9);
return x_23;
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_17);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = lean::cnstr_get(x_17, 0);
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_25, 1);
x_28 = l_Lean_Expander_declaration_transform___closed__2;
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_25, 1, x_29);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_13);
lean::cnstr_set(x_30, 1, x_6);
x_31 = lean::apply_1(x_18, x_30);
lean::cnstr_set(x_9, 0, x_31);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_9);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_25, 0);
x_34 = lean::cnstr_get(x_25, 1);
x_35 = lean::cnstr_get(x_25, 2);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_25);
x_36 = l_Lean_Expander_declaration_transform___closed__2;
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_33);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set(x_38, 2, x_35);
lean::cnstr_set(x_17, 0, x_38);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_13);
lean::cnstr_set(x_39, 1, x_6);
x_40 = lean::apply_1(x_18, x_39);
lean::cnstr_set(x_9, 0, x_40);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_9);
return x_41;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_17, 0);
lean::inc(x_42);
lean::dec(x_17);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 lean::cnstr_release(x_42, 2);
 x_46 = x_42;
} else {
 lean::dec_ref(x_42);
 x_46 = lean::box(0);
}
x_47 = l_Lean_Expander_declaration_transform___closed__2;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_46;
}
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set(x_49, 2, x_45);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_13, 1, x_50);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_13);
lean::cnstr_set(x_51, 1, x_6);
x_52 = lean::apply_1(x_18, x_51);
lean::cnstr_set(x_9, 0, x_52);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_9);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_54 = lean::cnstr_get(x_13, 0);
x_55 = lean::cnstr_get(x_13, 1);
x_56 = lean::cnstr_get(x_13, 2);
x_57 = lean::cnstr_get(x_13, 3);
x_58 = lean::cnstr_get(x_13, 4);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_13);
x_59 = lean::cnstr_get(x_3, 1);
lean::inc(x_59);
x_60 = lean::box(0);
lean::cnstr_set(x_8, 0, x_60);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_61 = l_Lean_Expander_declaration_transform___closed__1;
x_62 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set(x_62, 2, x_56);
lean::cnstr_set(x_62, 3, x_57);
lean::cnstr_set(x_62, 4, x_58);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_6);
x_64 = lean::apply_1(x_59, x_63);
lean::cnstr_set(x_9, 0, x_64);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_9);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_66 = lean::cnstr_get(x_55, 0);
lean::inc(x_66);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_67 = x_55;
} else {
 lean::dec_ref(x_55);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_66, 2);
lean::inc(x_70);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 lean::cnstr_release(x_66, 2);
 x_71 = x_66;
} else {
 lean::dec_ref(x_66);
 x_71 = lean::box(0);
}
x_72 = l_Lean_Expander_declaration_transform___closed__2;
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_69);
if (lean::is_scalar(x_71)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_71;
}
lean::cnstr_set(x_74, 0, x_68);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set(x_74, 2, x_70);
if (lean::is_scalar(x_67)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_67;
}
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_76, 0, x_54);
lean::cnstr_set(x_76, 1, x_75);
lean::cnstr_set(x_76, 2, x_56);
lean::cnstr_set(x_76, 3, x_57);
lean::cnstr_set(x_76, 4, x_58);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_6);
x_78 = lean::apply_1(x_59, x_77);
lean::cnstr_set(x_9, 0, x_78);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_9);
return x_79;
}
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_80 = lean::cnstr_get(x_8, 1);
x_81 = lean::cnstr_get(x_8, 2);
x_82 = lean::cnstr_get(x_8, 3);
x_83 = lean::cnstr_get(x_8, 4);
x_84 = lean::cnstr_get(x_8, 5);
x_85 = lean::cnstr_get(x_8, 6);
lean::inc(x_85);
lean::inc(x_84);
lean::inc(x_83);
lean::inc(x_82);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_8);
x_86 = lean::cnstr_get(x_13, 0);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_13, 1);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_13, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_13, 3);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_13, 4);
lean::inc(x_90);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 lean::cnstr_release(x_13, 2);
 lean::cnstr_release(x_13, 3);
 lean::cnstr_release(x_13, 4);
 x_91 = x_13;
} else {
 lean::dec_ref(x_13);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_3, 1);
lean::inc(x_92);
x_93 = lean::box(0);
x_94 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_80);
lean::cnstr_set(x_94, 2, x_81);
lean::cnstr_set(x_94, 3, x_82);
lean::cnstr_set(x_94, 4, x_83);
lean::cnstr_set(x_94, 5, x_84);
lean::cnstr_set(x_94, 6, x_85);
lean::cnstr_set(x_6, 0, x_94);
if (lean::obj_tag(x_87) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_95 = l_Lean_Expander_declaration_transform___closed__1;
if (lean::is_scalar(x_91)) {
 x_96 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_96 = x_91;
}
lean::cnstr_set(x_96, 0, x_86);
lean::cnstr_set(x_96, 1, x_95);
lean::cnstr_set(x_96, 2, x_88);
lean::cnstr_set(x_96, 3, x_89);
lean::cnstr_set(x_96, 4, x_90);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_6);
x_98 = lean::apply_1(x_92, x_97);
lean::cnstr_set(x_9, 0, x_98);
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_9);
return x_99;
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_100 = lean::cnstr_get(x_87, 0);
lean::inc(x_100);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_101 = x_87;
} else {
 lean::dec_ref(x_87);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_100, 2);
lean::inc(x_104);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 lean::cnstr_release(x_100, 1);
 lean::cnstr_release(x_100, 2);
 x_105 = x_100;
} else {
 lean::dec_ref(x_100);
 x_105 = lean::box(0);
}
x_106 = l_Lean_Expander_declaration_transform___closed__2;
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
if (lean::is_scalar(x_105)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_105;
}
lean::cnstr_set(x_108, 0, x_102);
lean::cnstr_set(x_108, 1, x_107);
lean::cnstr_set(x_108, 2, x_104);
if (lean::is_scalar(x_101)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_101;
}
lean::cnstr_set(x_109, 0, x_108);
if (lean::is_scalar(x_91)) {
 x_110 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_110 = x_91;
}
lean::cnstr_set(x_110, 0, x_86);
lean::cnstr_set(x_110, 1, x_109);
lean::cnstr_set(x_110, 2, x_88);
lean::cnstr_set(x_110, 3, x_89);
lean::cnstr_set(x_110, 4, x_90);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_6);
x_112 = lean::apply_1(x_92, x_111);
lean::cnstr_set(x_9, 0, x_112);
x_113 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_113, 0, x_9);
return x_113;
}
}
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_9);
x_114 = lean::cnstr_get(x_5, 0);
lean::inc(x_114);
lean::dec(x_5);
x_115 = lean::cnstr_get(x_8, 1);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_8, 2);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_8, 3);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_8, 4);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_8, 5);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_8, 6);
lean::inc(x_120);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 lean::cnstr_release(x_8, 4);
 lean::cnstr_release(x_8, 5);
 lean::cnstr_release(x_8, 6);
 x_121 = x_8;
} else {
 lean::dec_ref(x_8);
 x_121 = lean::box(0);
}
x_122 = lean::cnstr_get(x_114, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_114, 1);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_114, 2);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_114, 3);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_114, 4);
lean::inc(x_126);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 lean::cnstr_release(x_114, 1);
 lean::cnstr_release(x_114, 2);
 lean::cnstr_release(x_114, 3);
 lean::cnstr_release(x_114, 4);
 x_127 = x_114;
} else {
 lean::dec_ref(x_114);
 x_127 = lean::box(0);
}
x_128 = lean::cnstr_get(x_3, 1);
lean::inc(x_128);
x_129 = lean::box(0);
if (lean::is_scalar(x_121)) {
 x_130 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_130 = x_121;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_115);
lean::cnstr_set(x_130, 2, x_116);
lean::cnstr_set(x_130, 3, x_117);
lean::cnstr_set(x_130, 4, x_118);
lean::cnstr_set(x_130, 5, x_119);
lean::cnstr_set(x_130, 6, x_120);
lean::cnstr_set(x_6, 0, x_130);
if (lean::obj_tag(x_123) == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_131 = l_Lean_Expander_declaration_transform___closed__1;
if (lean::is_scalar(x_127)) {
 x_132 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_132 = x_127;
}
lean::cnstr_set(x_132, 0, x_122);
lean::cnstr_set(x_132, 1, x_131);
lean::cnstr_set(x_132, 2, x_124);
lean::cnstr_set(x_132, 3, x_125);
lean::cnstr_set(x_132, 4, x_126);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_6);
x_134 = lean::apply_1(x_128, x_133);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_134);
x_136 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_136, 0, x_135);
return x_136;
}
else
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_137 = lean::cnstr_get(x_123, 0);
lean::inc(x_137);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_138 = x_123;
} else {
 lean::dec_ref(x_123);
 x_138 = lean::box(0);
}
x_139 = lean::cnstr_get(x_137, 0);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_137, 2);
lean::inc(x_141);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 lean::cnstr_release(x_137, 2);
 x_142 = x_137;
} else {
 lean::dec_ref(x_137);
 x_142 = lean::box(0);
}
x_143 = l_Lean_Expander_declaration_transform___closed__2;
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_140);
if (lean::is_scalar(x_142)) {
 x_145 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_145 = x_142;
}
lean::cnstr_set(x_145, 0, x_139);
lean::cnstr_set(x_145, 1, x_144);
lean::cnstr_set(x_145, 2, x_141);
if (lean::is_scalar(x_138)) {
 x_146 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_146 = x_138;
}
lean::cnstr_set(x_146, 0, x_145);
if (lean::is_scalar(x_127)) {
 x_147 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_147 = x_127;
}
lean::cnstr_set(x_147, 0, x_122);
lean::cnstr_set(x_147, 1, x_146);
lean::cnstr_set(x_147, 2, x_124);
lean::cnstr_set(x_147, 3, x_125);
lean::cnstr_set(x_147, 4, x_126);
x_148 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_6);
x_149 = lean::apply_1(x_128, x_148);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
}
}
else
{
obj* x_152; obj* x_153; 
x_152 = lean::cnstr_get(x_6, 0);
lean::inc(x_152);
lean::dec(x_6);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
if (lean::obj_tag(x_153) == 0)
{
obj* x_154; 
lean::dec(x_152);
lean::dec(x_5);
x_154 = l_Lean_Expander_noExpansion(x_2);
return x_154;
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_155 = x_153;
} else {
 lean::dec_ref(x_153);
 x_155 = lean::box(0);
}
x_156 = lean::cnstr_get(x_5, 0);
lean::inc(x_156);
lean::dec(x_5);
x_157 = lean::cnstr_get(x_152, 1);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_152, 2);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_152, 3);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_152, 4);
lean::inc(x_160);
x_161 = lean::cnstr_get(x_152, 5);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_152, 6);
lean::inc(x_162);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 lean::cnstr_release(x_152, 2);
 lean::cnstr_release(x_152, 3);
 lean::cnstr_release(x_152, 4);
 lean::cnstr_release(x_152, 5);
 lean::cnstr_release(x_152, 6);
 x_163 = x_152;
} else {
 lean::dec_ref(x_152);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_156, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_156, 1);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_156, 2);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_156, 3);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_156, 4);
lean::inc(x_168);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 lean::cnstr_release(x_156, 2);
 lean::cnstr_release(x_156, 3);
 lean::cnstr_release(x_156, 4);
 x_169 = x_156;
} else {
 lean::dec_ref(x_156);
 x_169 = lean::box(0);
}
x_170 = lean::cnstr_get(x_3, 1);
lean::inc(x_170);
x_171 = lean::box(0);
if (lean::is_scalar(x_163)) {
 x_172 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_172 = x_163;
}
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_157);
lean::cnstr_set(x_172, 2, x_158);
lean::cnstr_set(x_172, 3, x_159);
lean::cnstr_set(x_172, 4, x_160);
lean::cnstr_set(x_172, 5, x_161);
lean::cnstr_set(x_172, 6, x_162);
x_173 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_173, 0, x_172);
if (lean::obj_tag(x_165) == 0)
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_174 = l_Lean_Expander_declaration_transform___closed__1;
if (lean::is_scalar(x_169)) {
 x_175 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_175 = x_169;
}
lean::cnstr_set(x_175, 0, x_164);
lean::cnstr_set(x_175, 1, x_174);
lean::cnstr_set(x_175, 2, x_166);
lean::cnstr_set(x_175, 3, x_167);
lean::cnstr_set(x_175, 4, x_168);
x_176 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_176, 0, x_175);
lean::cnstr_set(x_176, 1, x_173);
x_177 = lean::apply_1(x_170, x_176);
if (lean::is_scalar(x_155)) {
 x_178 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_178 = x_155;
}
lean::cnstr_set(x_178, 0, x_177);
x_179 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_179, 0, x_178);
return x_179;
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_180 = lean::cnstr_get(x_165, 0);
lean::inc(x_180);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 x_181 = x_165;
} else {
 lean::dec_ref(x_165);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_180, 0);
lean::inc(x_182);
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
x_184 = lean::cnstr_get(x_180, 2);
lean::inc(x_184);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 lean::cnstr_release(x_180, 2);
 x_185 = x_180;
} else {
 lean::dec_ref(x_180);
 x_185 = lean::box(0);
}
x_186 = l_Lean_Expander_declaration_transform___closed__2;
x_187 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_183);
if (lean::is_scalar(x_185)) {
 x_188 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_188 = x_185;
}
lean::cnstr_set(x_188, 0, x_182);
lean::cnstr_set(x_188, 1, x_187);
lean::cnstr_set(x_188, 2, x_184);
if (lean::is_scalar(x_181)) {
 x_189 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_189 = x_181;
}
lean::cnstr_set(x_189, 0, x_188);
if (lean::is_scalar(x_169)) {
 x_190 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_190 = x_169;
}
lean::cnstr_set(x_190, 0, x_164);
lean::cnstr_set(x_190, 1, x_189);
lean::cnstr_set(x_190, 2, x_166);
lean::cnstr_set(x_190, 3, x_167);
lean::cnstr_set(x_190, 4, x_168);
x_191 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_173);
x_192 = lean::apply_1(x_170, x_191);
if (lean::is_scalar(x_155)) {
 x_193 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_193 = x_155;
}
lean::cnstr_set(x_193, 0, x_192);
x_194 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_194, 0, x_193);
return x_194;
}
}
}
}
case 5:
{
uint8 x_195; 
x_195 = !lean::is_exclusive(x_6);
if (x_195 == 0)
{
obj* x_196; obj* x_197; 
x_196 = lean::cnstr_get(x_6, 0);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; 
lean::dec(x_197);
lean::free_heap_obj(x_6);
lean::dec(x_196);
lean::dec(x_5);
x_198 = l_Lean_Expander_noExpansion(x_2);
return x_198;
}
else
{
obj* x_199; uint8 x_200; 
lean::dec(x_197);
x_199 = lean::cnstr_get(x_5, 0);
lean::inc(x_199);
lean::dec(x_5);
x_200 = !lean::is_exclusive(x_196);
if (x_200 == 0)
{
obj* x_201; uint8 x_202; 
x_201 = lean::cnstr_get(x_196, 0);
lean::dec(x_201);
x_202 = !lean::is_exclusive(x_199);
if (x_202 == 0)
{
obj* x_203; obj* x_204; obj* x_205; 
x_203 = lean::cnstr_get(x_199, 1);
x_204 = lean::cnstr_get(x_3, 1);
lean::inc(x_204);
x_205 = l_Lean_Expander_declaration_transform___closed__3;
lean::cnstr_set(x_196, 0, x_205);
if (lean::obj_tag(x_203) == 0)
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_206 = l_Lean_Expander_declaration_transform___closed__1;
lean::cnstr_set(x_199, 1, x_206);
x_207 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_207, 0, x_199);
lean::cnstr_set(x_207, 1, x_6);
x_208 = lean::apply_1(x_204, x_207);
x_209 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_209, 0, x_208);
x_210 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_210, 0, x_209);
return x_210;
}
else
{
uint8 x_211; 
x_211 = !lean::is_exclusive(x_203);
if (x_211 == 0)
{
obj* x_212; uint8 x_213; 
x_212 = lean::cnstr_get(x_203, 0);
x_213 = !lean::is_exclusive(x_212);
if (x_213 == 0)
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_214 = lean::cnstr_get(x_212, 1);
x_215 = l_Lean_Expander_declaration_transform___closed__2;
x_216 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_216, 0, x_215);
lean::cnstr_set(x_216, 1, x_214);
lean::cnstr_set(x_212, 1, x_216);
x_217 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_217, 0, x_199);
lean::cnstr_set(x_217, 1, x_6);
x_218 = lean::apply_1(x_204, x_217);
x_219 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_219, 0, x_218);
x_220 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_220, 0, x_219);
return x_220;
}
else
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; 
x_221 = lean::cnstr_get(x_212, 0);
x_222 = lean::cnstr_get(x_212, 1);
x_223 = lean::cnstr_get(x_212, 2);
lean::inc(x_223);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_212);
x_224 = l_Lean_Expander_declaration_transform___closed__2;
x_225 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_225, 0, x_224);
lean::cnstr_set(x_225, 1, x_222);
x_226 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_226, 0, x_221);
lean::cnstr_set(x_226, 1, x_225);
lean::cnstr_set(x_226, 2, x_223);
lean::cnstr_set(x_203, 0, x_226);
x_227 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_227, 0, x_199);
lean::cnstr_set(x_227, 1, x_6);
x_228 = lean::apply_1(x_204, x_227);
x_229 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_229, 0, x_228);
x_230 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_230, 0, x_229);
return x_230;
}
}
else
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
x_231 = lean::cnstr_get(x_203, 0);
lean::inc(x_231);
lean::dec(x_203);
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_233 = lean::cnstr_get(x_231, 1);
lean::inc(x_233);
x_234 = lean::cnstr_get(x_231, 2);
lean::inc(x_234);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 lean::cnstr_release(x_231, 2);
 x_235 = x_231;
} else {
 lean::dec_ref(x_231);
 x_235 = lean::box(0);
}
x_236 = l_Lean_Expander_declaration_transform___closed__2;
x_237 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_233);
if (lean::is_scalar(x_235)) {
 x_238 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_238 = x_235;
}
lean::cnstr_set(x_238, 0, x_232);
lean::cnstr_set(x_238, 1, x_237);
lean::cnstr_set(x_238, 2, x_234);
x_239 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_199, 1, x_239);
x_240 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_240, 0, x_199);
lean::cnstr_set(x_240, 1, x_6);
x_241 = lean::apply_1(x_204, x_240);
x_242 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_242, 0, x_241);
x_243 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_243, 0, x_242);
return x_243;
}
}
}
else
{
obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_244 = lean::cnstr_get(x_199, 0);
x_245 = lean::cnstr_get(x_199, 1);
x_246 = lean::cnstr_get(x_199, 2);
x_247 = lean::cnstr_get(x_199, 3);
x_248 = lean::cnstr_get(x_199, 4);
lean::inc(x_248);
lean::inc(x_247);
lean::inc(x_246);
lean::inc(x_245);
lean::inc(x_244);
lean::dec(x_199);
x_249 = lean::cnstr_get(x_3, 1);
lean::inc(x_249);
x_250 = l_Lean_Expander_declaration_transform___closed__3;
lean::cnstr_set(x_196, 0, x_250);
if (lean::obj_tag(x_245) == 0)
{
obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
x_251 = l_Lean_Expander_declaration_transform___closed__1;
x_252 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_252, 0, x_244);
lean::cnstr_set(x_252, 1, x_251);
lean::cnstr_set(x_252, 2, x_246);
lean::cnstr_set(x_252, 3, x_247);
lean::cnstr_set(x_252, 4, x_248);
x_253 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_253, 0, x_252);
lean::cnstr_set(x_253, 1, x_6);
x_254 = lean::apply_1(x_249, x_253);
x_255 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_255, 0, x_254);
x_256 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_256, 0, x_255);
return x_256;
}
else
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_257 = lean::cnstr_get(x_245, 0);
lean::inc(x_257);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_release(x_245, 0);
 x_258 = x_245;
} else {
 lean::dec_ref(x_245);
 x_258 = lean::box(0);
}
x_259 = lean::cnstr_get(x_257, 0);
lean::inc(x_259);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_257, 2);
lean::inc(x_261);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 lean::cnstr_release(x_257, 2);
 x_262 = x_257;
} else {
 lean::dec_ref(x_257);
 x_262 = lean::box(0);
}
x_263 = l_Lean_Expander_declaration_transform___closed__2;
x_264 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_264, 0, x_263);
lean::cnstr_set(x_264, 1, x_260);
if (lean::is_scalar(x_262)) {
 x_265 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_265 = x_262;
}
lean::cnstr_set(x_265, 0, x_259);
lean::cnstr_set(x_265, 1, x_264);
lean::cnstr_set(x_265, 2, x_261);
if (lean::is_scalar(x_258)) {
 x_266 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_266 = x_258;
}
lean::cnstr_set(x_266, 0, x_265);
x_267 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_267, 0, x_244);
lean::cnstr_set(x_267, 1, x_266);
lean::cnstr_set(x_267, 2, x_246);
lean::cnstr_set(x_267, 3, x_247);
lean::cnstr_set(x_267, 4, x_248);
x_268 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_6);
x_269 = lean::apply_1(x_249, x_268);
x_270 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_270, 0, x_269);
x_271 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_271, 0, x_270);
return x_271;
}
}
}
else
{
obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
x_272 = lean::cnstr_get(x_196, 1);
x_273 = lean::cnstr_get(x_196, 2);
x_274 = lean::cnstr_get(x_196, 3);
x_275 = lean::cnstr_get(x_196, 4);
x_276 = lean::cnstr_get(x_196, 5);
x_277 = lean::cnstr_get(x_196, 6);
x_278 = lean::cnstr_get(x_196, 7);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::inc(x_275);
lean::inc(x_274);
lean::inc(x_273);
lean::inc(x_272);
lean::dec(x_196);
x_279 = lean::cnstr_get(x_199, 0);
lean::inc(x_279);
x_280 = lean::cnstr_get(x_199, 1);
lean::inc(x_280);
x_281 = lean::cnstr_get(x_199, 2);
lean::inc(x_281);
x_282 = lean::cnstr_get(x_199, 3);
lean::inc(x_282);
x_283 = lean::cnstr_get(x_199, 4);
lean::inc(x_283);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_release(x_199, 0);
 lean::cnstr_release(x_199, 1);
 lean::cnstr_release(x_199, 2);
 lean::cnstr_release(x_199, 3);
 lean::cnstr_release(x_199, 4);
 x_284 = x_199;
} else {
 lean::dec_ref(x_199);
 x_284 = lean::box(0);
}
x_285 = lean::cnstr_get(x_3, 1);
lean::inc(x_285);
x_286 = l_Lean_Expander_declaration_transform___closed__3;
x_287 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_272);
lean::cnstr_set(x_287, 2, x_273);
lean::cnstr_set(x_287, 3, x_274);
lean::cnstr_set(x_287, 4, x_275);
lean::cnstr_set(x_287, 5, x_276);
lean::cnstr_set(x_287, 6, x_277);
lean::cnstr_set(x_287, 7, x_278);
lean::cnstr_set(x_6, 0, x_287);
if (lean::obj_tag(x_280) == 0)
{
obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_288 = l_Lean_Expander_declaration_transform___closed__1;
if (lean::is_scalar(x_284)) {
 x_289 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_289 = x_284;
}
lean::cnstr_set(x_289, 0, x_279);
lean::cnstr_set(x_289, 1, x_288);
lean::cnstr_set(x_289, 2, x_281);
lean::cnstr_set(x_289, 3, x_282);
lean::cnstr_set(x_289, 4, x_283);
x_290 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_6);
x_291 = lean::apply_1(x_285, x_290);
x_292 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_292, 0, x_291);
x_293 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_293, 0, x_292);
return x_293;
}
else
{
obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; 
x_294 = lean::cnstr_get(x_280, 0);
lean::inc(x_294);
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 x_295 = x_280;
} else {
 lean::dec_ref(x_280);
 x_295 = lean::box(0);
}
x_296 = lean::cnstr_get(x_294, 0);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_294, 2);
lean::inc(x_298);
if (lean::is_exclusive(x_294)) {
 lean::cnstr_release(x_294, 0);
 lean::cnstr_release(x_294, 1);
 lean::cnstr_release(x_294, 2);
 x_299 = x_294;
} else {
 lean::dec_ref(x_294);
 x_299 = lean::box(0);
}
x_300 = l_Lean_Expander_declaration_transform___closed__2;
x_301 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_301, 0, x_300);
lean::cnstr_set(x_301, 1, x_297);
if (lean::is_scalar(x_299)) {
 x_302 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_302 = x_299;
}
lean::cnstr_set(x_302, 0, x_296);
lean::cnstr_set(x_302, 1, x_301);
lean::cnstr_set(x_302, 2, x_298);
if (lean::is_scalar(x_295)) {
 x_303 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_303 = x_295;
}
lean::cnstr_set(x_303, 0, x_302);
if (lean::is_scalar(x_284)) {
 x_304 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_304 = x_284;
}
lean::cnstr_set(x_304, 0, x_279);
lean::cnstr_set(x_304, 1, x_303);
lean::cnstr_set(x_304, 2, x_281);
lean::cnstr_set(x_304, 3, x_282);
lean::cnstr_set(x_304, 4, x_283);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_6);
x_306 = lean::apply_1(x_285, x_305);
x_307 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_307, 0, x_306);
x_308 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_308, 0, x_307);
return x_308;
}
}
}
}
else
{
obj* x_309; obj* x_310; 
x_309 = lean::cnstr_get(x_6, 0);
lean::inc(x_309);
lean::dec(x_6);
x_310 = lean::cnstr_get(x_309, 0);
lean::inc(x_310);
if (lean::obj_tag(x_310) == 0)
{
obj* x_311; 
lean::dec(x_310);
lean::dec(x_309);
lean::dec(x_5);
x_311 = l_Lean_Expander_noExpansion(x_2);
return x_311;
}
else
{
obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_310);
x_312 = lean::cnstr_get(x_5, 0);
lean::inc(x_312);
lean::dec(x_5);
x_313 = lean::cnstr_get(x_309, 1);
lean::inc(x_313);
x_314 = lean::cnstr_get(x_309, 2);
lean::inc(x_314);
x_315 = lean::cnstr_get(x_309, 3);
lean::inc(x_315);
x_316 = lean::cnstr_get(x_309, 4);
lean::inc(x_316);
x_317 = lean::cnstr_get(x_309, 5);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_309, 6);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_309, 7);
lean::inc(x_319);
if (lean::is_exclusive(x_309)) {
 lean::cnstr_release(x_309, 0);
 lean::cnstr_release(x_309, 1);
 lean::cnstr_release(x_309, 2);
 lean::cnstr_release(x_309, 3);
 lean::cnstr_release(x_309, 4);
 lean::cnstr_release(x_309, 5);
 lean::cnstr_release(x_309, 6);
 lean::cnstr_release(x_309, 7);
 x_320 = x_309;
} else {
 lean::dec_ref(x_309);
 x_320 = lean::box(0);
}
x_321 = lean::cnstr_get(x_312, 0);
lean::inc(x_321);
x_322 = lean::cnstr_get(x_312, 1);
lean::inc(x_322);
x_323 = lean::cnstr_get(x_312, 2);
lean::inc(x_323);
x_324 = lean::cnstr_get(x_312, 3);
lean::inc(x_324);
x_325 = lean::cnstr_get(x_312, 4);
lean::inc(x_325);
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 lean::cnstr_release(x_312, 2);
 lean::cnstr_release(x_312, 3);
 lean::cnstr_release(x_312, 4);
 x_326 = x_312;
} else {
 lean::dec_ref(x_312);
 x_326 = lean::box(0);
}
x_327 = lean::cnstr_get(x_3, 1);
lean::inc(x_327);
x_328 = l_Lean_Expander_declaration_transform___closed__3;
if (lean::is_scalar(x_320)) {
 x_329 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_329 = x_320;
}
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_313);
lean::cnstr_set(x_329, 2, x_314);
lean::cnstr_set(x_329, 3, x_315);
lean::cnstr_set(x_329, 4, x_316);
lean::cnstr_set(x_329, 5, x_317);
lean::cnstr_set(x_329, 6, x_318);
lean::cnstr_set(x_329, 7, x_319);
x_330 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_330, 0, x_329);
if (lean::obj_tag(x_322) == 0)
{
obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_331 = l_Lean_Expander_declaration_transform___closed__1;
if (lean::is_scalar(x_326)) {
 x_332 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_332 = x_326;
}
lean::cnstr_set(x_332, 0, x_321);
lean::cnstr_set(x_332, 1, x_331);
lean::cnstr_set(x_332, 2, x_323);
lean::cnstr_set(x_332, 3, x_324);
lean::cnstr_set(x_332, 4, x_325);
x_333 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_330);
x_334 = lean::apply_1(x_327, x_333);
x_335 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_335, 0, x_334);
x_336 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_336, 0, x_335);
return x_336;
}
else
{
obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
x_337 = lean::cnstr_get(x_322, 0);
lean::inc(x_337);
if (lean::is_exclusive(x_322)) {
 lean::cnstr_release(x_322, 0);
 x_338 = x_322;
} else {
 lean::dec_ref(x_322);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_337, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_337, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_337, 2);
lean::inc(x_341);
if (lean::is_exclusive(x_337)) {
 lean::cnstr_release(x_337, 0);
 lean::cnstr_release(x_337, 1);
 lean::cnstr_release(x_337, 2);
 x_342 = x_337;
} else {
 lean::dec_ref(x_337);
 x_342 = lean::box(0);
}
x_343 = l_Lean_Expander_declaration_transform___closed__2;
x_344 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_344, 0, x_343);
lean::cnstr_set(x_344, 1, x_340);
if (lean::is_scalar(x_342)) {
 x_345 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_345 = x_342;
}
lean::cnstr_set(x_345, 0, x_339);
lean::cnstr_set(x_345, 1, x_344);
lean::cnstr_set(x_345, 2, x_341);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_345);
if (lean::is_scalar(x_326)) {
 x_347 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_347 = x_326;
}
lean::cnstr_set(x_347, 0, x_321);
lean::cnstr_set(x_347, 1, x_346);
lean::cnstr_set(x_347, 2, x_323);
lean::cnstr_set(x_347, 3, x_324);
lean::cnstr_set(x_347, 4, x_325);
x_348 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_348, 0, x_347);
lean::cnstr_set(x_348, 1, x_330);
x_349 = lean::apply_1(x_327, x_348);
x_350 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_350, 0, x_349);
x_351 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_351, 0, x_350);
return x_351;
}
}
}
}
default: 
{
obj* x_352; 
lean::dec(x_6);
lean::dec(x_5);
x_352 = l_Lean_Expander_noExpansion(x_2);
return x_352;
}
}
}
}
obj* l_Lean_Expander_declaration_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_declaration_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_introRule_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Lean_Parser_command_introRule_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 3);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 1);
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; 
lean::free_heap_obj(x_6);
lean::dec(x_7);
lean::dec(x_5);
x_11 = l_Lean_Expander_noExpansion(x_2);
return x_11;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_5, 3);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
x_15 = !lean::is_exclusive(x_9);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_16 = lean::cnstr_get(x_9, 0);
x_17 = lean::box(0);
x_18 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_14);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_9, 0, x_19);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_9);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_23 = l_Lean_Parser_Term_pi_HasView;
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_16, 1);
lean::inc(x_25);
lean::dec(x_16);
x_26 = l_Lean_Expander_depArrow_transform___closed__1;
x_27 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_28 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_27);
lean::cnstr_set(x_28, 3, x_25);
x_29 = lean::apply_1(x_24, x_28);
x_30 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = l_Lean_Expander_axiom_transform___closed__1;
lean::cnstr_set(x_6, 1, x_32);
lean::cnstr_set(x_6, 0, x_33);
x_34 = lean::apply_1(x_22, x_5);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_37 = lean::cnstr_get(x_9, 0);
lean::inc(x_37);
lean::dec(x_9);
x_38 = lean::box(0);
x_39 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_14);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::cnstr_get(x_3, 1);
lean::inc(x_44);
x_45 = l_Lean_Parser_Term_pi_HasView;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_37, 1);
lean::inc(x_47);
lean::dec(x_37);
x_48 = l_Lean_Expander_depArrow_transform___closed__1;
x_49 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_50 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
lean::cnstr_set(x_50, 3, x_47);
x_51 = lean::apply_1(x_46, x_50);
x_52 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = l_Lean_Expander_axiom_transform___closed__1;
lean::cnstr_set(x_6, 1, x_54);
lean::cnstr_set(x_6, 0, x_55);
x_56 = lean::apply_1(x_44, x_5);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_59 = lean::cnstr_get(x_5, 0);
x_60 = lean::cnstr_get(x_5, 1);
x_61 = lean::cnstr_get(x_5, 2);
lean::inc(x_61);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_5);
x_62 = lean::cnstr_get(x_7, 0);
lean::inc(x_62);
lean::dec(x_7);
x_63 = lean::cnstr_get(x_9, 0);
lean::inc(x_63);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_64 = x_9;
} else {
 lean::dec_ref(x_9);
 x_64 = lean::box(0);
}
x_65 = lean::box(0);
x_66 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_62);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
if (lean::is_scalar(x_64)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_64;
}
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::cnstr_get(x_3, 1);
lean::inc(x_71);
x_72 = l_Lean_Parser_Term_pi_HasView;
x_73 = lean::cnstr_get(x_72, 1);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_63, 1);
lean::inc(x_74);
lean::dec(x_63);
x_75 = l_Lean_Expander_depArrow_transform___closed__1;
x_76 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_76);
lean::cnstr_set(x_77, 3, x_74);
x_78 = lean::apply_1(x_73, x_77);
x_79 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = l_Lean_Expander_axiom_transform___closed__1;
lean::cnstr_set(x_6, 1, x_81);
lean::cnstr_set(x_6, 0, x_82);
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_59);
lean::cnstr_set(x_83, 1, x_60);
lean::cnstr_set(x_83, 2, x_61);
lean::cnstr_set(x_83, 3, x_6);
x_84 = lean::apply_1(x_71, x_83);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
obj* x_87; 
x_87 = lean::cnstr_get(x_6, 1);
lean::inc(x_87);
lean::dec(x_6);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; 
lean::dec(x_7);
lean::dec(x_5);
x_88 = l_Lean_Expander_noExpansion(x_2);
return x_88;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_89 = lean::cnstr_get(x_5, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_5, 1);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_5, 2);
lean::inc(x_91);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_92 = x_5;
} else {
 lean::dec_ref(x_5);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_7, 0);
lean::inc(x_93);
lean::dec(x_7);
x_94 = lean::cnstr_get(x_87, 0);
lean::inc(x_94);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_95 = x_87;
} else {
 lean::dec_ref(x_87);
 x_95 = lean::box(0);
}
x_96 = lean::box(0);
x_97 = l_List_map___main___at_Lean_Expander_depArrow_transform___spec__2(x_93);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
if (lean::is_scalar(x_95)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_95;
}
lean::cnstr_set(x_99, 0, x_98);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
x_102 = lean::cnstr_get(x_3, 1);
lean::inc(x_102);
x_103 = l_Lean_Parser_Term_pi_HasView;
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_94, 1);
lean::inc(x_105);
lean::dec(x_94);
x_106 = l_Lean_Expander_depArrow_transform___closed__1;
x_107 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_101);
lean::cnstr_set(x_108, 2, x_107);
lean::cnstr_set(x_108, 3, x_105);
x_109 = lean::apply_1(x_104, x_108);
x_110 = l_Lean_Expander_mkSimpleBinder___closed__1;
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_109);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = l_Lean_Expander_axiom_transform___closed__1;
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_112);
if (lean::is_scalar(x_92)) {
 x_115 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_115 = x_92;
}
lean::cnstr_set(x_115, 0, x_89);
lean::cnstr_set(x_115, 1, x_90);
lean::cnstr_set(x_115, 2, x_91);
lean::cnstr_set(x_115, 3, x_114);
x_116 = lean::apply_1(x_102, x_115);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
obj* x_119; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_119 = l_Lean_Expander_noExpansion(x_2);
return x_119;
}
}
}
obj* l_Lean_Expander_introRule_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_introRule_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_variable_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("variables");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Expander_variable_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = l_Lean_Parser_command_variable_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = l_Lean_Parser_command_variables_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = lean::box(0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = l_Lean_Expander_variable_transform___closed__1;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::apply_1(x_7, x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
lean::dec(x_8);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = l_Lean_Expander_coeBinderBracketedBinder___closed__1;
x_21 = l_Lean_Expander_coeBinderBracketedBinder___closed__2;
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set(x_22, 2, x_21);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_9);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_Lean_Expander_variable_transform___closed__1;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::apply_1(x_7, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l_Lean_Expander_variable_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_variable_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Expander");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("bindingAnnotationUpdate");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Expander_bindingAnnotationUpdate;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
return x_5;
}
}
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1;
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
x_7 = l_Lean_Expander_bindingAnnotationUpdate;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
}
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
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
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Expander_bindingAnnotationUpdate_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::mk_string("dummy");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_TermParserM_Monad;
x_9 = l_Lean_Parser_TermParserM_MonadExcept;
x_10 = l_Lean_Parser_TermParserM_Lean_Parser_MonadParsec;
x_11 = l_Lean_Parser_TermParserM_Alternative;
x_12 = l_Lean_Expander_bindingAnnotationUpdate;
x_13 = l_Lean_Expander_bindingAnnotationUpdate_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::mk_string("dummy");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_NotationSpec_precedenceTerm_Parser_Lean_Parser_HasTokens___spec__1___boxed), 8, 3);
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
obj* l_Lean_Expander_bindingAnnotationUpdate_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Expander_bindingAnnotationUpdate;
x_7 = l_Lean_Expander_bindingAnnotationUpdate_Parser___closed__1;
x_8 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_NotationSpec_precedenceLit_Parser___spec__1(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::box(0);
x_2 = lean::mk_string(" : ");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_Lean_Expander_bindingAnnotationUpdate_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::mk_string("dummy");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_1(x_7, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = l_Lean_Expander_expandBracketedBinder___main___closed__4;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
} else {
 lean::dec_ref(x_1);
 x_6 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; 
lean::dec(x_24);
lean::dec(x_23);
x_25 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_25;
goto block_22;
}
else
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_24);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_24, 0);
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
x_29 = lean::cnstr_get(x_27, 2);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_4);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::cnstr_get(x_4, 0);
lean::dec(x_31);
x_32 = !lean::is_exclusive(x_23);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = lean::cnstr_get(x_23, 1);
lean::dec(x_33);
x_34 = !lean::is_exclusive(x_27);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_27, 2);
lean::dec(x_35);
x_36 = lean::cnstr_get(x_27, 1);
lean::dec(x_36);
x_37 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
lean::cnstr_set(x_27, 1, x_37);
x_38 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_38;
goto block_22;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
lean::dec(x_27);
x_40 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set(x_41, 2, x_29);
lean::cnstr_set(x_24, 0, x_41);
x_42 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_42;
goto block_22;
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_43 = lean::cnstr_get(x_23, 0);
x_44 = lean::cnstr_get(x_23, 2);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_23);
x_45 = lean::cnstr_get(x_27, 0);
lean::inc(x_45);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 lean::cnstr_release(x_27, 2);
 x_46 = x_27;
} else {
 lean::dec_ref(x_27);
 x_46 = lean::box(0);
}
x_47 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_29);
lean::cnstr_set(x_24, 0, x_48);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_24);
lean::cnstr_set(x_49, 2, x_44);
lean::cnstr_set(x_4, 0, x_49);
x_50 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_50;
goto block_22;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_4);
x_51 = lean::cnstr_get(x_23, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_23, 2);
lean::inc(x_52);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 lean::cnstr_release(x_23, 2);
 x_53 = x_23;
} else {
 lean::dec_ref(x_23);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_27, 0);
lean::inc(x_54);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 lean::cnstr_release(x_27, 2);
 x_55 = x_27;
} else {
 lean::dec_ref(x_27);
 x_55 = lean::box(0);
}
x_56 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set(x_57, 2, x_29);
lean::cnstr_set(x_24, 0, x_57);
if (lean::is_scalar(x_53)) {
 x_58 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_58 = x_53;
}
lean::cnstr_set(x_58, 0, x_51);
lean::cnstr_set(x_58, 1, x_24);
lean::cnstr_set(x_58, 2, x_52);
x_59 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = l_Lean_Expander_expandBracketedBinder___main(x_59, x_2);
x_7 = x_60;
goto block_22;
}
}
else
{
obj* x_61; 
lean::dec(x_29);
lean::free_heap_obj(x_24);
lean::dec(x_27);
lean::dec(x_23);
x_61 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_61;
goto block_22;
}
}
else
{
obj* x_62; 
lean::dec(x_28);
lean::free_heap_obj(x_24);
lean::dec(x_27);
lean::dec(x_23);
x_62 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_62;
goto block_22;
}
}
else
{
obj* x_63; obj* x_64; 
x_63 = lean::cnstr_get(x_24, 0);
lean::inc(x_63);
lean::dec(x_24);
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; 
x_65 = lean::cnstr_get(x_63, 2);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_66 = x_4;
} else {
 lean::dec_ref(x_4);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_23, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_23, 2);
lean::inc(x_68);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 lean::cnstr_release(x_23, 2);
 x_69 = x_23;
} else {
 lean::dec_ref(x_23);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_63, 0);
lean::inc(x_70);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 lean::cnstr_release(x_63, 2);
 x_71 = x_63;
} else {
 lean::dec_ref(x_63);
 x_71 = lean::box(0);
}
x_72 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_71)) {
 x_73 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_73 = x_71;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_72);
lean::cnstr_set(x_73, 2, x_65);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
if (lean::is_scalar(x_69)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_69;
}
lean::cnstr_set(x_75, 0, x_67);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set(x_75, 2, x_68);
if (lean::is_scalar(x_66)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_66;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = l_Lean_Expander_expandBracketedBinder___main(x_76, x_2);
x_7 = x_77;
goto block_22;
}
else
{
obj* x_78; 
lean::dec(x_65);
lean::dec(x_63);
lean::dec(x_23);
x_78 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_78;
goto block_22;
}
}
else
{
obj* x_79; 
lean::dec(x_64);
lean::dec(x_63);
lean::dec(x_23);
x_79 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_79;
goto block_22;
}
}
}
}
else
{
obj* x_80; 
x_80 = l_Lean_Expander_expandBracketedBinder___main(x_4, x_2);
x_7 = x_80;
goto block_22;
}
block_22:
{
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_6);
lean::dec(x_5);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_12 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_5, x_2);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
lean::dec(x_11);
lean::dec(x_6);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_12);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_scalar(x_6)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_6;
}
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_12, 0, x_18);
return x_12;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
if (lean::is_scalar(x_6)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_6;
}
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
}
}
obj* l_Lean_Expander_variables_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_command_variables_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_8, x_2);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
lean::free_heap_obj(x_6);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_9);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_9, 0);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
x_16 = l_List_join___main___rarg(x_14);
lean::cnstr_set_tag(x_6, 1);
lean::cnstr_set(x_6, 0, x_16);
x_17 = l_Lean_Expander_variable_transform___closed__1;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_6);
x_19 = lean::apply_1(x_15, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_9, 0, x_20);
return x_9;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_9, 0);
lean::inc(x_21);
lean::dec(x_9);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_23 = l_List_join___main___rarg(x_21);
lean::cnstr_set_tag(x_6, 1);
lean::cnstr_set(x_6, 0, x_23);
x_24 = l_Lean_Expander_variable_transform___closed__1;
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
x_26 = lean::apply_1(x_22, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_6, 0);
lean::inc(x_29);
lean::dec(x_6);
x_30 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_29, x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_32 = x_30;
} else {
 lean::dec_ref(x_30);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_35 = x_30;
} else {
 lean::dec_ref(x_30);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_3, 1);
lean::inc(x_36);
x_37 = l_List_join___main___rarg(x_34);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = l_Lean_Expander_variable_transform___closed__1;
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::apply_1(x_36, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
if (lean::is_scalar(x_35)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_35;
}
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
obj* x_44; 
lean::dec(x_6);
x_44 = l_Lean_Expander_noExpansion(x_2);
return x_44;
}
}
}
obj* l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mmap___main___at_Lean_Expander_variables_transform___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_variables_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_variables_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_Level_leading_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Level_leading_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
if (lean::obj_tag(x_5) == 3)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; 
lean::dec(x_5);
x_10 = l_Lean_Expander_noExpansion(x_2);
return x_10;
}
}
}
obj* l_Lean_Expander_Level_leading_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_Level_leading_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_Subtype_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Subtype");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
return x_4;
}
}
obj* l_Lean_Expander_Subtype_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_3 = l_Lean_Parser_Term_Subtype_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = l_Lean_Parser_Term_lambda_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 2);
lean::inc(x_9);
x_10 = l_Lean_Expander_getOptType___main(x_9);
lean::dec(x_9);
x_11 = 0;
x_12 = l_Lean_Expander_mkSimpleBinder(x_8, x_11, x_10);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::cnstr_get(x_5, 4);
lean::inc(x_14);
lean::dec(x_5);
x_15 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__2;
x_16 = l_List_mfor___main___at_Lean_Expander_mkNotationTransformer___spec__4___closed__3;
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_13);
lean::cnstr_set(x_17, 2, x_16);
lean::cnstr_set(x_17, 3, x_14);
x_18 = lean::apply_1(x_7, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Expander_Subtype_transform___closed__1;
x_22 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_21, x_20);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
obj* l_Lean_Expander_Subtype_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_Subtype_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("universe");
x_3 = l_String_trim(x_2);
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Expander_universes_transform___spec__1(obj* x_1) {
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
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Parser_command_universe_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
x_10 = lean::apply_1(x_7, x_9);
x_11 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1(x_5);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_1, 0, x_10);
return x_1;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_14 = l_Lean_Parser_command_universe_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1___closed__1;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
x_18 = lean::apply_1(x_15, x_17);
x_19 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1(x_13);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_Lean_Expander_universes_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = l_Lean_Parser_command_universes_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::apply_1(x_4, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = l_List_map___main___at_Lean_Expander_universes_transform___spec__1(x_6);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_Lean_Expander_universes_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_universes_transform(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expander_sorry_transform___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = lean::box(0);
x_2 = lean::mk_string("sorryAx");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_Expander_globId(x_3);
x_5 = l_Lean_Parser_Term_hole_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::box(0);
x_8 = lean::mk_string("_");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_1(x_6, x_11);
x_13 = lean::mk_string("Bool");
x_14 = lean_name_mk_string(x_1, x_13);
x_15 = lean::mk_string("false");
x_16 = lean_name_mk_string(x_14, x_15);
x_17 = l_Lean_Expander_globId(x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_List_foldl___main___at_Lean_Parser_Term_mkApp___spec__1(x_4, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
obj* l_Lean_Expander_sorry_transform(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_sorry_transform___closed__1;
return x_3;
}
}
obj* l_Lean_Expander_sorry_transform___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_sorry_transform(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
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
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
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
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
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
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
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
obj* l_RBNode_insert___at_Lean_Expander_builtinTransformers___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_Expander_builtinTransformers___spec__2(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__3(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = l_RBNode_insert___at_Lean_Expander_builtinTransformers___spec__1(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_Expander_builtinTransformers() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_1 = l_Lean_Parser_command_mixfix;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_mixfix_transform___boxed), 2, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_command_reserveMixfix;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_reserveMixfix_transform___boxed), 2, 0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_Term_bracketedBinders;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_bracketedBinders_transform___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_Term_lambda;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_lambda_transform___boxed), 2, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_Term_pi;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_pi_transform___boxed), 2, 0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_Term_depArrow;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_depArrow_transform___boxed), 2, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_Term_arrow;
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_arrow_transform___boxed), 2, 0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_Term_paren;
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_paren_transform___boxed), 2, 0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_Term_assume;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_assume_transform___boxed), 2, 0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_Term_if;
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_if_transform___boxed), 2, 0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_Term_let;
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_let_transform___boxed), 2, 0);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
x_34 = l_Lean_Parser_command_axiom;
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_axiom_transform___boxed), 2, 0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_declaration;
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_declaration_transform___boxed), 2, 0);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_command_introRule;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_introRule_transform___boxed), 2, 0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_command_variable;
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_variable_transform___boxed), 2, 0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_variables;
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_variables_transform___boxed), 2, 0);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_Lean_Parser_Level_leading;
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_Level_leading_transform___boxed), 2, 0);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_Lean_Parser_Term_Subtype;
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_Subtype_transform___boxed), 2, 0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_53);
x_55 = l_Lean_Parser_command_universes;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_universes_transform___boxed), 2, 0);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_Lean_Parser_Term_sorry;
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_sorry_transform___boxed), 2, 0);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::box(0);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_57);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_54);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_51);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_48);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_45);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_42);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_39);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_36);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_33);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_30);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_27);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_24);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_21);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_18);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_15);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_12);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_9);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_6);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_3);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::box(0);
x_83 = l_List_foldl___main___at_Lean_Expander_builtinTransformers___spec__3(x_82, x_81);
return x_83;
}
}
obj* l_Lean_Expander_ExpanderConfig_HasLift(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Expander_ExpanderConfig_HasLift___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Expander_ExpanderConfig_HasLift(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Expander_ExpanderState_new() {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0u);
return x_1;
}
}
obj* l_Lean_Expander_mkScope(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_1, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_Lean_Expander_mkScope___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Expander_mkScope(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_5, 0);
x_7 = lean::cnstr_get(x_5, 2);
x_8 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
x_11 = 2;
x_12 = l_String_splitAux___main___closed__1;
lean::inc(x_6);
x_13 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_2);
lean::cnstr_set_scalar(x_13, sizeof(void*)*5, x_11);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = l_Lean_Parser_Syntax_getPos(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Lean_FileMap_toPosition(x_7, x_17);
x_19 = 2;
x_20 = l_String_splitAux___main___closed__1;
lean::inc(x_6);
x_21 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set(x_21, 2, x_8);
lean::cnstr_set(x_21, 3, x_20);
lean::cnstr_set(x_21, 4, x_2);
lean::cnstr_set_scalar(x_21, sizeof(void*)*5, x_19);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
lean::dec(x_16);
x_24 = l_Lean_FileMap_toPosition(x_7, x_23);
x_25 = 2;
x_26 = l_String_splitAux___main___closed__1;
lean::inc(x_6);
x_27 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
lean::cnstr_set(x_27, 4, x_2);
lean::cnstr_set_scalar(x_27, sizeof(void*)*5, x_25);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_4);
lean::dec(x_1);
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
uint8 x_8; 
x_8 = !lean::is_exclusive(x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::inc(x_1);
x_11 = l___private_init_lean_expander_2__expandCore___main(x_1, x_9, x_3, x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
lean::free_heap_obj(x_2);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
lean::dec(x_15);
x_18 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(x_1, x_10, x_17, x_4);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
lean::dec(x_16);
lean::free_heap_obj(x_2);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
lean::dec(x_18);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_18);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_2, 1, x_25);
lean::cnstr_set(x_2, 0, x_16);
lean::cnstr_set(x_23, 0, x_2);
return x_18;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_23, 0);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_23);
lean::cnstr_set(x_2, 1, x_26);
lean::cnstr_set(x_2, 0, x_16);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_2);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set(x_18, 0, x_28);
return x_18;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_18, 0);
lean::inc(x_29);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 x_32 = x_29;
} else {
 lean::dec_ref(x_29);
 x_32 = lean::box(0);
}
lean::cnstr_set(x_2, 1, x_30);
lean::cnstr_set(x_2, 0, x_16);
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_2);
lean::cnstr_set(x_33, 1, x_31);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_2, 0);
x_36 = lean::cnstr_get(x_2, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_2);
lean::inc(x_4);
lean::inc(x_1);
x_37 = l___private_init_lean_expander_2__expandCore___main(x_1, x_35, x_3, x_4);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_36);
lean::dec(x_4);
lean::dec(x_1);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_39 = x_37;
} else {
 lean::dec_ref(x_37);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_38);
return x_40;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
lean::dec(x_41);
x_44 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(x_1, x_36, x_43, x_4);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_42);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_46 = x_44;
} else {
 lean::dec_ref(x_44);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_49 = x_44;
} else {
 lean::dec_ref(x_44);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_52 = x_48;
} else {
 lean::dec_ref(x_48);
 x_52 = lean::box(0);
}
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_42);
lean::cnstr_set(x_53, 1, x_50);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
if (lean::is_scalar(x_49)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_49;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
obj* l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::box(0);
lean::inc(x_1);
lean::cnstr_set(x_2, 1, x_7);
lean::cnstr_set(x_2, 0, x_1);
x_8 = l_Lean_Parser_Syntax_flipScopes___main(x_2, x_5);
x_9 = l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(x_1, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = lean::box(0);
lean::inc(x_1);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_Syntax_flipScopes___main(x_14, x_11);
x_16 = l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(x_1, x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_4);
lean::dec(x_1);
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
uint8 x_8; 
x_8 = !lean::is_exclusive(x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::inc(x_1);
x_11 = l___private_init_lean_expander_2__expandCore___main(x_1, x_9, x_3, x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
lean::free_heap_obj(x_2);
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
lean::dec(x_15);
x_18 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(x_1, x_10, x_17, x_4);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
lean::dec(x_16);
lean::free_heap_obj(x_2);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
lean::inc(x_20);
lean::dec(x_18);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_18);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::cnstr_get(x_18, 0);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_2, 1, x_25);
lean::cnstr_set(x_2, 0, x_16);
lean::cnstr_set(x_23, 0, x_2);
return x_18;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_23, 0);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_23);
lean::cnstr_set(x_2, 1, x_26);
lean::cnstr_set(x_2, 0, x_16);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_2);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set(x_18, 0, x_28);
return x_18;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_18, 0);
lean::inc(x_29);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 x_32 = x_29;
} else {
 lean::dec_ref(x_29);
 x_32 = lean::box(0);
}
lean::cnstr_set(x_2, 1, x_30);
lean::cnstr_set(x_2, 0, x_16);
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_2);
lean::cnstr_set(x_33, 1, x_31);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_2, 0);
x_36 = lean::cnstr_get(x_2, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_2);
lean::inc(x_4);
lean::inc(x_1);
x_37 = l___private_init_lean_expander_2__expandCore___main(x_1, x_35, x_3, x_4);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_36);
lean::dec(x_4);
lean::dec(x_1);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_39 = x_37;
} else {
 lean::dec_ref(x_37);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_38);
return x_40;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
lean::dec(x_37);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
lean::dec(x_41);
x_44 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(x_1, x_36, x_43, x_4);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_42);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_46 = x_44;
} else {
 lean::dec_ref(x_44);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_49 = x_44;
} else {
 lean::dec_ref(x_44);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_52 = x_48;
} else {
 lean::dec_ref(x_48);
 x_52 = lean::box(0);
}
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_42);
lean::cnstr_set(x_53, 1, x_50);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
if (lean::is_scalar(x_49)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_49;
}
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
}
obj* _init_l___private_init_lean_expander_2__expandCore___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("macro expansion limit exceeded");
return x_1;
}
}
obj* l___private_init_lean_expander_2__expandCore___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
lean::inc(x_2);
x_9 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_8);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_4, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(x_13, x_14);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::dec(x_12);
x_17 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__3(x_8, x_16, x_3, x_4);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
lean::dec(x_14);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_17);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
x_25 = l_Lean_Parser_Syntax_mkNode(x_14, x_24);
lean::cnstr_set(x_22, 0, x_25);
return x_17;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_22, 0);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_22);
x_28 = l_Lean_Parser_Syntax_mkNode(x_14, x_26);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_17, 0, x_29);
return x_17;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_17, 0);
lean::inc(x_30);
lean::dec(x_17);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_30, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_33 = x_30;
} else {
 lean::dec_ref(x_30);
 x_33 = lean::box(0);
}
x_34 = l_Lean_Parser_Syntax_mkNode(x_14, x_31);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_32);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_15, 0);
lean::inc(x_37);
lean::dec(x_15);
x_38 = l_Lean_Expander_mkScope(x_3, x_4);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
lean::dec(x_37);
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_8);
lean::dec(x_4);
x_39 = !lean::is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
lean::dec(x_38);
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
lean::dec(x_42);
x_45 = lean::box(0);
lean::inc(x_43);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::cnstr_get(x_12, 1);
lean::inc(x_47);
lean::dec(x_12);
lean::inc(x_47);
x_48 = l_List_map___main___at___private_init_lean_expander_2__expandCore___main___spec__4(x_43, x_47);
lean::inc(x_14);
x_49 = l_Lean_Parser_Syntax_mkNode(x_14, x_48);
x_50 = lean::cnstr_get(x_4, 0);
lean::inc(x_50);
x_51 = lean::apply_2(x_37, x_49, x_50);
if (lean::obj_tag(x_51) == 0)
{
uint8 x_52; 
lean::dec(x_47);
lean::dec(x_46);
lean::dec(x_44);
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_4);
x_52 = !lean::is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
obj* x_53; obj* x_54; 
x_53 = lean::cnstr_get(x_51, 0);
lean::inc(x_53);
lean::dec(x_51);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_51, 0);
lean::inc(x_55);
lean::dec(x_51);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; 
lean::dec(x_46);
x_56 = l_List_mmap___main___at___private_init_lean_expander_2__expandCore___main___spec__5(x_8, x_47, x_44, x_4);
if (lean::obj_tag(x_56) == 0)
{
uint8 x_57; 
lean::dec(x_14);
x_57 = !lean::is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
obj* x_58; obj* x_59; 
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
lean::dec(x_56);
x_59 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
else
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_56);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::cnstr_get(x_56, 0);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; obj* x_64; 
x_63 = lean::cnstr_get(x_61, 0);
x_64 = l_Lean_Parser_Syntax_mkNode(x_14, x_63);
lean::cnstr_set(x_61, 0, x_64);
return x_56;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_61, 0);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_61);
x_67 = l_Lean_Parser_Syntax_mkNode(x_14, x_65);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
lean::cnstr_set(x_56, 0, x_68);
return x_56;
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_56, 0);
lean::inc(x_69);
lean::dec(x_56);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_72 = x_69;
} else {
 lean::dec_ref(x_69);
 x_72 = lean::box(0);
}
x_73 = l_Lean_Parser_Syntax_mkNode(x_14, x_70);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_71);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
obj* x_76; obj* x_77; 
lean::dec(x_47);
lean::dec(x_14);
x_76 = lean::cnstr_get(x_55, 0);
lean::inc(x_76);
lean::dec(x_55);
x_77 = l_Lean_Parser_Syntax_flipScopes___main(x_46, x_76);
x_1 = x_8;
x_2 = x_77;
x_3 = x_44;
goto _start;
}
}
}
}
}
}
else
{
obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_2);
x_80 = l___private_init_lean_expander_2__expandCore___main___closed__1;
x_81 = l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(x_79, x_80, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_79);
return x_81;
}
}
}
obj* l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Expander_error___at___private_init_lean_expander_2__expandCore___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at___private_init_lean_expander_2__expandCore___main___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_expander_2__expandCore(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_expander_2__expandCore___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Expander_expand(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(1000u);
x_4 = l_Lean_Expander_ExpanderState_new;
x_5 = l___private_init_lean_expander_2__expandCore___main(x_3, x_1, x_4, x_2);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_5);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
lean::cnstr_set(x_5, 0, x_11);
return x_5;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
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
l_Lean_Expander_declaration_transform___closed__1 = _init_l_Lean_Expander_declaration_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_declaration_transform___closed__1);
l_Lean_Expander_declaration_transform___closed__2 = _init_l_Lean_Expander_declaration_transform___closed__2();
lean::mark_persistent(l_Lean_Expander_declaration_transform___closed__2);
l_Lean_Expander_declaration_transform___closed__3 = _init_l_Lean_Expander_declaration_transform___closed__3();
lean::mark_persistent(l_Lean_Expander_declaration_transform___closed__3);
l_Lean_Expander_variable_transform___closed__1 = _init_l_Lean_Expander_variable_transform___closed__1();
lean::mark_persistent(l_Lean_Expander_variable_transform___closed__1);
l_Lean_Expander_bindingAnnotationUpdate = _init_l_Lean_Expander_bindingAnnotationUpdate();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate);
l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_HasView_x27___elambda__1___closed__1);
l_Lean_Expander_bindingAnnotationUpdate_HasView_x27 = _init_l_Lean_Expander_bindingAnnotationUpdate_HasView_x27();
lean::mark_persistent(l_Lean_Expander_bindingAnnotationUpdate_HasView_x27);
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
