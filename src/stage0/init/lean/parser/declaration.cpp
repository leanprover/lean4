// Lean compiler output
// Module: init.lean.parser.declaration
// Imports: init.lean.parser.term
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
obj* l_Lean_Parser_command_univParams_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_HasView;
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_relaxedInferModifier;
obj* l_Lean_Parser_command_equation_Parser___closed__1;
extern obj* l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27;
obj* l_Lean_Parser_command_structExplicitBinder_HasView;
obj* l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_declAttributes_HasView_x_27;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView;
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_typeSpec_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_notationLike_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structBinderContent;
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_univParams;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_command_defLike_kind_HasView;
obj* l_Lean_Parser_command_equation_HasView;
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x_27(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_binderDefault_HasView;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_command_example_HasView_x_27;
obj* l_Lean_Parser_command_declVal_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x_27;
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2;
extern obj* l_Lean_Parser_Term_paren_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_simpleDeclVal;
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes;
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_termParser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_defLike_HasView_x_27;
obj* l_Lean_Parser_command_structureFieldBlock_Parser___closed__1;
obj* l_Lean_Parser_command_structure_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureKw;
obj* l_Lean_Parser_command_inferModifier_Parser___closed__1;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structureCtor;
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27;
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_docComment_HasView_x_27;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_visibility_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_extends;
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_Parser___closed__1;
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___elambda__1(obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_constantKeyword;
obj* l_Lean_Parser_command_defLike;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView;
obj* l_Lean_Parser_command_docComment_Parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_declSig;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27;
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_declSig_Parser(obj*, obj*, obj*, obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_HasView;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1;
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9(obj*, obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structImplicitBinder;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_Parser___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_oldUnivParams;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__2(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x_27___elambda__2(obj*);
obj* l_Lean_Parser_command_structBinderContent_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27;
obj* l_Lean_Parser_command_declModifiers_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1;
obj* l_Lean_Parser_command_structureCtor_HasView;
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView_x_27;
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_axiom_HasView;
obj* l_Lean_Parser_command_declaration_HasView;
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Level_leading_HasView_x_27___elambda__1___closed__3;
extern obj* l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_declVal_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27;
obj* l_Lean_Parser_MonadParsec_many_x_27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structImplicitBinder_HasView;
obj* l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_command_inferModifier_HasView;
obj* l_Lean_Parser_command_inductive_HasView;
obj* l_Lean_Parser_command_declaration_HasView_x_27;
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_attrInstance_HasView;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_introRule_HasView;
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView;
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8(obj*);
obj* l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1___spec__1(obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_declSig_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
obj* l___private_init_lean_parser_parsec_2__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_optDeclSig_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_declaration_inner_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x_27;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView;
obj* l_Lean_Parser_command_structureFieldBlock;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams;
obj* l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView;
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27___elambda__1(obj*);
extern obj* l_Lean_Parser_command_notationLike_HasView;
obj* l_List_join___main___rarg(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2;
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___boxed(obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structure;
obj* l_Lean_Parser_command_structure_HasView_x_27;
obj* l_Lean_Parser_command_declAttributes_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_axiom;
obj* l_Lean_Parser_Term_binderDefault_Parser(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_command_instImplicitBinder;
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_declaration_inner;
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3;
extern obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
obj* l_Lean_Parser_command_inferModifier;
obj* l_Lean_Parser_command_extends_HasView_x_27;
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1(obj*);
extern obj* l_Lean_Parser_command_notation_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_declModifiers_HasView;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_strictInferModifier_HasView;
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_declModifiers_Parser___closed__1;
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_univParams_HasView_x_27;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___elambda__1(obj*);
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView;
obj* l_Lean_Parser_command_univParams_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1;
extern obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x_27;
obj* l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView;
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_tokens___rarg(obj*);
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1(obj*);
extern obj* l_Lean_Parser_Term_tuple_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4;
extern obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2;
obj* l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_oldUnivParams_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5;
obj* l_Lean_Parser_Term_optType_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4;
extern obj* l_Lean_Parser_Term_optType_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_attrInstance;
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___boxed(obj*);
obj* l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structureFieldBlock_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_example_HasView;
obj* l_Lean_Parser_command_introRule_Parser___closed__1;
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__3;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__2(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x_27;
obj* l_Lean_Parser_command_docComment_HasView;
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_instImplicitBinder_HasView;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_example_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_HasView;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declAttributes_Parser___closed__1;
obj* l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27;
obj* l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_Term_bracketedBinders_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_structure_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(obj*);
obj* l_Lean_Parser_command_declVal_Parser___closed__1;
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1;
extern obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_example_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_equation_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4;
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*);
obj* l_Lean_Parser_command_declVal;
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2;
obj* l_Lean_Parser_command_structBinderContent_Parser___closed__1;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1;
obj* l_String_trim(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1;
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declModifiers;
obj* l_Lean_Parser_command_structure_HasView;
obj* l_Lean_Parser_command_declModifiers_HasView_x_27;
extern obj* l_Lean_Parser_Term_binderDefault_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structureFieldBlock_HasView;
extern obj* l_Lean_Parser_number_HasView_x_27___elambda__1___closed__6;
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_declaration;
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, uint8, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance;
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_extends_HasView;
obj* l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3;
extern obj* l_Lean_Parser_Term_bracketedBinders_HasView;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser___closed__1;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27;
obj* l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
obj* l_Lean_Parser_command_identUnivParams_HasView;
obj* l_Lean_Parser_command_simpleDeclVal_HasView;
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1(obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_equation_HasView_x_27;
obj* l_Lean_Parser_command_inductive;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_constantKeyword_HasView;
obj* l_Lean_Parser_command_docComment;
obj* l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4(obj*);
extern obj* l_Lean_Parser_number_HasView_x_27___elambda__1___closed__4;
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1;
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind;
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_equation;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParserCommandParserCoe(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_introRule_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_docComment_Parser___closed__1;
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictInferModifier;
obj* l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27;
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_command_declaration_Parser___closed__1;
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_command_univParams_HasView;
obj* l_Lean_Parser_command_structure_Parser___closed__1;
obj* l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1(obj*);
extern obj* l_Lean_Parser_command_mixfix_kind_HasView_x_27___elambda__1___closed__6;
obj* l_Lean_Parser_command_docComment_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27;
obj* l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Term_typeSpec_HasView;
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1(obj*);
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27;
obj* l_Lean_Parser_command_docComment_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_CommandParserM_Alternative(obj*);
obj* l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_defLike_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declaration_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Monad(obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x_27;
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_command_optDeclSig_Parser___closed__1;
obj* l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27;
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictImplicitBinder;
obj* l_String_quote(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinderContent;
obj* l_Lean_Parser_Term_typeSpec_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_command_instance_HasView;
obj* l_List_map___main___at_Lean_Parser_Term_tuple_HasView_x_27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig_HasView;
obj* l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_visibility;
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x_27;
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_command_example;
obj* l_Lean_Parser_command_docComment_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView_x_27;
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1;
obj* l_Lean_Parser_command_axiom_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_CommandParserM_MonadExcept(obj*);
obj* l_Lean_Parser_command_declSig_Parser___closed__1;
obj* l_Lean_Parser_command_introRule_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_introRule;
obj* l_Lean_Parser_command_inferModifier_HasView_x_27;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2(obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinder;
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1(obj*);
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_termParserCommandParserCoe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_termParser_run(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_docComment() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("docComment");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_command_docComment;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_command_docComment_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_command_docComment;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
lean::dec(x_3);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
if (lean::obj_tag(x_5) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_24 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(3);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_command_docComment;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_30 = lean::cnstr_get(x_5, 0);
lean::inc(x_30);
lean::dec(x_5);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_23);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::box(3);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
x_38 = l_Lean_Parser_command_docComment;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_40);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__3;
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_docComment;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_48 = lean::cnstr_get(x_5, 0);
lean::inc(x_48);
lean::dec(x_5);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_8);
x_53 = lean::box(3);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_43);
lean::cnstr_set(x_55, 1, x_54);
x_56 = l_Lean_Parser_command_docComment;
x_57 = l_Lean_Parser_Syntax_mkNode(x_56, x_55);
return x_57;
}
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_3, 0);
lean::inc(x_58);
lean::dec(x_3);
x_61 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_61, 0, x_58);
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_43);
lean::cnstr_set(x_64, 1, x_63);
x_65 = l_Lean_Parser_command_docComment;
x_66 = l_Lean_Parser_Syntax_mkNode(x_65, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_5, 0);
lean::inc(x_67);
lean::dec(x_5);
x_70 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_8);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_61);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_43);
lean::cnstr_set(x_73, 1, x_72);
x_74 = l_Lean_Parser_command_docComment;
x_75 = l_Lean_Parser_Syntax_mkNode(x_74, x_73);
return x_75;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
lean::cnstr_set(x_1, 2, x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_docComment_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; obj* x_30; obj* x_31; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_1;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
lean::dec(x_1);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_29:
{
switch (lean::obj_tag(x_28)) {
case 0:
{
obj* x_39; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_18);
lean::cnstr_set(x_43, 1, x_27);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
case 3:
{
obj* x_44; obj* x_45; 
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_18);
lean::cnstr_set(x_45, 1, x_27);
lean::cnstr_set(x_45, 2, x_44);
return x_45;
}
default:
{
obj* x_47; obj* x_48; 
lean::dec(x_28);
x_47 = lean::box(0);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_27);
lean::cnstr_set(x_48, 2, x_47);
return x_48;
}
}
}
lbl_32:
{
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_31, 0);
lean::inc(x_49);
lean::dec(x_31);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
if (lean::obj_tag(x_30) == 0)
{
obj* x_53; obj* x_54; 
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_18);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_30, 0);
lean::inc(x_55);
lean::dec(x_30);
x_27 = x_52;
x_28 = x_55;
goto lbl_29;
}
}
case 3:
{
obj* x_58; 
x_58 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_59; 
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_18);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_30, 0);
lean::inc(x_60);
lean::dec(x_30);
x_27 = x_58;
x_28 = x_60;
goto lbl_29;
}
}
default:
{
obj* x_64; 
lean::dec(x_31);
x_64 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_65; 
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_18);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set(x_65, 2, x_64);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_30, 0);
lean::inc(x_66);
lean::dec(x_30);
x_27 = x_64;
x_28 = x_66;
goto lbl_29;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_docComment_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_14; obj* x_15; 
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_5);
lean::inc(x_9);
x_14 = l_Lean_Parser_token(x_9, x_5, x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_19 = x_14;
} else {
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get(x_15, 1);
x_24 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 lean::cnstr_set(x_15, 2, lean::box(0));
 x_26 = x_15;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_15);
 x_26 = lean::box(0);
}
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_29; obj* x_31; uint8 x_34; 
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_34 = lean::string_dec_eq(x_0, x_31);
lean::dec(x_0);
if (x_34 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_26);
lean::dec(x_19);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_5);
x_39 = lean::box(0);
x_40 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_31, x_2, x_38, x_39, x_9, x_22, x_17);
lean::dec(x_9);
x_42 = lean::cnstr_get(x_40, 0);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_44 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_46 = x_40;
} else {
 lean::inc(x_44);
 lean::dec(x_40);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_42, 1);
x_49 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_51 = x_42;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_20);
lean::cnstr_set(x_53, 1, x_47);
lean::cnstr_set(x_53, 2, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_55);
x_57 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_56, x_8);
x_58 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_57);
if (lean::is_scalar(x_46)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_46;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_44);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_20);
x_61 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_63 = x_40;
} else {
 lean::inc(x_61);
 lean::dec(x_40);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_42, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_67 = x_42;
} else {
 lean::inc(x_64);
 lean::dec(x_42);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_69);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_70);
x_73 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_72, x_8);
x_74 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_31);
x_80 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_26)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_26;
}
lean::cnstr_set(x_81, 0, x_20);
lean::cnstr_set(x_81, 1, x_22);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_81);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_82);
x_85 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_84, x_8);
x_86 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_85);
if (lean::is_scalar(x_19)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_19;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_17);
return x_87;
}
}
case 3:
{
obj* x_91; 
lean::dec(x_26);
lean::dec(x_0);
lean::dec(x_19);
x_91 = lean::box(0);
x_27 = x_91;
goto lbl_28;
}
default:
{
obj* x_96; 
lean::dec(x_26);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_20);
x_96 = lean::box(0);
x_27 = x_96;
goto lbl_28;
}
}
lbl_28:
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_27);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_5);
x_99 = lean::box(0);
x_100 = l_String_splitAux___main___closed__1;
x_101 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_100, x_2, x_98, x_99, x_9, x_22, x_17);
lean::dec(x_9);
x_103 = lean::cnstr_get(x_101, 0);
x_105 = lean::cnstr_get(x_101, 1);
if (lean::is_exclusive(x_101)) {
 x_107 = x_101;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_101);
 x_107 = lean::box(0);
}
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_103);
x_109 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_109, x_108);
x_111 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_110, x_8);
x_112 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_111);
if (lean::is_scalar(x_107)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_107;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_105);
return x_113;
}
}
else
{
obj* x_118; obj* x_120; obj* x_121; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_118 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_120 = x_14;
} else {
 lean::inc(x_118);
 lean::dec(x_14);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_15, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_124 = x_15;
} else {
 lean::inc(x_121);
 lean::dec(x_15);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = x_125;
x_127 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_128 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_127, x_126);
x_129 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_128, x_8);
x_130 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_129);
if (lean::is_scalar(x_120)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_120;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_118);
return x_131;
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_String_isEmpty(x_0);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_7 = lean::string_length(x_0);
x_8 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_8);
lean::inc(x_4);
x_12 = l___private_init_lean_parser_parsec_2__strAux___main(x_7, x_10, x_4);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_0);
x_14 = lean::box(0);
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set(x_16, 2, x_1);
lean::cnstr_set(x_16, 3, x_14);
x_17 = 0;
x_18 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1, x_17);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_5);
return x_20;
}
else
{
obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_4);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
lean::dec(x_12);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_0);
lean::cnstr_set(x_27, 1, x_23);
lean::cnstr_set(x_27, 2, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_5);
return x_28;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_0);
x_31 = l_String_splitAux___main___closed__1;
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_4);
lean::cnstr_set(x_33, 2, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_5);
return x_34;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_4);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_6, x_0, x_1, x_2, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = 0;
x_20 = lean::box(x_19);
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_3);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_4);
lean::cnstr_set(x_27, 2, x_26);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_11);
return x_28;
}
else
{
uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_22);
x_30 = 1;
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = lean::box(x_30);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
lean::cnstr_set(x_33, 2, x_31);
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_11);
return x_34;
}
}
else
{
obj* x_37; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::dec(x_3);
x_37 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_39 = x_8;
} else {
 lean::inc(x_37);
 lean::dec(x_8);
 x_39 = lean::box(0);
}
x_40 = 1;
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = lean::box(x_40);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_4);
lean::cnstr_set(x_43, 2, x_41);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_6, x_7, x_5, x_5, x_0, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_13 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = l_String_OldIterator_curr___main(x_2);
x_18 = l_True_Decidable;
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_19 = l_Char_quoteCore(x_17);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_23, x_25, x_24, x_24, x_0, x_1, x_2, x_3);
x_27 = lean::cnstr_get(x_26, 0);
x_29 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_31 = x_26;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_26);
 x_31 = lean::box(0);
}
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_27);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_29);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = l_String_OldIterator_next___main(x_2);
x_36 = lean::box(0);
x_37 = lean::box_uint32(x_17);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set(x_38, 2, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_3);
return x_39;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_13; obj* x_14; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_1, x_8);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_0);
x_13 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 1);
x_21 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_set(x_14, 1, lean::box(0));
 lean::cnstr_set(x_14, 2, lean::box(0));
 x_23 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
lean::inc(x_19);
x_25 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_0, x_9, x_2, x_3, x_19, x_16);
lean::dec(x_9);
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_19);
lean::dec(x_23);
x_31 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_33 = x_25;
} else {
 lean::inc(x_31);
 lean::dec(x_25);
 x_33 = lean::box(0);
}
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_27);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_31);
return x_35;
}
else
{
uint8 x_36; 
x_36 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_37 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_39 = x_25;
} else {
 lean::inc(x_37);
 lean::dec(x_25);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_27, 0);
lean::inc(x_40);
lean::dec(x_27);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_mjoin___rarg___closed__1;
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_47, 0, x_43);
lean::closure_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::box(0);
if (lean::is_scalar(x_23)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_23;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_19);
lean::cnstr_set(x_50, 2, x_48);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_50);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_37);
return x_52;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_19);
lean::dec(x_23);
x_55 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_57 = x_25;
} else {
 lean::inc(x_55);
 lean::dec(x_25);
 x_57 = lean::box(0);
}
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_27);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
}
}
else
{
obj* x_64; obj* x_66; obj* x_67; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_66 = x_13;
} else {
 lean::inc(x_64);
 lean::dec(x_13);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_14, 0);
x_69 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_70 = x_14;
} else {
 lean::inc(x_67);
 lean::dec(x_14);
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
if (lean::is_scalar(x_66)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_66;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_64);
return x_73;
}
}
else
{
obj* x_74; obj* x_75; 
x_74 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_77 = lean::cnstr_get(x_74, 1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_79 = x_74;
} else {
 lean::inc(x_77);
 lean::dec(x_74);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_75, 1);
x_82 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_84 = x_75;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_75);
 x_84 = lean::box(0);
}
x_85 = lean::box(0);
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_84)) {
 x_87 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_87 = x_84;
}
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_80);
lean::cnstr_set(x_87, 2, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_87);
if (lean::is_scalar(x_79)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_79;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_77);
return x_89;
}
else
{
obj* x_90; obj* x_92; obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_90 = lean::cnstr_get(x_74, 1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_92 = x_74;
} else {
 lean::inc(x_90);
 lean::dec(x_74);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_75, 0);
x_95 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 x_96 = x_75;
} else {
 lean::inc(x_93);
 lean::dec(x_75);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
if (lean::is_scalar(x_92)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_92;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_90);
return x_99;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_many_x_27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = l_String_OldIterator_remaining___main(x_3);
lean::inc(x_3);
x_7 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_0, x_5, x_1, x_2, x_3, x_4);
lean::dec(x_5);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; 
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_11);
return x_17;
}
else
{
uint8 x_18; 
x_18 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_18 == 0)
{
obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
lean::dec(x_15);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_mjoin___rarg___closed__1;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_22);
lean::closure_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_3);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_11);
return x_30;
}
else
{
obj* x_32; 
lean::dec(x_3);
if (lean::is_scalar(x_13)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_13;
}
lean::cnstr_set(x_32, 0, x_15);
lean::cnstr_set(x_32, 1, x_11);
return x_32;
}
}
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_3);
lean::inc(x_2);
x_8 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::apply_5(x_1, x_14, x_2, x_3, x_16, x_11);
x_22 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_26 = x_21;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_21);
 x_26 = lean::box(0);
}
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_22);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_34 = x_8;
} else {
 lean::inc(x_32);
 lean::dec(x_8);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_9, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_38 = x_9;
} else {
 lean::inc(x_35);
 lean::dec(x_9);
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
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; 
x_0 = lean::mk_string("/--");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = lean::mk_string("-/");
x_6 = l_Lean_Parser_symbol_tokens___rarg(x_5, x_1);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_4);
lean::dec(x_6);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_8);
lean::dec(x_8);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
x_15 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_15;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_4);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_6, x_0, x_1, x_2, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = 0;
x_20 = lean::box(x_19);
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_3);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_4);
lean::cnstr_set(x_27, 2, x_26);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_11);
return x_28;
}
else
{
uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_22);
x_30 = 1;
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = lean::box(x_30);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
lean::cnstr_set(x_33, 2, x_31);
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_11);
return x_34;
}
}
else
{
obj* x_37; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::dec(x_3);
x_37 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_39 = x_8;
} else {
 lean::inc(x_37);
 lean::dec(x_8);
 x_39 = lean::box(0);
}
x_40 = 1;
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = lean::box(x_40);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_4);
lean::cnstr_set(x_43, 2, x_41);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_3);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(x_0, x_1, x_2, x_5, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; uint8 x_12; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_12 = lean::unbox(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_3);
x_22 = lean::box(0);
x_23 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_24 = l_mjoin___rarg___closed__1;
x_25 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_23, x_24, x_21, x_22, x_1, x_2, x_16, x_13);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 lean::cnstr_set(x_25, 1, lean::box(0));
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_26);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_30);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_32, 2);
lean::inc(x_36);
lean::dec(x_32);
x_39 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_34, x_28);
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
else
{
obj* x_47; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_47 = lean::cnstr_get(x_32, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_exclusive(x_32)) {
 x_50 = x_32;
} else {
 lean::inc(x_47);
 lean::dec(x_32);
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
if (lean::is_scalar(x_30)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_30;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_28);
return x_53;
}
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_3);
x_55 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_57 = x_7;
} else {
 lean::inc(x_55);
 lean::dec(x_7);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_8, 1);
x_60 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_62 = x_8;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_8);
 x_62 = lean::box(0);
}
x_63 = lean::box(0);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_5);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_64);
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_66, 2);
lean::inc(x_70);
lean::dec(x_66);
x_73 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_68, x_55);
x_74 = lean::cnstr_get(x_73, 0);
x_76 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_78 = x_73;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_73);
 x_78 = lean::box(0);
}
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_74);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_76);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_81 = lean::cnstr_get(x_66, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_84 = x_66;
} else {
 lean::inc(x_81);
 lean::dec(x_66);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
if (lean::is_scalar(x_57)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_57;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_55);
return x_87;
}
}
}
else
{
obj* x_89; obj* x_91; obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_3);
x_89 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_91 = x_7;
} else {
 lean::inc(x_89);
 lean::dec(x_7);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_8, 0);
x_94 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_95 = x_8;
} else {
 lean::inc(x_92);
 lean::dec(x_8);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_100; obj* x_102; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_91);
x_100 = lean::cnstr_get(x_98, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_98, 2);
lean::inc(x_102);
lean::dec(x_98);
x_105 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_100, x_89);
x_106 = lean::cnstr_get(x_105, 0);
x_108 = lean::cnstr_get(x_105, 1);
if (lean::is_exclusive(x_105)) {
 x_110 = x_105;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_105);
 x_110 = lean::box(0);
}
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_102, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
return x_112;
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_113 = lean::cnstr_get(x_98, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_98, sizeof(void*)*1);
if (lean::is_exclusive(x_98)) {
 x_116 = x_98;
} else {
 lean::inc(x_113);
 lean::dec(x_98);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
if (lean::is_scalar(x_91)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_91;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_89);
return x_119;
}
}
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_MonadParsec_many_x_27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(x_0, x_2, x_3, x_4, x_5);
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
obj* _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("/--");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::mk_string("-/");
lean::inc(x_11);
x_13 = l_String_quote(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_19, 0, x_15);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
x_21 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_24, 0, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_25, 0, x_21);
lean::closure_set(x_25, 1, x_9);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_20);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_command_docComment;
x_31 = l_Lean_Parser_command_docComment_HasView;
x_32 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_30, x_29, x_31);
lean::dec(x_29);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_32;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_4);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_6, x_0, x_1, x_2, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = 0;
x_20 = lean::box(x_19);
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_3);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_4);
lean::cnstr_set(x_27, 2, x_26);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_11);
return x_28;
}
else
{
uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_22);
x_30 = 1;
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = lean::box(x_30);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
lean::cnstr_set(x_33, 2, x_31);
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_11);
return x_34;
}
}
else
{
obj* x_37; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::dec(x_3);
x_37 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_39 = x_8;
} else {
 lean::inc(x_37);
 lean::dec(x_8);
 x_39 = lean::box(0);
}
x_40 = 1;
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = lean::box(x_40);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_4);
lean::cnstr_set(x_43, 2, x_41);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_17 = x_2;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_2);
 x_17 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_3);
x_23 = lean::apply_4(x_13, x_3, x_4, x_5, x_6);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_18 = x_24;
x_19 = x_26;
goto lbl_20;
}
else
{
uint8 x_29; 
x_29 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_29 == 0)
{
obj* x_30; obj* x_33; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_23, 1);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean::inc(x_33);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
x_36 = 0;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = x_37;
x_18 = x_38;
x_19 = x_30;
goto lbl_20;
}
else
{
obj* x_39; obj* x_42; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_23, 1);
lean::inc(x_39);
lean::dec(x_23);
x_42 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_44 = x_24;
} else {
 lean::inc(x_42);
 lean::dec(x_24);
 x_44 = lean::box(0);
}
x_45 = 1;
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_45);
x_47 = x_46;
x_18 = x_47;
x_19 = x_39;
goto lbl_20;
}
}
else
{
obj* x_48; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_50 = x_24;
} else {
 lean::inc(x_48);
 lean::dec(x_24);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 3);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_53; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
x_53 = lean::cnstr_get(x_23, 1);
lean::inc(x_53);
lean::dec(x_23);
x_56 = lean::cnstr_get(x_48, 0);
x_58 = lean::cnstr_get(x_48, 1);
x_60 = lean::cnstr_get(x_48, 2);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 3);
 x_62 = x_48;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_48);
 x_62 = lean::box(0);
}
x_63 = lean::box(3);
lean::inc(x_1);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_1);
x_66 = l_List_reverse___rarg(x_65);
lean::inc(x_0);
x_68 = l_Lean_Parser_Syntax_mkNode(x_0, x_66);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
if (lean::is_scalar(x_62)) {
 x_70 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_70 = x_62;
}
lean::cnstr_set(x_70, 0, x_56);
lean::cnstr_set(x_70, 1, x_58);
lean::cnstr_set(x_70, 2, x_60);
lean::cnstr_set(x_70, 3, x_69);
if (x_29 == 0)
{
uint8 x_71; obj* x_72; obj* x_73; 
x_71 = 0;
if (lean::is_scalar(x_50)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_50;
}
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_71);
x_73 = x_72;
x_18 = x_73;
x_19 = x_53;
goto lbl_20;
}
else
{
uint8 x_74; obj* x_75; obj* x_76; 
x_74 = 1;
if (lean::is_scalar(x_50)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_50;
}
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_74);
x_76 = x_75;
x_18 = x_76;
x_19 = x_53;
goto lbl_20;
}
}
else
{
obj* x_77; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
x_77 = lean::cnstr_get(x_23, 1);
lean::inc(x_77);
lean::dec(x_23);
x_80 = lean::cnstr_get(x_48, 0);
x_82 = lean::cnstr_get(x_48, 1);
x_84 = lean::cnstr_get(x_48, 2);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 3);
 x_86 = x_48;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_48);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_89 = x_51;
} else {
 lean::inc(x_87);
 lean::dec(x_51);
 x_89 = lean::box(0);
}
lean::inc(x_1);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set(x_91, 1, x_1);
x_92 = l_List_reverse___rarg(x_91);
lean::inc(x_0);
x_94 = l_Lean_Parser_Syntax_mkNode(x_0, x_92);
if (lean::is_scalar(x_89)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_89;
}
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_86)) {
 x_96 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_96 = x_86;
}
lean::cnstr_set(x_96, 0, x_80);
lean::cnstr_set(x_96, 1, x_82);
lean::cnstr_set(x_96, 2, x_84);
lean::cnstr_set(x_96, 3, x_95);
if (x_29 == 0)
{
uint8 x_97; obj* x_98; obj* x_99; 
x_97 = 0;
if (lean::is_scalar(x_50)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_50;
}
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_97);
x_99 = x_98;
x_18 = x_99;
x_19 = x_77;
goto lbl_20;
}
else
{
uint8 x_100; obj* x_101; obj* x_102; 
x_100 = 1;
if (lean::is_scalar(x_50)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_50;
}
lean::cnstr_set(x_101, 0, x_96);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_100);
x_102 = x_101;
x_18 = x_102;
x_19 = x_77;
goto lbl_20;
}
}
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_18, 0);
x_105 = lean::cnstr_get(x_18, 1);
x_107 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 x_109 = x_18;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_18);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_17;
}
lean::cnstr_set(x_110, 0, x_103);
lean::cnstr_set(x_110, 1, x_1);
x_111 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_105);
lean::cnstr_set(x_112, 2, x_111);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_116; obj* x_118; obj* x_121; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_113, 2);
lean::inc(x_118);
lean::dec(x_113);
x_121 = l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(x_0, x_114, x_15, x_3, x_4, x_116, x_19);
x_122 = lean::cnstr_get(x_121, 0);
x_124 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 x_126 = x_121;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_118, x_122);
if (lean::is_scalar(x_126)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_126;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_124);
return x_128;
}
else
{
obj* x_133; uint8 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_133 = lean::cnstr_get(x_113, 0);
x_135 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
if (lean::is_exclusive(x_113)) {
 x_136 = x_113;
} else {
 lean::inc(x_133);
 lean::dec(x_113);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_133);
lean::cnstr_set_scalar(x_137, sizeof(void*)*1, x_135);
x_138 = x_137;
x_139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_19);
return x_139;
}
}
else
{
obj* x_146; uint8 x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_146 = lean::cnstr_get(x_18, 0);
x_148 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_149 = x_18;
} else {
 lean::inc(x_146);
 lean::dec(x_18);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_146);
lean::cnstr_set_scalar(x_150, sizeof(void*)*1, x_148);
x_151 = x_150;
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_19);
return x_152;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
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
x_21 = l_List_reverse___rarg(x_14);
x_22 = l_Lean_Parser_Syntax_mkNode(x_0, x_21);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_20;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_24);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
return x_26;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::inc(x_28);
 lean::dec(x_8);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_9, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_34 = x_9;
} else {
 lean::inc(x_31);
 lean::dec(x_9);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_28);
return x_37;
}
}
}
obj* l_Lean_Parser_command_docComment_Parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_3);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(x_0, x_1, x_2, x_5, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; uint8 x_12; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_12 = lean::unbox(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_3);
x_22 = lean::box(0);
x_23 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_24 = l_mjoin___rarg___closed__1;
x_25 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_23, x_24, x_21, x_22, x_1, x_2, x_16, x_13);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 lean::cnstr_set(x_25, 1, lean::box(0));
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_26);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_30);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_32, 2);
lean::inc(x_36);
lean::dec(x_32);
x_39 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_34, x_28);
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 x_44 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
else
{
obj* x_47; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_47 = lean::cnstr_get(x_32, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_exclusive(x_32)) {
 x_50 = x_32;
} else {
 lean::inc(x_47);
 lean::dec(x_32);
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
if (lean::is_scalar(x_30)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_30;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_28);
return x_53;
}
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_3);
x_55 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_57 = x_7;
} else {
 lean::inc(x_55);
 lean::dec(x_7);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_8, 1);
x_60 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_62 = x_8;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_8);
 x_62 = lean::box(0);
}
x_63 = lean::box(0);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_5);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_64);
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_66, 2);
lean::inc(x_70);
lean::dec(x_66);
x_73 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_68, x_55);
x_74 = lean::cnstr_get(x_73, 0);
x_76 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 x_78 = x_73;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::dec(x_73);
 x_78 = lean::box(0);
}
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_74);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_76);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_81 = lean::cnstr_get(x_66, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_84 = x_66;
} else {
 lean::inc(x_81);
 lean::dec(x_66);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
if (lean::is_scalar(x_57)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_57;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_55);
return x_87;
}
}
}
else
{
obj* x_89; obj* x_91; obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_3);
x_89 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_91 = x_7;
} else {
 lean::inc(x_89);
 lean::dec(x_7);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_8, 0);
x_94 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_95 = x_8;
} else {
 lean::inc(x_92);
 lean::dec(x_8);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_100; obj* x_102; obj* x_105; obj* x_106; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_91);
x_100 = lean::cnstr_get(x_98, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_98, 2);
lean::inc(x_102);
lean::dec(x_98);
x_105 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_100, x_89);
x_106 = lean::cnstr_get(x_105, 0);
x_108 = lean::cnstr_get(x_105, 1);
if (lean::is_exclusive(x_105)) {
 x_110 = x_105;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::dec(x_105);
 x_110 = lean::box(0);
}
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_102, x_106);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_108);
return x_112;
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_113 = lean::cnstr_get(x_98, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_98, sizeof(void*)*1);
if (lean::is_exclusive(x_98)) {
 x_116 = x_98;
} else {
 lean::inc(x_113);
 lean::dec(x_98);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
if (lean::is_scalar(x_91)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_91;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_89);
return x_119;
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::mk_string("/--");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("-/");
lean::inc(x_7);
x_9 = l_String_quote(x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser___lambda__1___boxed), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_15, 0, x_11);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_15);
x_17 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_17);
lean::closure_set(x_21, 1, x_5);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_6);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_Lean_Parser_command_docComment_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_docComment;
x_5 = l_Lean_Parser_command_docComment_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_command_docComment_Parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_command_docComment_Parser___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_attrInstance() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("attrInstance");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
x_7 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_3);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_command_attrInstance;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOTAnIdent");
lean::inc(x_1);
x_3 = l_Lean_Parser_Substring_ofString(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::box(3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1;
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
x_9 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_6);
x_10 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3;
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
switch (lean::obj_tag(x_2)) {
case 1:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_30);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_20);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
else
{
obj* x_35; obj* x_38; obj* x_41; 
x_35 = lean::cnstr_get(x_2, 0);
lean::inc(x_35);
lean::dec(x_2);
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
lean::dec(x_1);
x_41 = l_Lean_Parser_Syntax_asNode___main(x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; 
x_42 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_35);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_47; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
lean::dec(x_41);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
x_50 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_47);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_35);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
case 3:
{
obj* x_52; 
x_52 = lean::box(0);
x_18 = x_52;
goto lbl_19;
}
default:
{
obj* x_54; 
lean::dec(x_2);
x_54 = lean::box(0);
x_18 = x_54;
goto lbl_19;
}
}
lbl_19:
{
lean::dec(x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_56; 
x_56 = l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2;
return x_56;
}
else
{
obj* x_57; obj* x_60; 
x_57 = lean::cnstr_get(x_1, 0);
lean::inc(x_57);
lean::dec(x_1);
x_60 = l_Lean_Parser_Syntax_asNode___main(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; 
x_61 = l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1;
return x_61;
}
else
{
obj* x_62; obj* x_65; obj* x_68; obj* x_69; obj* x_70; 
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
lean::dec(x_60);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_65);
x_69 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_attrInstance_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
lean::inc(x_4);
x_8 = l___private_init_lean_parser_token_4__ident_x_27(x_4, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_14, x_4, x_16, x_11);
lean::dec(x_4);
x_23 = lean::cnstr_get(x_21, 0);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_27 = x_21;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_23);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_4);
x_31 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_33 = x_8;
} else {
 lean::inc(x_31);
 lean::dec(x_8);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_9, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_37 = x_9;
} else {
 lean::inc(x_34);
 lean::dec(x_9);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_36);
x_39 = x_38;
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_31);
return x_40;
}
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0ul);
x_8 = lean::nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_17; obj* x_18; 
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_sub(x_2, x_9);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_0);
x_17 = lean::apply_4(x_0, x_3, x_4, x_5, x_6);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; 
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_11 = x_18;
x_12 = x_20;
goto lbl_13;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_18, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_26 = x_18;
} else {
 lean::inc(x_23);
 lean::dec(x_18);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_23, 3);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_29 = lean::cnstr_get(x_17, 1);
lean::inc(x_29);
lean::dec(x_17);
x_32 = lean::cnstr_get(x_23, 0);
x_34 = lean::cnstr_get(x_23, 1);
x_36 = lean::cnstr_get(x_23, 2);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 3);
 x_38 = x_23;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_23);
 x_38 = lean::box(0);
}
x_39 = lean::box(3);
lean::inc(x_1);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_1);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_List_reverse___rarg(x_42);
x_44 = l_Lean_Parser_noKind;
x_45 = l_Lean_Parser_Syntax_mkNode(x_44, x_43);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
if (lean::is_scalar(x_38)) {
 x_47 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_47 = x_38;
}
lean::cnstr_set(x_47, 0, x_32);
lean::cnstr_set(x_47, 1, x_34);
lean::cnstr_set(x_47, 2, x_36);
lean::cnstr_set(x_47, 3, x_46);
if (x_25 == 0)
{
uint8 x_48; obj* x_49; obj* x_50; 
x_48 = 0;
if (lean::is_scalar(x_26)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_26;
}
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_48);
x_50 = x_49;
x_11 = x_50;
x_12 = x_29;
goto lbl_13;
}
else
{
uint8 x_51; obj* x_52; obj* x_53; 
x_51 = 1;
if (lean::is_scalar(x_26)) {
 x_52 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_52 = x_26;
}
lean::cnstr_set(x_52, 0, x_47);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_51);
x_53 = x_52;
x_11 = x_53;
x_12 = x_29;
goto lbl_13;
}
}
else
{
obj* x_54; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_54 = lean::cnstr_get(x_17, 1);
lean::inc(x_54);
lean::dec(x_17);
x_57 = lean::cnstr_get(x_23, 0);
x_59 = lean::cnstr_get(x_23, 1);
x_61 = lean::cnstr_get(x_23, 2);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 3);
 x_63 = x_23;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_23);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_66 = x_27;
} else {
 lean::inc(x_64);
 lean::dec(x_27);
 x_66 = lean::box(0);
}
lean::inc(x_1);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set(x_68, 1, x_1);
x_69 = lean::box(3);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
x_71 = l_List_reverse___rarg(x_70);
x_72 = l_Lean_Parser_noKind;
x_73 = l_Lean_Parser_Syntax_mkNode(x_72, x_71);
if (lean::is_scalar(x_66)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_66;
}
lean::cnstr_set(x_74, 0, x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_57);
lean::cnstr_set(x_75, 1, x_59);
lean::cnstr_set(x_75, 2, x_61);
lean::cnstr_set(x_75, 3, x_74);
if (x_25 == 0)
{
uint8 x_76; obj* x_77; obj* x_78; 
x_76 = 0;
if (lean::is_scalar(x_26)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_26;
}
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_76);
x_78 = x_77;
x_11 = x_78;
x_12 = x_54;
goto lbl_13;
}
else
{
uint8 x_79; obj* x_80; obj* x_81; 
x_79 = 1;
if (lean::is_scalar(x_26)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_26;
}
lean::cnstr_set(x_80, 0, x_75);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_79);
x_81 = x_80;
x_11 = x_81;
x_12 = x_54;
goto lbl_13;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_97; 
x_82 = lean::cnstr_get(x_11, 0);
x_84 = lean::cnstr_get(x_11, 1);
x_86 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_88 = x_11;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_11);
 x_88 = lean::box(0);
}
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_82);
lean::cnstr_set(x_89, 1, x_1);
lean::inc(x_89);
x_91 = l_List_reverse___rarg(x_89);
x_92 = l_Lean_Parser_noKind;
x_93 = l_Lean_Parser_Syntax_mkNode(x_92, x_91);
lean::inc(x_84);
x_95 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_0, x_89, x_10, x_3, x_4, x_84, x_12);
lean::dec(x_10);
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_88);
lean::dec(x_93);
lean::dec(x_84);
x_102 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_104 = x_95;
} else {
 lean::inc(x_102);
 lean::dec(x_95);
 x_104 = lean::box(0);
}
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_97);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_102);
return x_106;
}
else
{
uint8 x_107; 
x_107 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (x_107 == 0)
{
obj* x_108; obj* x_110; obj* x_111; obj* x_114; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_108 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_110 = x_95;
} else {
 lean::inc(x_108);
 lean::dec(x_95);
 x_110 = lean::box(0);
}
x_111 = lean::cnstr_get(x_97, 0);
lean::inc(x_111);
lean::dec(x_97);
x_114 = lean::cnstr_get(x_111, 2);
lean::inc(x_114);
lean::dec(x_111);
x_117 = l_mjoin___rarg___closed__1;
x_118 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_118, 0, x_114);
lean::closure_set(x_118, 1, x_117);
x_119 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_119, 0, x_118);
if (lean::is_scalar(x_88)) {
 x_120 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_120 = x_88;
}
lean::cnstr_set(x_120, 0, x_93);
lean::cnstr_set(x_120, 1, x_84);
lean::cnstr_set(x_120, 2, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_120);
if (lean::is_scalar(x_110)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_110;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_108);
return x_122;
}
else
{
obj* x_126; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_88);
lean::dec(x_93);
lean::dec(x_84);
x_126 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_128 = x_95;
} else {
 lean::inc(x_126);
 lean::dec(x_95);
 x_128 = lean::box(0);
}
x_129 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_97);
if (lean::is_scalar(x_128)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_128;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_126);
return x_130;
}
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_10);
x_136 = lean::cnstr_get(x_11, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_139 = x_11;
} else {
 lean::inc(x_136);
 lean::dec(x_11);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_136);
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_138);
x_141 = x_140;
x_142 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_12);
return x_142;
}
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
lean::dec(x_1);
lean::dec(x_0);
x_145 = lean::box(0);
x_146 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_147 = l_mjoin___rarg___closed__1;
x_148 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_146, x_147, x_145, x_145, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_148;
}
}
}
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_add(x_5, x_7);
lean::dec(x_5);
x_10 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_0, x_6, x_8, x_1, x_2, x_3, x_4);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_10, 0);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_16 = x_10;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_14);
return x_19;
}
}
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_3);
x_6 = l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3(x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_14 == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_15 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_17 = x_6;
} else {
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
lean::dec(x_7);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_mjoin___rarg___closed__1;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_25, 0, x_21);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_3);
lean::cnstr_set(x_28, 2, x_26);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_15);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_3);
x_31 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_33 = x_6;
} else {
 lean::inc(x_31);
 lean::dec(x_6);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_1);
x_3 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_5 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_0);
lean::dec(x_5);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_7);
lean::dec(x_7);
x_11 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
return x_11;
}
}
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = l_Lean_Parser_maxPrec;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_command_attrInstance;
x_13 = l_Lean_Parser_command_attrInstance_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_12, x_11, x_13);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_maxPrec;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_Lean_Parser_command_attrInstance_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_attrInstance;
x_5 = l_Lean_Parser_command_attrInstance_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declAttributes() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declAttributes");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1___spec__1(obj* x_0) {
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1___spec__1(x_4);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_13 = l_Lean_Parser_command_attrInstance_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::apply_1(x_14, x_10);
x_18 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_6;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_27; obj* x_28; obj* x_31; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_8, 0);
lean::inc(x_24);
lean::dec(x_8);
x_27 = l_Lean_Parser_command_attrInstance_HasView;
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
lean::dec(x_27);
x_31 = lean::apply_1(x_28, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
if (lean::is_scalar(x_6)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_6;
}
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_7);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_24, 0);
lean::inc(x_35);
lean::dec(x_24);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_35);
if (lean::is_scalar(x_6)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_6;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_31);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_7);
return x_42;
}
}
}
}
}
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1___spec__1(x_3);
x_9 = l_List_join___main___rarg(x_8);
x_10 = l_Lean_Parser_noKind;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
x_12 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_command_declAttributes;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_19 = lean::cnstr_get(x_5, 0);
lean::inc(x_19);
lean::dec(x_5);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_command_declAttributes;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
}
else
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
lean::dec(x_1);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
if (lean::obj_tag(x_5) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_11);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_declAttributes;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_38 = lean::cnstr_get(x_5, 0);
lean::inc(x_38);
lean::dec(x_5);
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_12);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_11);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_declAttributes;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
return x_46;
}
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 x_8 = x_2;
} else {
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = l_Lean_Parser_command_attrInstance_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_13 = lean::apply_1(x_10, x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_25 = x_4;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_4);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Parser_command_attrInstance_HasView;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
lean::dec(x_26);
x_30 = lean::apply_1(x_27, x_18);
x_31 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(x_0, x_1, x_23);
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_21, 0);
lean::inc(x_32);
lean::dec(x_21);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_30);
lean::cnstr_set(x_37, 1, x_36);
if (lean::is_scalar(x_25)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_25;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
case 3:
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_39);
if (lean::is_scalar(x_25)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_25;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_31);
return x_41;
}
default:
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_21);
x_43 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_30);
lean::cnstr_set(x_44, 1, x_43);
if (lean::is_scalar(x_25)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_25;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_31);
return x_45;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_Lean_Parser_command_attrInstance_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::mk_string(",");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_0);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2;
x_12 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
x_13 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(x_11, x_12, x_8);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_0);
return x_14;
}
}
}
obj* l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
x_36 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(0);
if (lean::obj_tag(x_27) == 0)
{
obj* x_38; obj* x_39; 
x_38 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_18);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set(x_39, 2, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_27, 0);
lean::inc(x_40);
lean::dec(x_27);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_43);
x_47 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
case 3:
{
obj* x_49; obj* x_50; 
x_49 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_18);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_37);
return x_50;
}
default:
{
obj* x_52; obj* x_53; 
lean::dec(x_40);
x_52 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_18);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_37);
return x_53;
}
}
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_60; obj* x_61; obj* x_62; 
x_54 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_56 = x_36;
} else {
 lean::inc(x_54);
 lean::dec(x_36);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2;
x_61 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
x_62 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(x_60, x_61, x_57);
if (lean::obj_tag(x_27) == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_56);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_18);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_64);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_27, 0);
lean::inc(x_66);
lean::dec(x_27);
switch (lean::obj_tag(x_66)) {
case 0:
{
obj* x_69; obj* x_72; obj* x_73; 
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
lean::dec(x_66);
if (lean::is_scalar(x_56)) {
 x_72 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_72 = x_56;
}
lean::cnstr_set(x_72, 0, x_69);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_18);
lean::cnstr_set(x_73, 1, x_62);
lean::cnstr_set(x_73, 2, x_72);
return x_73;
}
case 3:
{
obj* x_75; obj* x_76; 
lean::dec(x_56);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_18);
lean::cnstr_set(x_76, 1, x_62);
lean::cnstr_set(x_76, 2, x_75);
return x_76;
}
default:
{
obj* x_79; obj* x_80; 
lean::dec(x_56);
lean::dec(x_66);
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_18);
lean::cnstr_set(x_80, 1, x_62);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declAttributes_HasView_x_27;
return x_0;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(0ul);
x_11 = lean::nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_sub(x_5, x_12);
if (x_3 == 0)
{
obj* x_23; obj* x_24; 
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_0);
x_23 = lean::apply_4(x_0, x_6, x_7, x_8, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_24, 0);
x_31 = lean::cnstr_get(x_24, 1);
x_33 = lean::cnstr_get(x_24, 2);
if (lean::is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_29);
x_37 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_35)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_35;
}
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_31);
lean::cnstr_set(x_38, 2, x_37);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_38);
x_17 = x_39;
x_18 = x_26;
goto lbl_19;
}
else
{
obj* x_40; obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_23, 1);
lean::inc(x_40);
lean::dec(x_23);
x_43 = lean::cnstr_get(x_24, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_exclusive(x_24)) {
 x_46 = x_24;
} else {
 lean::inc(x_43);
 lean::dec(x_24);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
x_17 = x_48;
x_18 = x_40;
goto lbl_19;
}
}
else
{
obj* x_49; obj* x_54; obj* x_55; 
x_49 = lean::box(0);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_0);
x_54 = lean::apply_4(x_0, x_6, x_7, x_8, x_9);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = lean::cnstr_get(x_55, 0);
x_62 = lean::cnstr_get(x_55, 1);
x_64 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 x_66 = x_55;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_55);
 x_66 = lean::box(0);
}
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_60);
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_66)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_66;
}
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_62);
lean::cnstr_set(x_69, 2, x_68);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_69);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_8);
x_17 = x_70;
x_18 = x_57;
goto lbl_19;
}
else
{
uint8 x_72; 
x_72 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_72 == 0)
{
obj* x_73; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::cnstr_get(x_73, 2);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_mjoin___rarg___closed__1;
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_80, 0, x_76);
lean::closure_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_49);
lean::cnstr_set(x_82, 1, x_8);
lean::cnstr_set(x_82, 2, x_81);
x_17 = x_82;
x_18 = x_57;
goto lbl_19;
}
else
{
lean::dec(x_8);
x_17 = x_70;
x_18 = x_57;
goto lbl_19;
}
}
}
else
{
uint8 x_84; 
x_84 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (x_84 == 0)
{
obj* x_85; obj* x_88; obj* x_91; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_85 = lean::cnstr_get(x_54, 1);
lean::inc(x_85);
lean::dec(x_54);
x_88 = lean::cnstr_get(x_55, 0);
lean::inc(x_88);
lean::dec(x_55);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_94 = l_mjoin___rarg___closed__1;
x_95 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_95, 0, x_91);
lean::closure_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_49);
lean::cnstr_set(x_97, 1, x_8);
lean::cnstr_set(x_97, 2, x_96);
x_17 = x_97;
x_18 = x_85;
goto lbl_19;
}
else
{
obj* x_99; obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_8);
x_99 = lean::cnstr_get(x_54, 1);
lean::inc(x_99);
lean::dec(x_54);
x_102 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_104 = x_55;
} else {
 lean::inc(x_102);
 lean::dec(x_55);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_84);
x_106 = x_105;
x_17 = x_106;
x_18 = x_99;
goto lbl_19;
}
}
}
lbl_16:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_107; 
x_107 = lean::cnstr_get(x_14, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_114; obj* x_116; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
x_114 = lean::cnstr_get(x_14, 1);
x_116 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_118 = x_14;
} else {
 lean::inc(x_114);
 lean::inc(x_116);
 lean::dec(x_14);
 x_118 = lean::box(0);
}
x_119 = l_List_reverse___rarg(x_4);
x_120 = l_Lean_Parser_noKind;
x_121 = l_Lean_Parser_Syntax_mkNode(x_120, x_119);
x_122 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_118)) {
 x_123 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_123 = x_118;
}
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_114);
lean::cnstr_set(x_123, 2, x_122);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_123);
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_15);
return x_125;
}
else
{
obj* x_126; obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_142; obj* x_143; obj* x_145; obj* x_148; 
x_126 = lean::cnstr_get(x_14, 1);
x_128 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_set(x_14, 1, lean::box(0));
 lean::cnstr_set(x_14, 2, lean::box(0));
 x_130 = x_14;
} else {
 lean::inc(x_126);
 lean::inc(x_128);
 lean::dec(x_14);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_set(x_107, 0, lean::box(0));
 x_133 = x_107;
} else {
 lean::inc(x_131);
 lean::dec(x_107);
 x_133 = lean::box(0);
}
x_137 = lean::box(0);
lean::inc(x_126);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_1);
x_142 = lean::apply_4(x_1, x_6, x_7, x_126, x_15);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
x_148 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_143);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_151; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
x_149 = lean::cnstr_get(x_148, 0);
x_151 = lean::cnstr_get(x_148, 1);
x_153 = lean::cnstr_get(x_148, 2);
if (lean::is_exclusive(x_148)) {
 x_155 = x_148;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::inc(x_153);
 lean::dec(x_148);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_156 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_156 = x_133;
}
lean::cnstr_set(x_156, 0, x_149);
x_157 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_155)) {
 x_158 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_158 = x_155;
}
lean::cnstr_set(x_158, 0, x_156);
lean::cnstr_set(x_158, 1, x_151);
lean::cnstr_set(x_158, 2, x_157);
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_153, x_158);
if (lean::obj_tag(x_159) == 0)
{
lean::dec(x_130);
lean::dec(x_126);
x_134 = x_159;
x_135 = x_145;
goto lbl_136;
}
else
{
uint8 x_162; 
x_162 = lean::cnstr_get_scalar<uint8>(x_159, sizeof(void*)*1);
if (x_162 == 0)
{
obj* x_163; obj* x_166; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_163 = lean::cnstr_get(x_159, 0);
lean::inc(x_163);
lean::dec(x_159);
x_166 = lean::cnstr_get(x_163, 2);
lean::inc(x_166);
lean::dec(x_163);
x_169 = l_mjoin___rarg___closed__1;
x_170 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_170, 0, x_166);
lean::closure_set(x_170, 1, x_169);
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
if (lean::is_scalar(x_130)) {
 x_172 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_172 = x_130;
}
lean::cnstr_set(x_172, 0, x_137);
lean::cnstr_set(x_172, 1, x_126);
lean::cnstr_set(x_172, 2, x_171);
x_134 = x_172;
x_135 = x_145;
goto lbl_136;
}
else
{
lean::dec(x_130);
lean::dec(x_126);
x_134 = x_159;
x_135 = x_145;
goto lbl_136;
}
}
}
else
{
uint8 x_175; 
x_175 = lean::cnstr_get_scalar<uint8>(x_148, sizeof(void*)*1);
if (x_175 == 0)
{
obj* x_176; obj* x_179; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_176 = lean::cnstr_get(x_148, 0);
lean::inc(x_176);
lean::dec(x_148);
x_179 = lean::cnstr_get(x_176, 2);
lean::inc(x_179);
lean::dec(x_176);
x_182 = l_mjoin___rarg___closed__1;
x_183 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_183, 0, x_179);
lean::closure_set(x_183, 1, x_182);
if (lean::is_scalar(x_133)) {
 x_184 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_184 = x_133;
}
lean::cnstr_set(x_184, 0, x_183);
if (lean::is_scalar(x_130)) {
 x_185 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_185 = x_130;
}
lean::cnstr_set(x_185, 0, x_137);
lean::cnstr_set(x_185, 1, x_126);
lean::cnstr_set(x_185, 2, x_184);
x_134 = x_185;
x_135 = x_145;
goto lbl_136;
}
else
{
obj* x_189; obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_130);
lean::dec(x_133);
lean::dec(x_126);
x_189 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_191 = x_148;
} else {
 lean::inc(x_189);
 lean::dec(x_148);
 x_191 = lean::box(0);
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_189);
lean::cnstr_set_scalar(x_192, sizeof(void*)*1, x_175);
x_193 = x_192;
x_134 = x_193;
x_135 = x_145;
goto lbl_136;
}
}
lbl_136:
{
if (lean::obj_tag(x_134) == 0)
{
obj* x_194; 
x_194 = lean::cnstr_get(x_134, 0);
lean::inc(x_194);
if (lean::obj_tag(x_194) == 0)
{
obj* x_201; obj* x_203; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
x_201 = lean::cnstr_get(x_134, 1);
x_203 = lean::cnstr_get(x_134, 2);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_205 = x_134;
} else {
 lean::inc(x_201);
 lean::inc(x_203);
 lean::dec(x_134);
 x_205 = lean::box(0);
}
x_206 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_206, 0, x_131);
lean::cnstr_set(x_206, 1, x_4);
x_207 = l_List_reverse___rarg(x_206);
x_208 = l_Lean_Parser_noKind;
x_209 = l_Lean_Parser_Syntax_mkNode(x_208, x_207);
x_210 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_205)) {
 x_211 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_211 = x_205;
}
lean::cnstr_set(x_211, 0, x_209);
lean::cnstr_set(x_211, 1, x_201);
lean::cnstr_set(x_211, 2, x_210);
x_212 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_203, x_211);
x_213 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_212);
x_214 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_214, 0, x_213);
lean::cnstr_set(x_214, 1, x_135);
return x_214;
}
else
{
obj* x_215; obj* x_217; obj* x_220; obj* x_223; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
x_215 = lean::cnstr_get(x_134, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_134, 2);
lean::inc(x_217);
lean::dec(x_134);
x_220 = lean::cnstr_get(x_194, 0);
lean::inc(x_220);
lean::dec(x_194);
x_223 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_223, 0, x_131);
lean::cnstr_set(x_223, 1, x_4);
x_224 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_224, 0, x_220);
lean::cnstr_set(x_224, 1, x_223);
x_225 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_2, x_224, x_13, x_6, x_7, x_215, x_135);
lean::dec(x_13);
x_227 = lean::cnstr_get(x_225, 0);
x_229 = lean::cnstr_get(x_225, 1);
if (lean::is_exclusive(x_225)) {
 x_231 = x_225;
} else {
 lean::inc(x_227);
 lean::inc(x_229);
 lean::dec(x_225);
 x_231 = lean::box(0);
}
x_232 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_217, x_227);
x_233 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_232);
if (lean::is_scalar(x_231)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_231;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_229);
return x_234;
}
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_131);
x_242 = lean::cnstr_get(x_134, 0);
x_244 = lean::cnstr_get_scalar<uint8>(x_134, sizeof(void*)*1);
if (lean::is_exclusive(x_134)) {
 x_245 = x_134;
} else {
 lean::inc(x_242);
 lean::dec(x_134);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_242);
lean::cnstr_set_scalar(x_246, sizeof(void*)*1, x_244);
x_247 = x_246;
x_248 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_247);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_135);
return x_249;
}
}
}
}
else
{
obj* x_256; uint8 x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
x_256 = lean::cnstr_get(x_14, 0);
x_258 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_259 = x_14;
} else {
 lean::inc(x_256);
 lean::dec(x_14);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_256);
lean::cnstr_set_scalar(x_260, sizeof(void*)*1, x_258);
x_261 = x_260;
x_262 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_262, 0, x_261);
lean::cnstr_set(x_262, 1, x_15);
return x_262;
}
}
lbl_19:
{
if (lean::obj_tag(x_17) == 0)
{
x_14 = x_17;
x_15 = x_18;
goto lbl_16;
}
else
{
obj* x_263; uint8 x_265; obj* x_266; obj* x_267; 
x_263 = lean::cnstr_get(x_17, 0);
x_265 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_266 = x_17;
} else {
 lean::inc(x_263);
 lean::dec(x_17);
 x_266 = lean::box(0);
}
x_267 = lean::cnstr_get(x_263, 3);
lean::inc(x_267);
if (lean::obj_tag(x_267) == 0)
{
obj* x_269; obj* x_271; obj* x_273; obj* x_275; obj* x_276; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_269 = lean::cnstr_get(x_263, 0);
x_271 = lean::cnstr_get(x_263, 1);
x_273 = lean::cnstr_get(x_263, 2);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_release(x_263, 3);
 x_275 = x_263;
} else {
 lean::inc(x_269);
 lean::inc(x_271);
 lean::inc(x_273);
 lean::dec(x_263);
 x_275 = lean::box(0);
}
x_276 = lean::box(3);
lean::inc(x_4);
x_278 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_278, 0, x_276);
lean::cnstr_set(x_278, 1, x_4);
x_279 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_279, 0, x_276);
lean::cnstr_set(x_279, 1, x_278);
x_280 = l_List_reverse___rarg(x_279);
x_281 = l_Lean_Parser_noKind;
x_282 = l_Lean_Parser_Syntax_mkNode(x_281, x_280);
x_283 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_283, 0, x_282);
if (lean::is_scalar(x_275)) {
 x_284 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_284 = x_275;
}
lean::cnstr_set(x_284, 0, x_269);
lean::cnstr_set(x_284, 1, x_271);
lean::cnstr_set(x_284, 2, x_273);
lean::cnstr_set(x_284, 3, x_283);
if (x_265 == 0)
{
uint8 x_285; obj* x_286; obj* x_287; 
x_285 = 0;
if (lean::is_scalar(x_266)) {
 x_286 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_286 = x_266;
}
lean::cnstr_set(x_286, 0, x_284);
lean::cnstr_set_scalar(x_286, sizeof(void*)*1, x_285);
x_287 = x_286;
x_14 = x_287;
x_15 = x_18;
goto lbl_16;
}
else
{
uint8 x_288; obj* x_289; obj* x_290; 
x_288 = 1;
if (lean::is_scalar(x_266)) {
 x_289 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_289 = x_266;
}
lean::cnstr_set(x_289, 0, x_284);
lean::cnstr_set_scalar(x_289, sizeof(void*)*1, x_288);
x_290 = x_289;
x_14 = x_290;
x_15 = x_18;
goto lbl_16;
}
}
else
{
obj* x_291; obj* x_293; obj* x_295; obj* x_297; obj* x_298; obj* x_300; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; 
x_291 = lean::cnstr_get(x_263, 0);
x_293 = lean::cnstr_get(x_263, 1);
x_295 = lean::cnstr_get(x_263, 2);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_release(x_263, 3);
 x_297 = x_263;
} else {
 lean::inc(x_291);
 lean::inc(x_293);
 lean::inc(x_295);
 lean::dec(x_263);
 x_297 = lean::box(0);
}
x_298 = lean::cnstr_get(x_267, 0);
if (lean::is_exclusive(x_267)) {
 x_300 = x_267;
} else {
 lean::inc(x_298);
 lean::dec(x_267);
 x_300 = lean::box(0);
}
lean::inc(x_4);
x_302 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_4);
x_303 = lean::box(3);
x_304 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_302);
x_305 = l_List_reverse___rarg(x_304);
x_306 = l_Lean_Parser_noKind;
x_307 = l_Lean_Parser_Syntax_mkNode(x_306, x_305);
if (lean::is_scalar(x_300)) {
 x_308 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_308 = x_300;
}
lean::cnstr_set(x_308, 0, x_307);
if (lean::is_scalar(x_297)) {
 x_309 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_309 = x_297;
}
lean::cnstr_set(x_309, 0, x_291);
lean::cnstr_set(x_309, 1, x_293);
lean::cnstr_set(x_309, 2, x_295);
lean::cnstr_set(x_309, 3, x_308);
if (x_265 == 0)
{
uint8 x_310; obj* x_311; obj* x_312; 
x_310 = 0;
if (lean::is_scalar(x_266)) {
 x_311 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_311 = x_266;
}
lean::cnstr_set(x_311, 0, x_309);
lean::cnstr_set_scalar(x_311, sizeof(void*)*1, x_310);
x_312 = x_311;
x_14 = x_312;
x_15 = x_18;
goto lbl_16;
}
else
{
uint8 x_313; obj* x_314; obj* x_315; 
x_313 = 1;
if (lean::is_scalar(x_266)) {
 x_314 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_314 = x_266;
}
lean::cnstr_set(x_314, 0, x_309);
lean::cnstr_set_scalar(x_314, sizeof(void*)*1, x_313);
x_315 = x_314;
x_14 = x_315;
x_15 = x_18;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_319 = lean::box(0);
x_320 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_321 = l_mjoin___rarg___closed__1;
x_322 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_320, x_321, x_319, x_319, x_6, x_7, x_8, x_9);
lean::dec(x_7);
lean::dec(x_6);
return x_322;
}
}
}
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_7 = l_String_OldIterator_remaining___main(x_5);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_7, x_9);
lean::dec(x_7);
x_12 = 0;
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_12, x_8, x_10, x_3, x_4, x_5, x_6);
lean::dec(x_10);
x_15 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 x_19 = x_13;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_13);
 x_19 = lean::box(0);
}
x_20 = l_Lean_Parser_finishCommentBlock___closed__2;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_15);
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_19; obj* x_22; 
x_0 = lean::mk_string("@[");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string(",");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_7, x_5);
lean::dec(x_5);
x_10 = lean::mk_string("]");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_1);
lean::dec(x_10);
x_13 = lean::box(0);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_13);
lean::dec(x_11);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_14);
lean::dec(x_14);
lean::dec(x_8);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_16);
lean::dec(x_16);
lean::dec(x_2);
x_22 = l_Lean_Parser_tokens___rarg(x_19);
lean::dec(x_19);
return x_22;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; obj* x_12; 
x_10 = lean::unbox(x_2);
x_11 = lean::unbox(x_3);
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_5);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
x_8 = l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("@[");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::mk_string(",");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_9);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
x_18 = 1;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_16);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::mk_string("]");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_25, 0, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_26, 0, x_22);
lean::closure_set(x_26, 1, x_9);
lean::closure_set(x_26, 2, x_25);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_10);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_declAttributes;
x_32 = l_Lean_Parser_command_declAttributes_HasView;
x_33 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_31, x_30, x_32);
lean::dec(x_30);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_33;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string("@[");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string(",");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
x_14 = 1;
x_15 = lean::box(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_12);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::mk_string("]");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_21, 0, x_18);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_5);
lean::closure_set(x_22, 2, x_21);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_16);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* l_Lean_Parser_command_declAttributes_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_declAttributes;
x_5 = l_Lean_Parser_command_declAttributes_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_visibility() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("visibility");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_visibility;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_visibility;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_command_visibility_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_visibility;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_visibility;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("visibility");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_visibility_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0ul);
x_60 = lean::nat_dec_eq(x_41, x_59);
lean::dec(x_41);
if (x_60 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_62; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_26;
}
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
case 3:
{
obj* x_68; 
lean::dec(x_26);
x_68 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1;
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_56);
lean::dec(x_26);
x_71 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_56, 0);
lean::inc(x_72);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_26;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
case 3:
{
obj* x_78; 
lean::dec(x_26);
x_78 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2;
return x_78;
}
default:
{
obj* x_81; 
lean::dec(x_56);
lean::dec(x_26);
x_81 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2;
return x_81;
}
}
}
}
else
{
obj* x_86; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_86 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_86;
}
}
}
}
}
}
}
else
{
obj* x_89; 
lean::dec(x_8);
lean::dec(x_17);
x_89 = l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3;
return x_89;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_visibility_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_visibility_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_visibility_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declModifiers() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declModifiers");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = l_Lean_Parser_noKind;
x_4 = l_Lean_Parser_Syntax_mkNode(x_3, x_2);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = l_Lean_Parser_noKind;
x_4 = l_Lean_Parser_Syntax_mkNode(x_3, x_2);
x_5 = l_Lean_Parser_Syntax_mkNode(x_3, x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_15; 
x_15 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_13 = x_15;
goto lbl_14;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_Lean_Parser_command_docComment_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_12);
x_25 = l_Lean_Parser_noKind;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_13 = x_26;
goto lbl_14;
}
lbl_14:
{
obj* x_27; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; 
x_29 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_27 = x_29;
goto lbl_28;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_30 = lean::cnstr_get(x_3, 0);
lean::inc(x_30);
lean::dec(x_3);
x_33 = l_Lean_Parser_command_declAttributes_HasView;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::apply_1(x_34, x_30);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_12);
x_39 = l_Lean_Parser_noKind;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_27 = x_40;
goto lbl_28;
}
lbl_28:
{
obj* x_41; 
if (lean::obj_tag(x_5) == 0)
{
obj* x_43; 
x_43 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_41 = x_43;
goto lbl_42;
}
else
{
obj* x_44; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_44 = lean::cnstr_get(x_5, 0);
lean::inc(x_44);
lean::dec(x_5);
x_47 = l_Lean_Parser_command_visibility_HasView;
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::apply_1(x_48, x_44);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_12);
x_53 = l_Lean_Parser_noKind;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
x_41 = x_54;
goto lbl_42;
}
lbl_42:
{
obj* x_55; obj* x_56; 
if (lean::obj_tag(x_7) == 0)
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_58 = l_Lean_Parser_Term_binderContent_HasView_x_27___elambda__1___closed__2;
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_41);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_27);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_13);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_Lean_Parser_command_declModifiers;
x_63 = l_Lean_Parser_Syntax_mkNode(x_62, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_67; 
x_64 = lean::cnstr_get(x_9, 0);
lean::inc(x_64);
lean::dec(x_9);
x_67 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_55 = x_67;
x_56 = x_64;
goto lbl_57;
}
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_7, 0);
lean::inc(x_68);
lean::dec(x_7);
if (lean::obj_tag(x_68) == 0)
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_71 = l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2;
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_41);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_27);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_13);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_Lean_Parser_command_declModifiers;
x_76 = l_Lean_Parser_Syntax_mkNode(x_75, x_74);
return x_76;
}
else
{
obj* x_77; obj* x_80; 
x_77 = lean::cnstr_get(x_9, 0);
lean::inc(x_77);
lean::dec(x_9);
x_80 = l_Lean_Parser_command_notation_HasView_x_27___elambda__1___closed__1;
x_55 = x_80;
x_56 = x_77;
goto lbl_57;
}
}
else
{
obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_81 = lean::cnstr_get(x_68, 0);
lean::inc(x_81);
lean::dec(x_68);
x_84 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_84, 0, x_81);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_12);
x_86 = l_Lean_Parser_noKind;
x_87 = l_Lean_Parser_Syntax_mkNode(x_86, x_85);
if (lean::obj_tag(x_9) == 0)
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_88 = l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_41);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_27);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_13);
lean::cnstr_set(x_92, 1, x_91);
x_93 = l_Lean_Parser_command_declModifiers;
x_94 = l_Lean_Parser_Syntax_mkNode(x_93, x_92);
return x_94;
}
else
{
obj* x_95; 
x_95 = lean::cnstr_get(x_9, 0);
lean::inc(x_95);
lean::dec(x_9);
x_55 = x_87;
x_56 = x_95;
goto lbl_57;
}
}
}
lbl_57:
{
if (lean::obj_tag(x_56) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1;
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_55);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_41);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_27);
lean::cnstr_set(x_101, 1, x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_13);
lean::cnstr_set(x_102, 1, x_101);
x_103 = l_Lean_Parser_command_declModifiers;
x_104 = l_Lean_Parser_Syntax_mkNode(x_103, x_102);
return x_104;
}
else
{
obj* x_105; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_105 = lean::cnstr_get(x_56, 0);
lean::inc(x_105);
lean::dec(x_56);
x_108 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_108, 0, x_105);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_12);
x_110 = l_Lean_Parser_noKind;
x_111 = l_Lean_Parser_Syntax_mkNode(x_110, x_109);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_12);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_55);
lean::cnstr_set(x_113, 1, x_112);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_41);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_27);
lean::cnstr_set(x_115, 1, x_114);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_13);
lean::cnstr_set(x_116, 1, x_115);
x_117 = l_Lean_Parser_command_declModifiers;
x_118 = l_Lean_Parser_Syntax_mkNode(x_117, x_116);
return x_118;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_visibility_HasView;
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
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_declAttributes_HasView;
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
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_docComment_HasView;
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
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3;
x_0 = x_4;
goto lbl_1;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::box(0);
x_0 = x_12;
goto lbl_1;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = l_Lean_Parser_command_docComment_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_15);
if (lean::is_scalar(x_7)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_7;
}
lean::cnstr_set(x_23, 0, x_22);
x_0 = x_23;
goto lbl_1;
}
else
{
obj* x_27; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_7);
x_27 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3;
x_0 = x_27;
goto lbl_1;
}
}
}
lbl_1:
{
obj* x_28; obj* x_30; obj* x_31; 
x_30 = lean::box(3);
x_31 = l_Lean_Parser_Syntax_asNode___main(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2;
x_28 = x_32;
goto lbl_29;
}
else
{
obj* x_33; obj* x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_set(x_31, 0, lean::box(0));
 x_35 = x_31;
} else {
 lean::inc(x_33);
 lean::dec(x_31);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; 
lean::dec(x_35);
x_40 = lean::box(0);
x_28 = x_40;
goto lbl_29;
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_46; obj* x_47; obj* x_50; obj* x_51; 
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
lean::dec(x_36);
x_46 = l_Lean_Parser_command_declAttributes_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_43);
if (lean::is_scalar(x_35)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_35;
}
lean::cnstr_set(x_51, 0, x_50);
x_28 = x_51;
goto lbl_29;
}
else
{
obj* x_55; 
lean::dec(x_41);
lean::dec(x_35);
lean::dec(x_36);
x_55 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2;
x_28 = x_55;
goto lbl_29;
}
}
}
lbl_29:
{
obj* x_56; obj* x_58; obj* x_59; 
x_58 = lean::box(3);
x_59 = l_Lean_Parser_Syntax_asNode___main(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; 
x_60 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1;
x_56 = x_60;
goto lbl_57;
}
else
{
obj* x_61; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_set(x_59, 0, lean::box(0));
 x_63 = x_59;
} else {
 lean::inc(x_61);
 lean::dec(x_59);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
if (lean::obj_tag(x_64) == 0)
{
obj* x_68; 
lean::dec(x_63);
x_68 = lean::box(0);
x_56 = x_68;
goto lbl_57;
}
else
{
obj* x_69; 
x_69 = lean::cnstr_get(x_64, 1);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_74; obj* x_75; obj* x_78; obj* x_79; 
x_71 = lean::cnstr_get(x_64, 0);
lean::inc(x_71);
lean::dec(x_64);
x_74 = l_Lean_Parser_command_visibility_HasView;
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
lean::dec(x_74);
x_78 = lean::apply_1(x_75, x_71);
if (lean::is_scalar(x_63)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_63;
}
lean::cnstr_set(x_79, 0, x_78);
x_56 = x_79;
goto lbl_57;
}
else
{
obj* x_83; 
lean::dec(x_64);
lean::dec(x_69);
lean::dec(x_63);
x_83 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1;
x_56 = x_83;
goto lbl_57;
}
}
}
lbl_57:
{
obj* x_84; obj* x_86; obj* x_87; 
x_86 = lean::box(3);
x_87 = l_Lean_Parser_Syntax_asNode___main(x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; 
x_88 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_84 = x_88;
goto lbl_85;
}
else
{
obj* x_89; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_set(x_87, 0, lean::box(0));
 x_91 = x_87;
} else {
 lean::inc(x_89);
 lean::dec(x_87);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; 
lean::dec(x_91);
x_96 = lean::box(0);
x_84 = x_96;
goto lbl_85;
}
else
{
obj* x_97; 
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; 
x_99 = lean::cnstr_get(x_92, 0);
lean::inc(x_99);
lean::dec(x_92);
switch (lean::obj_tag(x_99)) {
case 0:
{
obj* x_102; obj* x_105; obj* x_106; 
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
lean::dec(x_99);
if (lean::is_scalar(x_91)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_91;
}
lean::cnstr_set(x_105, 0, x_102);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
x_84 = x_106;
goto lbl_85;
}
case 3:
{
obj* x_108; 
lean::dec(x_91);
x_108 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_84 = x_108;
goto lbl_85;
}
default:
{
obj* x_111; 
lean::dec(x_91);
lean::dec(x_99);
x_111 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_84 = x_111;
goto lbl_85;
}
}
}
else
{
obj* x_115; 
lean::dec(x_97);
lean::dec(x_91);
lean::dec(x_92);
x_115 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_84 = x_115;
goto lbl_85;
}
}
}
lbl_85:
{
obj* x_116; obj* x_117; 
x_116 = lean::box(3);
x_117 = l_Lean_Parser_Syntax_asNode___main(x_116);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; 
x_118 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_119 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_119, 0, x_0);
lean::cnstr_set(x_119, 1, x_28);
lean::cnstr_set(x_119, 2, x_56);
lean::cnstr_set(x_119, 3, x_84);
lean::cnstr_set(x_119, 4, x_118);
return x_119;
}
else
{
obj* x_120; obj* x_122; obj* x_123; 
x_120 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_set(x_117, 0, lean::box(0));
 x_122 = x_117;
} else {
 lean::inc(x_120);
 lean::dec(x_117);
 x_122 = lean::box(0);
}
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; obj* x_128; 
lean::dec(x_122);
x_127 = lean::box(0);
x_128 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_128, 0, x_0);
lean::cnstr_set(x_128, 1, x_28);
lean::cnstr_set(x_128, 2, x_56);
lean::cnstr_set(x_128, 3, x_84);
lean::cnstr_set(x_128, 4, x_127);
return x_128;
}
else
{
obj* x_129; 
x_129 = lean::cnstr_get(x_123, 1);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
obj* x_131; 
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
switch (lean::obj_tag(x_131)) {
case 0:
{
obj* x_134; obj* x_137; obj* x_138; obj* x_139; 
x_134 = lean::cnstr_get(x_131, 0);
lean::inc(x_134);
lean::dec(x_131);
if (lean::is_scalar(x_122)) {
 x_137 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_137 = x_122;
}
lean::cnstr_set(x_137, 0, x_134);
x_138 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_138, 0, x_137);
x_139 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_139, 0, x_0);
lean::cnstr_set(x_139, 1, x_28);
lean::cnstr_set(x_139, 2, x_56);
lean::cnstr_set(x_139, 3, x_84);
lean::cnstr_set(x_139, 4, x_138);
return x_139;
}
case 3:
{
obj* x_141; obj* x_142; 
lean::dec(x_122);
x_141 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_142 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_142, 0, x_0);
lean::cnstr_set(x_142, 1, x_28);
lean::cnstr_set(x_142, 2, x_56);
lean::cnstr_set(x_142, 3, x_84);
lean::cnstr_set(x_142, 4, x_141);
return x_142;
}
default:
{
obj* x_145; obj* x_146; 
lean::dec(x_122);
lean::dec(x_131);
x_145 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_146 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_146, 0, x_0);
lean::cnstr_set(x_146, 1, x_28);
lean::cnstr_set(x_146, 2, x_56);
lean::cnstr_set(x_146, 3, x_84);
lean::cnstr_set(x_146, 4, x_145);
return x_146;
}
}
}
else
{
obj* x_150; obj* x_151; 
lean::dec(x_122);
lean::dec(x_123);
lean::dec(x_129);
x_150 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_151 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_151, 0, x_0);
lean::cnstr_set(x_151, 1, x_28);
lean::cnstr_set(x_151, 2, x_56);
lean::cnstr_set(x_151, 3, x_84);
lean::cnstr_set(x_151, 4, x_150);
return x_151;
}
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4;
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
obj* x_18; obj* x_20; 
x_20 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
x_21 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3;
x_18 = x_21;
goto lbl_19;
}
else
{
obj* x_22; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_24 = x_20;
} else {
 lean::inc(x_22);
 lean::dec(x_20);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; 
lean::dec(x_24);
x_29 = lean::box(0);
x_18 = x_29;
goto lbl_19;
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; obj* x_35; obj* x_36; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_25, 0);
lean::inc(x_32);
lean::dec(x_25);
x_35 = l_Lean_Parser_command_docComment_HasView;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_39 = lean::apply_1(x_36, x_32);
if (lean::is_scalar(x_24)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_24;
}
lean::cnstr_set(x_40, 0, x_39);
x_18 = x_40;
goto lbl_19;
}
else
{
obj* x_44; 
lean::dec(x_30);
lean::dec(x_24);
lean::dec(x_25);
x_44 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3;
x_18 = x_44;
goto lbl_19;
}
}
}
lbl_19:
{
obj* x_45; obj* x_46; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_48; 
x_48 = lean::box(3);
x_45 = x_1;
x_46 = x_48;
goto lbl_47;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_1, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_1, 1);
lean::inc(x_51);
lean::dec(x_1);
x_45 = x_51;
x_46 = x_49;
goto lbl_47;
}
lbl_47:
{
obj* x_54; obj* x_56; 
x_56 = l_Lean_Parser_Syntax_asNode___main(x_46);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
x_57 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2;
x_54 = x_57;
goto lbl_55;
}
else
{
obj* x_58; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 x_60 = x_56;
} else {
 lean::inc(x_58);
 lean::dec(x_56);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; 
lean::dec(x_60);
x_65 = lean::box(0);
x_54 = x_65;
goto lbl_55;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_71; obj* x_72; obj* x_75; obj* x_76; 
x_68 = lean::cnstr_get(x_61, 0);
lean::inc(x_68);
lean::dec(x_61);
x_71 = l_Lean_Parser_command_declAttributes_HasView;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
lean::dec(x_71);
x_75 = lean::apply_1(x_72, x_68);
if (lean::is_scalar(x_60)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_60;
}
lean::cnstr_set(x_76, 0, x_75);
x_54 = x_76;
goto lbl_55;
}
else
{
obj* x_80; 
lean::dec(x_60);
lean::dec(x_66);
lean::dec(x_61);
x_80 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2;
x_54 = x_80;
goto lbl_55;
}
}
}
lbl_55:
{
obj* x_81; obj* x_82; 
if (lean::obj_tag(x_45) == 0)
{
obj* x_84; 
x_84 = lean::box(3);
x_81 = x_45;
x_82 = x_84;
goto lbl_83;
}
else
{
obj* x_85; obj* x_87; 
x_85 = lean::cnstr_get(x_45, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_45, 1);
lean::inc(x_87);
lean::dec(x_45);
x_81 = x_87;
x_82 = x_85;
goto lbl_83;
}
lbl_83:
{
obj* x_90; obj* x_92; 
x_92 = l_Lean_Parser_Syntax_asNode___main(x_82);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; 
x_93 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1;
x_90 = x_93;
goto lbl_91;
}
else
{
obj* x_94; obj* x_96; obj* x_97; 
x_94 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_set(x_92, 0, lean::box(0));
 x_96 = x_92;
} else {
 lean::inc(x_94);
 lean::dec(x_92);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
if (lean::obj_tag(x_97) == 0)
{
obj* x_101; 
lean::dec(x_96);
x_101 = lean::box(0);
x_90 = x_101;
goto lbl_91;
}
else
{
obj* x_102; 
x_102 = lean::cnstr_get(x_97, 1);
lean::inc(x_102);
if (lean::obj_tag(x_102) == 0)
{
obj* x_104; obj* x_107; obj* x_108; obj* x_111; obj* x_112; 
x_104 = lean::cnstr_get(x_97, 0);
lean::inc(x_104);
lean::dec(x_97);
x_107 = l_Lean_Parser_command_visibility_HasView;
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
lean::dec(x_107);
x_111 = lean::apply_1(x_108, x_104);
if (lean::is_scalar(x_96)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_96;
}
lean::cnstr_set(x_112, 0, x_111);
x_90 = x_112;
goto lbl_91;
}
else
{
obj* x_116; 
lean::dec(x_96);
lean::dec(x_97);
lean::dec(x_102);
x_116 = l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1;
x_90 = x_116;
goto lbl_91;
}
}
}
lbl_91:
{
obj* x_117; obj* x_118; 
if (lean::obj_tag(x_81) == 0)
{
obj* x_120; 
x_120 = lean::box(3);
x_117 = x_81;
x_118 = x_120;
goto lbl_119;
}
else
{
obj* x_121; obj* x_123; 
x_121 = lean::cnstr_get(x_81, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_81, 1);
lean::inc(x_123);
lean::dec(x_81);
x_117 = x_123;
x_118 = x_121;
goto lbl_119;
}
lbl_119:
{
obj* x_126; obj* x_128; 
x_128 = l_Lean_Parser_Syntax_asNode___main(x_118);
if (lean::obj_tag(x_128) == 0)
{
obj* x_129; 
x_129 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_126 = x_129;
goto lbl_127;
}
else
{
obj* x_130; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_128, 0);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_set(x_128, 0, lean::box(0));
 x_132 = x_128;
} else {
 lean::inc(x_130);
 lean::dec(x_128);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
if (lean::obj_tag(x_133) == 0)
{
obj* x_137; 
lean::dec(x_132);
x_137 = lean::box(0);
x_126 = x_137;
goto lbl_127;
}
else
{
obj* x_138; 
x_138 = lean::cnstr_get(x_133, 1);
lean::inc(x_138);
if (lean::obj_tag(x_138) == 0)
{
obj* x_140; 
x_140 = lean::cnstr_get(x_133, 0);
lean::inc(x_140);
lean::dec(x_133);
switch (lean::obj_tag(x_140)) {
case 0:
{
obj* x_143; obj* x_146; obj* x_147; 
x_143 = lean::cnstr_get(x_140, 0);
lean::inc(x_143);
lean::dec(x_140);
if (lean::is_scalar(x_132)) {
 x_146 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_146 = x_132;
}
lean::cnstr_set(x_146, 0, x_143);
x_147 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_147, 0, x_146);
x_126 = x_147;
goto lbl_127;
}
case 3:
{
obj* x_149; 
lean::dec(x_132);
x_149 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_126 = x_149;
goto lbl_127;
}
default:
{
obj* x_152; 
lean::dec(x_140);
lean::dec(x_132);
x_152 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_126 = x_152;
goto lbl_127;
}
}
}
else
{
obj* x_156; 
lean::dec(x_138);
lean::dec(x_133);
lean::dec(x_132);
x_156 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_126 = x_156;
goto lbl_127;
}
}
}
lbl_127:
{
obj* x_157; 
if (lean::obj_tag(x_117) == 0)
{
obj* x_159; 
x_159 = lean::box(3);
x_157 = x_159;
goto lbl_158;
}
else
{
obj* x_160; 
x_160 = lean::cnstr_get(x_117, 0);
lean::inc(x_160);
lean::dec(x_117);
x_157 = x_160;
goto lbl_158;
}
lbl_158:
{
obj* x_163; 
x_163 = l_Lean_Parser_Syntax_asNode___main(x_157);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_165; 
x_164 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_165 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_165, 0, x_18);
lean::cnstr_set(x_165, 1, x_54);
lean::cnstr_set(x_165, 2, x_90);
lean::cnstr_set(x_165, 3, x_126);
lean::cnstr_set(x_165, 4, x_164);
return x_165;
}
else
{
obj* x_166; obj* x_168; obj* x_169; 
x_166 = lean::cnstr_get(x_163, 0);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_set(x_163, 0, lean::box(0));
 x_168 = x_163;
} else {
 lean::inc(x_166);
 lean::dec(x_163);
 x_168 = lean::box(0);
}
x_169 = lean::cnstr_get(x_166, 1);
lean::inc(x_169);
lean::dec(x_166);
if (lean::obj_tag(x_169) == 0)
{
obj* x_173; obj* x_174; 
lean::dec(x_168);
x_173 = lean::box(0);
x_174 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_174, 0, x_18);
lean::cnstr_set(x_174, 1, x_54);
lean::cnstr_set(x_174, 2, x_90);
lean::cnstr_set(x_174, 3, x_126);
lean::cnstr_set(x_174, 4, x_173);
return x_174;
}
else
{
obj* x_175; 
x_175 = lean::cnstr_get(x_169, 1);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 0)
{
obj* x_177; 
x_177 = lean::cnstr_get(x_169, 0);
lean::inc(x_177);
lean::dec(x_169);
switch (lean::obj_tag(x_177)) {
case 0:
{
obj* x_180; obj* x_183; obj* x_184; obj* x_185; 
x_180 = lean::cnstr_get(x_177, 0);
lean::inc(x_180);
lean::dec(x_177);
if (lean::is_scalar(x_168)) {
 x_183 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_183 = x_168;
}
lean::cnstr_set(x_183, 0, x_180);
x_184 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_184, 0, x_183);
x_185 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_185, 0, x_18);
lean::cnstr_set(x_185, 1, x_54);
lean::cnstr_set(x_185, 2, x_90);
lean::cnstr_set(x_185, 3, x_126);
lean::cnstr_set(x_185, 4, x_184);
return x_185;
}
case 3:
{
obj* x_187; obj* x_188; 
lean::dec(x_168);
x_187 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_188 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_188, 0, x_18);
lean::cnstr_set(x_188, 1, x_54);
lean::cnstr_set(x_188, 2, x_90);
lean::cnstr_set(x_188, 3, x_126);
lean::cnstr_set(x_188, 4, x_187);
return x_188;
}
default:
{
obj* x_191; obj* x_192; 
lean::dec(x_168);
lean::dec(x_177);
x_191 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_192 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_192, 0, x_18);
lean::cnstr_set(x_192, 1, x_54);
lean::cnstr_set(x_192, 2, x_90);
lean::cnstr_set(x_192, 3, x_126);
lean::cnstr_set(x_192, 4, x_191);
return x_192;
}
}
}
else
{
obj* x_196; obj* x_197; 
lean::dec(x_168);
lean::dec(x_169);
lean::dec(x_175);
x_196 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_197 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_197, 0, x_18);
lean::cnstr_set(x_197, 1, x_54);
lean::cnstr_set(x_197, 2, x_90);
lean::cnstr_set(x_197, 3, x_126);
lean::cnstr_set(x_197, 4, x_196);
return x_197;
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
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declModifiers_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
if (x_1 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::inc(x_4);
x_14 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_10 = x_15;
x_11 = x_17;
goto lbl_12;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_23 = x_15;
} else {
 lean::inc(x_20);
 lean::dec(x_15);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_20, 3);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_26 = lean::cnstr_get(x_14, 1);
lean::inc(x_26);
lean::dec(x_14);
x_29 = lean::cnstr_get(x_20, 0);
x_31 = lean::cnstr_get(x_20, 1);
x_33 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 3);
 x_35 = x_20;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_20);
 x_35 = lean::box(0);
}
x_36 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set(x_37, 1, x_31);
lean::cnstr_set(x_37, 2, x_33);
lean::cnstr_set(x_37, 3, x_36);
if (x_22 == 0)
{
uint8 x_38; obj* x_39; obj* x_40; 
x_38 = 0;
if (lean::is_scalar(x_23)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_23;
}
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_38);
x_40 = x_39;
x_10 = x_40;
x_11 = x_26;
goto lbl_12;
}
else
{
uint8 x_41; obj* x_42; obj* x_43; 
x_41 = 1;
if (lean::is_scalar(x_23)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_23;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_41);
x_43 = x_42;
x_10 = x_43;
x_11 = x_26;
goto lbl_12;
}
}
else
{
obj* x_44; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_44 = lean::cnstr_get(x_14, 1);
lean::inc(x_44);
lean::dec(x_14);
x_47 = lean::cnstr_get(x_20, 0);
x_49 = lean::cnstr_get(x_20, 1);
x_51 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 3);
 x_53 = x_20;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_20);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_56 = x_24;
} else {
 lean::inc(x_54);
 lean::dec(x_24);
 x_56 = lean::box(0);
}
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_Lean_Parser_noKind;
x_60 = l_Lean_Parser_Syntax_mkNode(x_59, x_58);
if (lean::is_scalar(x_56)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_56;
}
lean::cnstr_set(x_61, 0, x_60);
if (lean::is_scalar(x_53)) {
 x_62 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_62 = x_53;
}
lean::cnstr_set(x_62, 0, x_47);
lean::cnstr_set(x_62, 1, x_49);
lean::cnstr_set(x_62, 2, x_51);
lean::cnstr_set(x_62, 3, x_61);
if (x_22 == 0)
{
uint8 x_63; obj* x_64; obj* x_65; 
x_63 = 0;
if (lean::is_scalar(x_23)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_23;
}
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_63);
x_65 = x_64;
x_10 = x_65;
x_11 = x_44;
goto lbl_12;
}
else
{
uint8 x_66; obj* x_67; obj* x_68; 
x_66 = 1;
if (lean::is_scalar(x_23)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_23;
}
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_66);
x_68 = x_67;
x_10 = x_68;
x_11 = x_44;
goto lbl_12;
}
}
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_69 = lean::cnstr_get(x_10, 0);
x_71 = lean::cnstr_get(x_10, 1);
x_73 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 x_75 = x_10;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_10);
 x_75 = lean::box(0);
}
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_69);
x_77 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_75;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_71);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_78);
if (lean::obj_tag(x_79) == 0)
{
lean::dec(x_4);
x_6 = x_79;
x_7 = x_11;
goto lbl_8;
}
else
{
uint8 x_81; 
x_81 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (x_81 == 0)
{
obj* x_82; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_mjoin___rarg___closed__1;
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_89, 0, x_85);
lean::closure_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_9);
lean::cnstr_set(x_91, 1, x_4);
lean::cnstr_set(x_91, 2, x_90);
x_6 = x_91;
x_7 = x_11;
goto lbl_8;
}
else
{
lean::dec(x_4);
x_6 = x_79;
x_7 = x_11;
goto lbl_8;
}
}
}
else
{
uint8 x_93; 
x_93 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_93 == 0)
{
obj* x_94; obj* x_97; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_94 = lean::cnstr_get(x_10, 0);
lean::inc(x_94);
lean::dec(x_10);
x_97 = lean::cnstr_get(x_94, 2);
lean::inc(x_97);
lean::dec(x_94);
x_100 = l_mjoin___rarg___closed__1;
x_101 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_101, 0, x_97);
lean::closure_set(x_101, 1, x_100);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_9);
lean::cnstr_set(x_103, 1, x_4);
lean::cnstr_set(x_103, 2, x_102);
x_6 = x_103;
x_7 = x_11;
goto lbl_8;
}
else
{
obj* x_105; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_4);
x_105 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_107 = x_10;
} else {
 lean::inc(x_105);
 lean::dec(x_10);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_93);
x_109 = x_108;
x_6 = x_109;
x_7 = x_11;
goto lbl_8;
}
}
}
}
else
{
obj* x_110; 
x_110 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_110;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_111; 
x_111 = lean::cnstr_get(x_6, 0);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_113 = lean::cnstr_get(x_6, 1);
x_115 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_117 = x_6;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_6);
 x_117 = lean::box(0);
}
x_118 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_119 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_117)) {
 x_120 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_120 = x_117;
}
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_113);
lean::cnstr_set(x_120, 2, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_120);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_7);
return x_122;
}
else
{
obj* x_123; obj* x_125; obj* x_127; obj* x_128; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_123 = lean::cnstr_get(x_6, 1);
x_125 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_127 = x_6;
} else {
 lean::inc(x_123);
 lean::inc(x_125);
 lean::dec(x_6);
 x_127 = lean::box(0);
}
x_128 = lean::cnstr_get(x_111, 0);
lean::inc(x_128);
lean::dec(x_111);
x_131 = lean::box(0);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_128);
lean::cnstr_set(x_132, 1, x_131);
x_133 = l_Lean_Parser_noKind;
x_134 = l_Lean_Parser_Syntax_mkNode(x_133, x_132);
x_135 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_136 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_136 = x_127;
}
lean::cnstr_set(x_136, 0, x_134);
lean::cnstr_set(x_136, 1, x_123);
lean::cnstr_set(x_136, 2, x_135);
x_137 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_125, x_136);
x_138 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_7);
return x_138;
}
}
else
{
obj* x_139; uint8 x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_6, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_142 = x_6;
} else {
 lean::inc(x_139);
 lean::dec(x_6);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_139);
lean::cnstr_set_scalar(x_143, sizeof(void*)*1, x_141);
x_144 = x_143;
x_145 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_7);
return x_145;
}
}
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_0, 0);
x_15 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_1, x_18);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::apply_4(x_13, x_2, x_3, x_4, x_5);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_26 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_set(x_23, 1, lean::box(0));
 x_28 = x_23;
} else {
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_24, 0);
x_31 = lean::cnstr_get(x_24, 1);
x_33 = lean::cnstr_get(x_24, 2);
if (lean::is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
x_36 = lean::box(0);
x_37 = lean_name_mk_numeral(x_36, x_1);
x_38 = lean::box(0);
if (lean::is_scalar(x_17)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_17;
}
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_Syntax_mkNode(x_37, x_39);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_31);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_49; 
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_15);
if (lean::is_scalar(x_28)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_28;
}
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_26);
return x_49;
}
else
{
uint8 x_50; 
x_50 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_28);
x_52 = lean::cnstr_get(x_43, 0);
lean::inc(x_52);
lean::dec(x_43);
x_55 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_15, x_19, x_2, x_3, x_4, x_26);
x_56 = lean::cnstr_get(x_55, 0);
x_58 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_60 = x_55;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_55);
 x_60 = lean::box(0);
}
x_61 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_52, x_56);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_58);
return x_62;
}
else
{
obj* x_68; 
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_15);
if (lean::is_scalar(x_28)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_28;
}
lean::cnstr_set(x_68, 0, x_43);
lean::cnstr_set(x_68, 1, x_26);
return x_68;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_1);
lean::dec(x_17);
x_71 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_72; obj* x_75; obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
x_72 = lean::cnstr_get(x_23, 1);
lean::inc(x_72);
lean::dec(x_23);
x_75 = lean::cnstr_get(x_24, 0);
lean::inc(x_75);
lean::dec(x_24);
x_78 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_15, x_19, x_2, x_3, x_4, x_72);
x_79 = lean::cnstr_get(x_78, 0);
x_81 = lean::cnstr_get(x_78, 1);
if (lean::is_exclusive(x_78)) {
 x_83 = x_78;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_78);
 x_83 = lean::box(0);
}
x_84 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_79);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_81);
return x_85;
}
else
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_15);
x_91 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_93 = x_23;
} else {
 lean::inc(x_91);
 lean::dec(x_23);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_96 = x_24;
} else {
 lean::inc(x_94);
 lean::dec(x_24);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_71);
x_98 = x_97;
if (lean::is_scalar(x_93)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_93;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_91);
return x_99;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_43; obj* x_46; obj* x_49; 
x_0 = l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_tokens___rarg(x_2);
x_4 = lean::mk_string("private");
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_5);
lean::dec(x_4);
x_8 = lean::mk_string("protected");
x_9 = l_Lean_Parser_symbol_tokens___rarg(x_8, x_5);
lean::dec(x_8);
x_11 = lean::box(0);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_11);
lean::dec(x_9);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_12);
lean::dec(x_12);
lean::dec(x_6);
x_17 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_11);
lean::dec(x_17);
x_21 = l_Lean_Parser_tokens___rarg(x_19);
lean::dec(x_19);
x_23 = l_Lean_Parser_tokens___rarg(x_21);
lean::dec(x_21);
x_25 = lean::mk_string("noncomputable");
x_26 = l_Lean_Parser_symbol_tokens___rarg(x_25, x_5);
lean::dec(x_25);
x_28 = l_Lean_Parser_tokens___rarg(x_26);
lean::dec(x_26);
x_30 = lean::mk_string("unsafe");
x_31 = l_Lean_Parser_symbol_tokens___rarg(x_30, x_5);
lean::dec(x_30);
x_33 = l_Lean_Parser_tokens___rarg(x_31);
lean::dec(x_31);
x_35 = l_Lean_Parser_List_cons_tokens___rarg(x_33, x_11);
lean::dec(x_33);
x_37 = l_Lean_Parser_List_cons_tokens___rarg(x_28, x_35);
lean::dec(x_35);
lean::dec(x_28);
x_40 = l_Lean_Parser_List_cons_tokens___rarg(x_23, x_37);
lean::dec(x_37);
lean::dec(x_23);
x_43 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_40);
lean::dec(x_40);
lean::dec(x_3);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_43);
lean::dec(x_43);
lean::dec(x_1);
x_49 = l_Lean_Parser_tokens___rarg(x_46);
lean::dec(x_46);
return x_49;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser), 4, 0);
x_5 = 0;
x_6 = lean::box(x_5);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_Parser), 4, 0);
lean::inc(x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_6);
x_12 = lean::mk_string("private");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_13);
x_17 = lean::mk_nat_obj(0ul);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_18, 0, x_13);
lean::closure_set(x_18, 1, x_17);
lean::closure_set(x_18, 2, x_16);
x_19 = lean::mk_string("protected");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_23, 0, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_17);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_18);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_17);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
x_30 = l_Lean_Parser_command_visibility;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_31, 0, x_30);
lean::closure_set(x_31, 1, x_29);
lean::inc(x_6);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_6);
x_34 = lean::mk_string("noncomputable");
x_35 = l_String_trim(x_34);
lean::dec(x_34);
lean::inc(x_35);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_38, 0, x_35);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_39, 0, x_35);
lean::closure_set(x_39, 1, x_17);
lean::closure_set(x_39, 2, x_38);
lean::inc(x_6);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_41, 0, x_39);
lean::closure_set(x_41, 1, x_6);
x_42 = lean::mk_string("unsafe");
x_43 = l_String_trim(x_42);
lean::dec(x_42);
lean::inc(x_43);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_46, 0, x_43);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_47, 0, x_43);
lean::closure_set(x_47, 1, x_17);
lean::closure_set(x_47, 2, x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_48, 0, x_47);
lean::closure_set(x_48, 1, x_6);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_25);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_41);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_33);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_11);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_8);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_Lean_Parser_command_declModifiers;
x_55 = l_Lean_Parser_command_declModifiers_HasView;
x_56 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_54, x_53, x_55);
lean::dec(x_53);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_56;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser___closed__1() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser), 4, 0);
x_1 = 0;
x_2 = lean::box(x_1);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_Parser), 4, 0);
lean::inc(x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_2);
x_8 = lean::mk_string("private");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_9);
x_13 = lean::mk_nat_obj(0ul);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_14, 0, x_9);
lean::closure_set(x_14, 1, x_13);
lean::closure_set(x_14, 2, x_12);
x_15 = lean::mk_string("protected");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_13);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_14);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_13);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
x_26 = l_Lean_Parser_command_visibility;
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_25);
lean::inc(x_2);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_2);
x_30 = lean::mk_string("noncomputable");
x_31 = l_String_trim(x_30);
lean::dec(x_30);
lean::inc(x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_34, 0, x_31);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_35, 0, x_31);
lean::closure_set(x_35, 1, x_13);
lean::closure_set(x_35, 2, x_34);
lean::inc(x_2);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_2);
x_38 = lean::mk_string("unsafe");
x_39 = l_String_trim(x_38);
lean::dec(x_38);
lean::inc(x_39);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_42, 0, x_39);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_43, 0, x_39);
lean::closure_set(x_43, 1, x_13);
lean::closure_set(x_43, 2, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_44, 0, x_43);
lean::closure_set(x_44, 1, x_2);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_21);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_29);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_7);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
}
obj* l_Lean_Parser_command_declModifiers_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_declModifiers;
x_5 = l_Lean_Parser_command_declModifiers_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declSig() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declSig");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_1);
x_11 = l_Lean_Parser_Term_typeSpec_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::apply_1(x_12, x_3);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_command_declSig;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_0 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_Term_typeSpec_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_4);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_Term_typeSpec_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_command_declSig_HasView_x_27___elambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_19; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
lean::dec(x_6);
x_15 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
lean::dec(x_12);
x_25 = l_Lean_Parser_Term_typeSpec_HasView;
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_29 = lean::apply_1(x_26, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_HasView_x_27___elambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declSig_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_10; 
x_0 = l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_Term_typeSpec_Parser_Lean_Parser_HasTokens;
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
obj* _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec_Parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_command_declSig;
x_12 = l_Lean_Parser_command_declSig_HasView;
x_13 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_11, x_10, x_12);
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_declSig_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec_Parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
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
obj* l_Lean_Parser_command_declSig_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_declSig;
x_5 = l_Lean_Parser_command_declSig_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("optDeclSig");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_command_optDeclSig;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::box(0);
x_19 = l_Lean_Parser_Term_typeSpec_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_15);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_18);
x_25 = l_Lean_Parser_noKind;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_10);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_command_optDeclSig;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
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
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_12, 1);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
x_23 = l_Lean_Parser_Term_typeSpec_HasView;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_20);
if (lean::is_scalar(x_11)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_11;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_5);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_33 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
obj* l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1;
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
obj* x_18; obj* x_19; obj* x_22; 
x_18 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_29);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_41 = l_Lean_Parser_Term_typeSpec_HasView;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_38);
if (lean::is_scalar(x_29)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_29;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_22);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_36);
x_51 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_22);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
x_56 = l_Lean_Parser_Syntax_asNode___main(x_53);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
x_57 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_22);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 x_61 = x_56;
} else {
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_61);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_22);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_62, 1);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_62, 0);
lean::inc(x_70);
lean::dec(x_62);
x_73 = l_Lean_Parser_Term_typeSpec_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_70);
if (lean::is_scalar(x_61)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_61;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_22);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_68);
lean::dec(x_62);
lean::dec(x_61);
x_83 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__2;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_22);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_optDeclSig_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_10; 
x_0 = l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_Term_optType_Parser_Lean_Parser_HasTokens;
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
obj* _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType_Parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_command_optDeclSig;
x_12 = l_Lean_Parser_command_optDeclSig_HasView;
x_13 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_11, x_10, x_12);
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType_Parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
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
obj* l_Lean_Parser_command_optDeclSig_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_optDeclSig;
x_5 = l_Lean_Parser_command_optDeclSig_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_equation() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("equation");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_equation_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_3);
x_11 = l_Lean_Parser_noKind;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_13);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_command_equation;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_14);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_12);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = l_Lean_Parser_command_equation;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
else
{
obj* x_31; obj* x_34; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
if (lean::obj_tag(x_5) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::box(3);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_14);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_12);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_command_equation;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_41 = lean::cnstr_get(x_5, 0);
lean::inc(x_41);
lean::dec(x_5);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_41);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_14);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_12);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_34);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_command_equation;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
return x_49;
}
}
}
}
obj* _init_l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_0);
lean::cnstr_set(x_4, 3, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_8);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_0);
lean::cnstr_set(x_12, 3, x_1);
return x_12;
}
}
}
obj* l_Lean_Parser_command_equation_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
x_36 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_36) == 0)
{
if (lean::obj_tag(x_27) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::box(0);
x_38 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_39 = lean::box(3);
x_40 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_40, 0, x_18);
lean::cnstr_set(x_40, 1, x_38);
lean::cnstr_set(x_40, 2, x_37);
lean::cnstr_set(x_40, 3, x_39);
return x_40;
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_27, 0);
lean::inc(x_41);
switch (lean::obj_tag(x_41)) {
case 0:
{
obj* x_43; obj* x_46; obj* x_49; 
x_43 = lean::cnstr_get(x_27, 1);
lean::inc(x_43);
lean::dec(x_27);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_46);
if (lean::obj_tag(x_43) == 0)
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_51 = lean::box(3);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_18);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_49);
lean::cnstr_set(x_52, 3, x_51);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_57; 
x_53 = lean::cnstr_get(x_43, 0);
lean::inc(x_53);
lean::dec(x_43);
x_56 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_18);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set(x_57, 2, x_49);
lean::cnstr_set(x_57, 3, x_53);
return x_57;
}
}
case 3:
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_27, 1);
lean::inc(x_58);
lean::dec(x_27);
x_61 = lean::box(0);
if (lean::obj_tag(x_58) == 0)
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_63 = lean::box(3);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_18);
lean::cnstr_set(x_64, 1, x_62);
lean::cnstr_set(x_64, 2, x_61);
lean::cnstr_set(x_64, 3, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_68; obj* x_69; 
x_65 = lean::cnstr_get(x_58, 0);
lean::inc(x_65);
lean::dec(x_58);
x_68 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_18);
lean::cnstr_set(x_69, 1, x_68);
lean::cnstr_set(x_69, 2, x_61);
lean::cnstr_set(x_69, 3, x_65);
return x_69;
}
}
default:
{
obj* x_71; obj* x_74; 
lean::dec(x_41);
x_71 = lean::cnstr_get(x_27, 1);
lean::inc(x_71);
lean::dec(x_27);
x_74 = lean::box(0);
if (lean::obj_tag(x_71) == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_76 = lean::box(3);
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_18);
lean::cnstr_set(x_77, 1, x_75);
lean::cnstr_set(x_77, 2, x_74);
lean::cnstr_set(x_77, 3, x_76);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_82 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_82, 0, x_18);
lean::cnstr_set(x_82, 1, x_81);
lean::cnstr_set(x_82, 2, x_74);
lean::cnstr_set(x_82, 3, x_78);
return x_82;
}
}
}
}
}
else
{
obj* x_83; obj* x_85; obj* x_86; obj* x_89; 
x_83 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_85 = x_36;
} else {
 lean::inc(x_83);
 lean::dec(x_36);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x_27___elambda__1___spec__1(x_86);
if (lean::obj_tag(x_27) == 0)
{
obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_85);
x_91 = lean::box(0);
x_92 = lean::box(3);
x_93 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_93, 0, x_18);
lean::cnstr_set(x_93, 1, x_89);
lean::cnstr_set(x_93, 2, x_91);
lean::cnstr_set(x_93, 3, x_92);
return x_93;
}
else
{
obj* x_94; 
x_94 = lean::cnstr_get(x_27, 0);
lean::inc(x_94);
switch (lean::obj_tag(x_94)) {
case 0:
{
obj* x_96; obj* x_99; obj* x_102; 
x_96 = lean::cnstr_get(x_27, 1);
lean::inc(x_96);
lean::dec(x_27);
x_99 = lean::cnstr_get(x_94, 0);
lean::inc(x_99);
lean::dec(x_94);
if (lean::is_scalar(x_85)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_85;
}
lean::cnstr_set(x_102, 0, x_99);
if (lean::obj_tag(x_96) == 0)
{
obj* x_103; obj* x_104; 
x_103 = lean::box(3);
x_104 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_104, 0, x_18);
lean::cnstr_set(x_104, 1, x_89);
lean::cnstr_set(x_104, 2, x_102);
lean::cnstr_set(x_104, 3, x_103);
return x_104;
}
else
{
obj* x_105; obj* x_108; 
x_105 = lean::cnstr_get(x_96, 0);
lean::inc(x_105);
lean::dec(x_96);
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_18);
lean::cnstr_set(x_108, 1, x_89);
lean::cnstr_set(x_108, 2, x_102);
lean::cnstr_set(x_108, 3, x_105);
return x_108;
}
}
case 3:
{
obj* x_110; obj* x_113; 
lean::dec(x_85);
x_110 = lean::cnstr_get(x_27, 1);
lean::inc(x_110);
lean::dec(x_27);
x_113 = lean::box(0);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_115; 
x_114 = lean::box(3);
x_115 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_115, 0, x_18);
lean::cnstr_set(x_115, 1, x_89);
lean::cnstr_set(x_115, 2, x_113);
lean::cnstr_set(x_115, 3, x_114);
return x_115;
}
else
{
obj* x_116; obj* x_119; 
x_116 = lean::cnstr_get(x_110, 0);
lean::inc(x_116);
lean::dec(x_110);
x_119 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_119, 0, x_18);
lean::cnstr_set(x_119, 1, x_89);
lean::cnstr_set(x_119, 2, x_113);
lean::cnstr_set(x_119, 3, x_116);
return x_119;
}
}
default:
{
obj* x_122; obj* x_125; 
lean::dec(x_94);
lean::dec(x_85);
x_122 = lean::cnstr_get(x_27, 1);
lean::inc(x_122);
lean::dec(x_27);
x_125 = lean::box(0);
if (lean::obj_tag(x_122) == 0)
{
obj* x_126; obj* x_127; 
x_126 = lean::box(3);
x_127 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_127, 0, x_18);
lean::cnstr_set(x_127, 1, x_89);
lean::cnstr_set(x_127, 2, x_125);
lean::cnstr_set(x_127, 3, x_126);
return x_127;
}
else
{
obj* x_128; obj* x_131; 
x_128 = lean::cnstr_get(x_122, 0);
lean::inc(x_128);
lean::dec(x_122);
x_131 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_131, 0, x_18);
lean::cnstr_set(x_131, 1, x_89);
lean::cnstr_set(x_131, 2, x_125);
lean::cnstr_set(x_131, 3, x_128);
return x_131;
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
obj* _init_l_Lean_Parser_command_equation_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_equation_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_equation_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_28; 
x_0 = lean::mk_string("|");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_4);
x_6 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
x_8 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
x_10 = lean::mk_string(":=");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_1);
lean::dec(x_10);
x_13 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_1);
x_14 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_16);
lean::dec(x_14);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_19);
lean::dec(x_19);
lean::dec(x_8);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_22);
lean::dec(x_22);
lean::dec(x_2);
x_28 = l_Lean_Parser_tokens___rarg(x_25);
lean::dec(x_25);
return x_28;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("|");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = l_Lean_Parser_maxPrec;
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_string(":=");
x_16 = l_String_trim(x_15);
lean::dec(x_15);
lean::inc(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_19, 0, x_16);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_9);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_21, 0, x_9);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_10);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_equation;
x_29 = l_Lean_Parser_command_equation_HasView;
x_30 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_28, x_27, x_29);
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_30;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string("|");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = l_Lean_Parser_maxPrec;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::mk_string(":=");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_5);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_17, 0, x_5);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
obj* l_Lean_Parser_command_equation_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_equation;
x_5 = l_Lean_Parser_command_equation_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("simpleDeclVal");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::box(3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_Lean_Parser_command_simpleDeclVal;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
x_17 = l_Lean_Parser_command_simpleDeclVal;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1;
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
x_10 = l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_13; obj* x_16; obj* x_19; 
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
if (lean::is_scalar(x_5)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_5;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::box(3);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
lean::dec(x_13);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_22);
return x_25;
}
}
case 3:
{
obj* x_27; 
lean::dec(x_5);
x_27 = lean::cnstr_get(x_6, 1);
lean::inc(x_27);
lean::dec(x_6);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; 
x_30 = l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1;
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_31);
return x_35;
}
}
default:
{
obj* x_38; 
lean::dec(x_11);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 1);
lean::inc(x_38);
lean::dec(x_6);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; 
x_41 = l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1;
return x_41;
}
else
{
obj* x_42; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_simpleDeclVal_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declVal() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declVal");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_declVal;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_equation_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_declVal_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_declVal;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
case 1:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1;
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_declVal;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
default:
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2;
x_34 = l_List_map___main___rarg(x_33, x_30);
x_35 = l_Lean_Parser_noKind;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_1);
x_38 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__4;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_1);
x_41 = l_Lean_Parser_command_declVal;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = l_Lean_Parser_command_equation_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_equation_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declVal");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_declVal_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0ul);
x_60 = lean::nat_dec_eq(x_41, x_59);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::mk_nat_obj(1ul);
x_62 = lean::nat_dec_eq(x_41, x_61);
lean::dec(x_41);
if (x_62 == 0)
{
obj* x_65; 
lean::dec(x_26);
x_65 = l_Lean_Parser_Syntax_asNode___main(x_56);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; 
x_66 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1;
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_73; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
lean::dec(x_65);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2;
x_74 = l_List_map___main___rarg(x_73, x_70);
x_75 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_76; obj* x_79; obj* x_80; 
x_76 = lean::cnstr_get(x_56, 0);
lean::inc(x_76);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_26;
}
lean::cnstr_set(x_79, 0, x_76);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
case 3:
{
obj* x_82; 
lean::dec(x_26);
x_82 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3;
return x_82;
}
default:
{
obj* x_85; 
lean::dec(x_56);
lean::dec(x_26);
x_85 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3;
return x_85;
}
}
}
}
else
{
obj* x_88; obj* x_89; obj* x_92; obj* x_93; 
lean::dec(x_26);
lean::dec(x_41);
x_88 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
lean::dec(x_88);
x_92 = lean::apply_1(x_89, x_56);
x_93 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
}
else
{
obj* x_98; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_98 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_98;
}
}
}
}
}
}
}
else
{
obj* x_101; 
lean::dec(x_8);
lean::dec(x_17);
x_101 = l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4;
return x_101;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declVal_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_28; obj* x_30; obj* x_32; 
x_0 = lean::mk_string(":=");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_1);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_7);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
x_13 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_15 = lean::mk_string(".");
x_16 = l_Lean_Parser_symbol_tokens___rarg(x_15, x_1);
lean::dec(x_15);
x_18 = l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens;
x_19 = l_Lean_Parser_tokens___rarg(x_18);
x_20 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_7);
lean::dec(x_19);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_16, x_20);
lean::dec(x_20);
lean::dec(x_16);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_13, x_22);
lean::dec(x_22);
lean::dec(x_13);
x_28 = l_Lean_Parser_tokens___rarg(x_25);
lean::dec(x_25);
x_30 = l_Lean_Parser_List_cons_tokens___rarg(x_28, x_7);
lean::dec(x_28);
x_32 = l_Lean_Parser_tokens___rarg(x_30);
lean::dec(x_30);
return x_32;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string(":=");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_command_simpleDeclVal;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::mk_string(".");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_22, 0, x_19);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_9);
lean::closure_set(x_23, 2, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_Parser), 4, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_13);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_17);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_9);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_13);
x_31 = l_Lean_Parser_command_declVal;
x_32 = l_Lean_Parser_command_declVal_HasView;
x_33 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_31, x_30, x_32);
lean::dec(x_30);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_33;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string(":=");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_command_simpleDeclVal;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_13, 0, x_12);
lean::closure_set(x_13, 1, x_11);
x_14 = lean::mk_string(".");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_18, 0, x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_19, 0, x_15);
lean::closure_set(x_19, 1, x_5);
lean::closure_set(x_19, 2, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_Parser), 4, 0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_9);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_5);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
return x_26;
}
}
obj* l_Lean_Parser_command_declVal_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_declVal;
x_5 = l_Lean_Parser_command_declVal_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("relaxedInferModifier");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_command_relaxedInferModifier;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
x_7 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1;
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::box(3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_Lean_Parser_command_relaxedInferModifier;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
}
else
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_17);
if (lean::obj_tag(x_3) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_relaxedInferModifier;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_20);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_relaxedInferModifier;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
case 3:
{
obj* x_26; obj* x_27; 
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
default:
{
obj* x_29; obj* x_30; 
lean::dec(x_2);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
lbl_6:
{
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_31; obj* x_34; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
if (lean::obj_tag(x_4) == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::dec(x_4);
x_1 = x_34;
x_2 = x_37;
goto lbl_3;
}
}
case 3:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_40; 
x_40 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1;
return x_40;
}
else
{
obj* x_41; obj* x_44; 
x_41 = lean::cnstr_get(x_4, 0);
lean::inc(x_41);
lean::dec(x_4);
x_44 = lean::box(0);
x_1 = x_44;
x_2 = x_41;
goto lbl_3;
}
}
default:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1;
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
}
}
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_relaxedInferModifier_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("strictInferModifier");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_command_strictInferModifier;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
x_7 = l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1;
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::box(3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = l_Lean_Parser_command_strictInferModifier;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
}
else
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_17);
if (lean::obj_tag(x_3) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_strictInferModifier;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_20);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_strictInferModifier;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
case 3:
{
obj* x_26; obj* x_27; 
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
default:
{
obj* x_29; obj* x_30; 
lean::dec(x_2);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
lbl_6:
{
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_31; obj* x_34; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
if (lean::obj_tag(x_4) == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::dec(x_4);
x_1 = x_34;
x_2 = x_37;
goto lbl_3;
}
}
case 3:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_40; 
x_40 = l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1;
return x_40;
}
else
{
obj* x_41; obj* x_44; 
x_41 = lean::cnstr_get(x_4, 0);
lean::inc(x_41);
lean::dec(x_4);
x_44 = lean::box(0);
x_1 = x_44;
x_2 = x_41;
goto lbl_3;
}
}
default:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1;
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
}
}
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_strictInferModifier_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_inferModifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inferModifier");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_inferModifier;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_strictInferModifier_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_inferModifier;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inferModifier");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
lean::dec(x_39);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_58 = l_Lean_Parser_command_strictInferModifier_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_52);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_68; obj* x_69; 
x_64 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_68 = lean::apply_1(x_65, x_52);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_73 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_73;
}
}
}
}
}
}
}
else
{
obj* x_76; 
lean::dec(x_8);
lean::dec(x_17);
x_76 = l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1;
return x_76;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_inferModifier_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_39; obj* x_41; 
x_0 = lean::mk_string("{");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string("}");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_7);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
x_13 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_15 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
x_17 = lean::mk_string("(");
x_18 = l_Lean_Parser_symbol_tokens___rarg(x_17, x_1);
lean::dec(x_17);
x_20 = lean::mk_string(")");
x_21 = l_Lean_Parser_symbol_tokens___rarg(x_20, x_1);
lean::dec(x_20);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_21, x_7);
lean::dec(x_21);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_23);
lean::dec(x_23);
lean::dec(x_18);
x_28 = l_Lean_Parser_tokens___rarg(x_25);
lean::dec(x_25);
x_30 = l_Lean_Parser_tokens___rarg(x_28);
lean::dec(x_28);
x_32 = l_Lean_Parser_List_cons_tokens___rarg(x_30, x_7);
lean::dec(x_30);
x_34 = l_Lean_Parser_List_cons_tokens___rarg(x_15, x_32);
lean::dec(x_32);
lean::dec(x_15);
x_37 = l_Lean_Parser_tokens___rarg(x_34);
lean::dec(x_34);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_37, x_7);
lean::dec(x_37);
x_41 = l_Lean_Parser_tokens___rarg(x_39);
lean::dec(x_39);
return x_41;
}
}
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = l_Lean_Parser_command_relaxedInferModifier;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_7);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
}
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = l_Lean_Parser_command_strictInferModifier;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_7);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("{");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::mk_string("}");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_9);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::mk_string("(");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_25, 0, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_26, 0, x_22);
lean::closure_set(x_26, 1, x_9);
lean::closure_set(x_26, 2, x_25);
x_27 = lean::mk_string(")");
x_28 = l_String_trim(x_27);
lean::dec(x_27);
lean::inc(x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_31, 0, x_28);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_32, 0, x_28);
lean::closure_set(x_32, 1, x_9);
lean::closure_set(x_32, 2, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_17);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_26);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2), 5, 1);
lean::closure_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_17);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_20);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_38, 0, x_37);
lean::closure_set(x_38, 1, x_9);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_17);
x_40 = l_Lean_Parser_command_inferModifier;
x_41 = l_Lean_Parser_command_inferModifier_HasView;
x_42 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_40, x_39, x_41);
lean::dec(x_39);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_42;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_0 = lean::mk_string("{");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("}");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::mk_string("(");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_21, 0, x_18);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_5);
lean::closure_set(x_22, 2, x_21);
x_23 = lean::mk_string(")");
x_24 = l_String_trim(x_23);
lean::dec(x_23);
lean::inc(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_27, 0, x_24);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_28, 0, x_24);
lean::closure_set(x_28, 1, x_5);
lean::closure_set(x_28, 2, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_13);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_22);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2), 5, 1);
lean::closure_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_13);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_16);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_34, 0, x_33);
lean::closure_set(x_34, 1, x_5);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_13);
return x_35;
}
}
obj* l_Lean_Parser_command_inferModifier_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_inferModifier;
x_5 = l_Lean_Parser_command_inferModifier_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_introRule() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("introRule");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_introRule_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_3);
x_11 = l_Lean_Parser_command_optDeclSig_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::apply_1(x_12, x_7);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(3);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_command_introRule;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_25 = lean::cnstr_get(x_5, 0);
lean::inc(x_25);
lean::dec(x_5);
x_28 = l_Lean_Parser_command_inferModifier_HasView;
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
lean::dec(x_28);
x_32 = lean::apply_1(x_29, x_25);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_16);
x_34 = l_Lean_Parser_noKind;
x_35 = l_Lean_Parser_Syntax_mkNode(x_34, x_33);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_17);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_10);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::box(3);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
x_40 = l_Lean_Parser_command_introRule;
x_41 = l_Lean_Parser_Syntax_mkNode(x_40, x_39);
return x_41;
}
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
lean::dec(x_1);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_17);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_10);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_command_introRule;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_52 = lean::cnstr_get(x_5, 0);
lean::inc(x_52);
lean::dec(x_5);
x_55 = l_Lean_Parser_command_inferModifier_HasView;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
x_59 = lean::apply_1(x_56, x_52);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_16);
x_61 = l_Lean_Parser_noKind;
x_62 = l_Lean_Parser_Syntax_mkNode(x_61, x_60);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_17);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_10);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_45);
lean::cnstr_set(x_65, 1, x_64);
x_66 = l_Lean_Parser_command_introRule;
x_67 = l_Lean_Parser_Syntax_mkNode(x_66, x_65);
return x_67;
}
}
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_inferModifier_HasView;
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
obj* _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_optDeclSig_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_4 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_5 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_4);
lean::cnstr_set(x_6, 3, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_9);
x_14 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_15 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set(x_16, 2, x_0);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
lean::dec(x_10);
x_22 = l_Lean_Parser_command_inferModifier_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_19);
if (lean::is_scalar(x_9)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_9;
}
lean::cnstr_set(x_27, 0, x_26);
x_28 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_29 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_27);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_9);
lean::dec(x_17);
lean::dec(x_10);
x_34 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_35 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_36 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_0);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set(x_37, 2, x_35);
lean::cnstr_set(x_37, 3, x_36);
return x_37;
}
}
}
}
}
obj* l_Lean_Parser_command_introRule_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
switch (lean::obj_tag(x_28)) {
case 1:
{
obj* x_38; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
x_36 = x_38;
goto lbl_37;
}
case 3:
{
obj* x_41; 
x_41 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_36 = x_41;
goto lbl_37;
}
default:
{
obj* x_43; 
lean::dec(x_28);
x_43 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_36 = x_43;
goto lbl_37;
}
}
lbl_37:
{
obj* x_44; obj* x_45; 
if (lean::obj_tag(x_27) == 0)
{
obj* x_47; 
x_47 = lean::box(3);
x_44 = x_27;
x_45 = x_47;
goto lbl_46;
}
else
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_27, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_27, 1);
lean::inc(x_50);
lean::dec(x_27);
x_44 = x_50;
x_45 = x_48;
goto lbl_46;
}
lbl_46:
{
obj* x_53; 
x_53 = l_Lean_Parser_Syntax_asNode___main(x_45);
if (lean::obj_tag(x_53) == 0)
{
if (lean::obj_tag(x_44) == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_55 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_18);
lean::cnstr_set(x_56, 1, x_36);
lean::cnstr_set(x_56, 2, x_54);
lean::cnstr_set(x_56, 3, x_55);
return x_56;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; 
x_57 = lean::cnstr_get(x_44, 0);
lean::inc(x_57);
lean::dec(x_44);
x_60 = l_Lean_Parser_command_optDeclSig_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::apply_1(x_61, x_57);
x_65 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_66 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_66, 0, x_18);
lean::cnstr_set(x_66, 1, x_36);
lean::cnstr_set(x_66, 2, x_65);
lean::cnstr_set(x_66, 3, x_64);
return x_66;
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_53, 0);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_set(x_53, 0, lean::box(0));
 x_69 = x_53;
} else {
 lean::inc(x_67);
 lean::dec(x_53);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_74; 
lean::dec(x_69);
x_74 = lean::box(0);
if (lean::obj_tag(x_44) == 0)
{
obj* x_75; obj* x_76; 
x_75 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_76 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_76, 0, x_18);
lean::cnstr_set(x_76, 1, x_36);
lean::cnstr_set(x_76, 2, x_74);
lean::cnstr_set(x_76, 3, x_75);
return x_76;
}
else
{
obj* x_77; obj* x_80; obj* x_81; obj* x_84; obj* x_85; 
x_77 = lean::cnstr_get(x_44, 0);
lean::inc(x_77);
lean::dec(x_44);
x_80 = l_Lean_Parser_command_optDeclSig_HasView;
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
lean::dec(x_80);
x_84 = lean::apply_1(x_81, x_77);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_18);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_74);
lean::cnstr_set(x_85, 3, x_84);
return x_85;
}
}
else
{
obj* x_86; 
x_86 = lean::cnstr_get(x_70, 1);
lean::inc(x_86);
if (lean::obj_tag(x_86) == 0)
{
obj* x_88; obj* x_91; obj* x_92; obj* x_95; obj* x_96; 
x_88 = lean::cnstr_get(x_70, 0);
lean::inc(x_88);
lean::dec(x_70);
x_91 = l_Lean_Parser_command_inferModifier_HasView;
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
lean::dec(x_91);
x_95 = lean::apply_1(x_92, x_88);
if (lean::is_scalar(x_69)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_69;
}
lean::cnstr_set(x_96, 0, x_95);
if (lean::obj_tag(x_44) == 0)
{
obj* x_97; obj* x_98; 
x_97 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_18);
lean::cnstr_set(x_98, 1, x_36);
lean::cnstr_set(x_98, 2, x_96);
lean::cnstr_set(x_98, 3, x_97);
return x_98;
}
else
{
obj* x_99; obj* x_102; obj* x_103; obj* x_106; obj* x_107; 
x_99 = lean::cnstr_get(x_44, 0);
lean::inc(x_99);
lean::dec(x_44);
x_102 = l_Lean_Parser_command_optDeclSig_HasView;
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
lean::dec(x_102);
x_106 = lean::apply_1(x_103, x_99);
x_107 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_107, 0, x_18);
lean::cnstr_set(x_107, 1, x_36);
lean::cnstr_set(x_107, 2, x_96);
lean::cnstr_set(x_107, 3, x_106);
return x_107;
}
}
else
{
lean::dec(x_86);
lean::dec(x_69);
lean::dec(x_70);
if (lean::obj_tag(x_44) == 0)
{
obj* x_111; obj* x_112; obj* x_113; 
x_111 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_112 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_113 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_113, 0, x_18);
lean::cnstr_set(x_113, 1, x_36);
lean::cnstr_set(x_113, 2, x_111);
lean::cnstr_set(x_113, 3, x_112);
return x_113;
}
else
{
obj* x_114; obj* x_117; obj* x_118; obj* x_121; obj* x_122; obj* x_123; 
x_114 = lean::cnstr_get(x_44, 0);
lean::inc(x_114);
lean::dec(x_44);
x_117 = l_Lean_Parser_command_optDeclSig_HasView;
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
lean::dec(x_117);
x_121 = lean::apply_1(x_118, x_114);
x_122 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_123 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_123, 0, x_18);
lean::cnstr_set(x_123, 1, x_36);
lean::cnstr_set(x_123, 2, x_122);
lean::cnstr_set(x_123, 3, x_121);
return x_123;
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
obj* _init_l_Lean_Parser_command_introRule_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_introRule_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_4);
x_9 = l_Lean_Parser_token(x_4, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_set(x_9, 1, lean::box(0));
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
x_19 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_21 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_10);
 x_21 = lean::box(0);
}
switch (lean::obj_tag(x_15)) {
case 1:
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_4);
lean::dec(x_2);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_21;
}
lean::cnstr_set(x_27, 0, x_15);
lean::cnstr_set(x_27, 1, x_17);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_28);
x_30 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_31 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_29, x_30);
x_32 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_31);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_12);
return x_33;
}
case 3:
{
obj* x_36; 
lean::dec(x_14);
lean::dec(x_21);
x_36 = lean::box(0);
x_22 = x_36;
goto lbl_23;
}
default:
{
obj* x_40; 
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_21);
x_40 = lean::box(0);
x_22 = x_40;
goto lbl_23;
}
}
lbl_23:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_22);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_2);
x_43 = lean::box(0);
x_44 = l_String_splitAux___main___closed__1;
x_45 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_46 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_45, x_42, x_43, x_4, x_17, x_12);
lean::dec(x_4);
x_48 = lean::cnstr_get(x_46, 0);
x_50 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 x_52 = x_46;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_46);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_48);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_53);
x_56 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_55, x_45);
x_57 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_56);
if (lean::is_scalar(x_52)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_52;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_50);
return x_58;
}
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_4);
lean::dec(x_2);
x_61 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_63 = x_9;
} else {
 lean::inc(x_61);
 lean::dec(x_9);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_10, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_67 = x_10;
} else {
 lean::inc(x_64);
 lean::dec(x_10);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_69);
x_72 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_73 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_71, x_72);
x_74 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_17; 
x_0 = lean::mk_string("|");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_tokens___rarg(x_5);
x_7 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_4);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_8);
lean::dec(x_8);
lean::dec(x_6);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_9);
lean::dec(x_9);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_12);
lean::dec(x_12);
lean::dec(x_2);
x_17 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
return x_17;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("|");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_12 = 0;
x_13 = lean::box(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_10);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_command_introRule;
x_23 = l_Lean_Parser_command_introRule_HasView;
x_24 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_22, x_21, x_23);
lean::dec(x_21);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_24;
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string("|");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_command_introRule_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_introRule;
x_5 = l_Lean_Parser_command_introRule_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structBinderContent");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(obj* x_0) {
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
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(x_4);
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
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(x_1);
x_11 = l_Lean_Parser_noKind;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = l_Lean_Parser_command_optDeclSig_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::apply_1(x_14, x_5);
x_18 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_command_structBinderContent;
x_25 = l_Lean_Parser_Syntax_mkNode(x_24, x_23);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
lean::dec(x_7);
x_29 = l_Lean_Parser_Term_binderDefault_HasView;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_33 = lean::apply_1(x_30, x_26);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_18);
x_35 = l_Lean_Parser_Syntax_mkNode(x_11, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_18);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_17);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_12);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_Parser_command_structBinderContent;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
else
{
obj* x_43; obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_3, 0);
lean::inc(x_43);
lean::dec(x_3);
x_46 = l_Lean_Parser_command_inferModifier_HasView;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
x_50 = lean::apply_1(x_47, x_43);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_18);
x_52 = l_Lean_Parser_Syntax_mkNode(x_11, x_51);
if (lean::obj_tag(x_7) == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_17);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_12);
lean::cnstr_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_command_structBinderContent;
x_58 = l_Lean_Parser_Syntax_mkNode(x_57, x_56);
return x_58;
}
else
{
obj* x_59; obj* x_62; obj* x_63; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
lean::dec(x_7);
x_62 = l_Lean_Parser_Term_binderDefault_HasView;
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
lean::dec(x_62);
x_66 = lean::apply_1(x_63, x_59);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_18);
x_68 = l_Lean_Parser_Syntax_mkNode(x_11, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_18);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_17);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_52);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_12);
lean::cnstr_set(x_72, 1, x_71);
x_73 = l_Lean_Parser_command_structBinderContent;
x_74 = l_Lean_Parser_Syntax_mkNode(x_73, x_72);
return x_74;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(obj* x_0) {
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
x_7 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_4);
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
if (lean::is_scalar(x_6)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_6;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_7);
return x_11;
}
case 3:
{
obj* x_12; obj* x_13; 
x_12 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
default:
{
obj* x_15; obj* x_16; 
lean::dec(x_2);
x_15 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_6)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_6;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOTAnIdent");
lean::inc(x_1);
x_3 = l_Lean_Parser_Substring_ofString(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_0 = x_4;
goto lbl_1;
}
else
{
obj* x_5; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_8);
x_0 = x_11;
goto lbl_1;
}
lbl_1:
{
obj* x_12; obj* x_14; obj* x_15; 
x_14 = lean::box(3);
x_15 = l_Lean_Parser_Syntax_asNode___main(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_12 = x_16;
goto lbl_13;
}
else
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_19 = x_15;
} else {
 lean::inc(x_17);
 lean::dec(x_15);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; 
lean::dec(x_19);
x_24 = lean::box(0);
x_12 = x_24;
goto lbl_13;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_30; obj* x_31; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_20, 0);
lean::inc(x_27);
lean::dec(x_20);
x_30 = l_Lean_Parser_command_inferModifier_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::apply_1(x_31, x_27);
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_34);
x_12 = x_35;
goto lbl_13;
}
else
{
obj* x_39; 
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_19);
x_39 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_12 = x_39;
goto lbl_13;
}
}
}
lbl_13:
{
obj* x_40; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
x_40 = l_Lean_Parser_command_optDeclSig_HasView;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
lean::dec(x_40);
x_44 = lean::box(3);
x_45 = lean::apply_1(x_41, x_44);
x_46 = l_Lean_Parser_Syntax_asNode___main(x_44);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; 
x_47 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_0);
lean::cnstr_set(x_48, 1, x_12);
lean::cnstr_set(x_48, 2, x_45);
lean::cnstr_set(x_48, 3, x_47);
return x_48;
}
else
{
obj* x_49; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 x_51 = x_46;
} else {
 lean::inc(x_49);
 lean::dec(x_46);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_51);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_0);
lean::cnstr_set(x_57, 1, x_12);
lean::cnstr_set(x_57, 2, x_45);
lean::cnstr_set(x_57, 3, x_56);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_52, 1);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_63; obj* x_64; obj* x_67; obj* x_68; obj* x_69; 
x_60 = lean::cnstr_get(x_52, 0);
lean::inc(x_60);
lean::dec(x_52);
x_63 = l_Lean_Parser_Term_binderDefault_HasView;
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
lean::dec(x_63);
x_67 = lean::apply_1(x_64, x_60);
if (lean::is_scalar(x_51)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_51;
}
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_0);
lean::cnstr_set(x_69, 1, x_12);
lean::cnstr_set(x_69, 2, x_45);
lean::cnstr_set(x_69, 3, x_68);
return x_69;
}
else
{
obj* x_73; obj* x_74; 
lean::dec(x_58);
lean::dec(x_51);
lean::dec(x_52);
x_73 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_0);
lean::cnstr_set(x_74, 1, x_12);
lean::cnstr_set(x_74, 2, x_45);
lean::cnstr_set(x_74, 3, x_73);
return x_74;
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2;
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
obj* x_18; obj* x_20; 
x_20 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
x_21 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_18 = x_21;
goto lbl_19;
}
else
{
obj* x_22; obj* x_25; obj* x_28; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_25);
x_18 = x_28;
goto lbl_19;
}
lbl_19:
{
obj* x_29; obj* x_30; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_32; 
x_32 = lean::box(3);
x_29 = x_1;
x_30 = x_32;
goto lbl_31;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
lean::dec(x_1);
x_29 = x_35;
x_30 = x_33;
goto lbl_31;
}
lbl_31:
{
obj* x_38; obj* x_40; 
x_40 = l_Lean_Parser_Syntax_asNode___main(x_30);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; 
x_41 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_38 = x_41;
goto lbl_39;
}
else
{
obj* x_42; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 x_44 = x_40;
} else {
 lean::inc(x_42);
 lean::dec(x_40);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_49; 
lean::dec(x_44);
x_49 = lean::box(0);
x_38 = x_49;
goto lbl_39;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_60; 
x_52 = lean::cnstr_get(x_45, 0);
lean::inc(x_52);
lean::dec(x_45);
x_55 = l_Lean_Parser_command_inferModifier_HasView;
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
lean::dec(x_55);
x_59 = lean::apply_1(x_56, x_52);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_59);
x_38 = x_60;
goto lbl_39;
}
else
{
obj* x_64; 
lean::dec(x_44);
lean::dec(x_45);
lean::dec(x_50);
x_64 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_38 = x_64;
goto lbl_39;
}
}
}
lbl_39:
{
obj* x_65; obj* x_66; 
if (lean::obj_tag(x_29) == 0)
{
obj* x_68; 
x_68 = lean::box(3);
x_65 = x_29;
x_66 = x_68;
goto lbl_67;
}
else
{
obj* x_69; obj* x_71; 
x_69 = lean::cnstr_get(x_29, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_29, 1);
lean::inc(x_71);
lean::dec(x_29);
x_65 = x_71;
x_66 = x_69;
goto lbl_67;
}
lbl_67:
{
obj* x_74; obj* x_75; obj* x_78; 
x_74 = l_Lean_Parser_command_optDeclSig_HasView;
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
lean::dec(x_74);
x_78 = lean::apply_1(x_75, x_66);
if (lean::obj_tag(x_65) == 0)
{
obj* x_79; obj* x_80; 
x_79 = lean::box(3);
x_80 = l_Lean_Parser_Syntax_asNode___main(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_82; 
x_81 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_82 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_82, 0, x_18);
lean::cnstr_set(x_82, 1, x_38);
lean::cnstr_set(x_82, 2, x_78);
lean::cnstr_set(x_82, 3, x_81);
return x_82;
}
else
{
obj* x_83; obj* x_85; obj* x_86; 
x_83 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_set(x_80, 0, lean::box(0));
 x_85 = x_80;
} else {
 lean::inc(x_83);
 lean::dec(x_80);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_91; 
lean::dec(x_85);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_91, 0, x_18);
lean::cnstr_set(x_91, 1, x_38);
lean::cnstr_set(x_91, 2, x_78);
lean::cnstr_set(x_91, 3, x_90);
return x_91;
}
else
{
obj* x_92; 
x_92 = lean::cnstr_get(x_86, 1);
lean::inc(x_92);
if (lean::obj_tag(x_92) == 0)
{
obj* x_94; obj* x_97; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
x_94 = lean::cnstr_get(x_86, 0);
lean::inc(x_94);
lean::dec(x_86);
x_97 = l_Lean_Parser_Term_binderDefault_HasView;
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
lean::dec(x_97);
x_101 = lean::apply_1(x_98, x_94);
if (lean::is_scalar(x_85)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_85;
}
lean::cnstr_set(x_102, 0, x_101);
x_103 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_103, 0, x_18);
lean::cnstr_set(x_103, 1, x_38);
lean::cnstr_set(x_103, 2, x_78);
lean::cnstr_set(x_103, 3, x_102);
return x_103;
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_86);
lean::dec(x_92);
lean::dec(x_85);
x_107 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_18);
lean::cnstr_set(x_108, 1, x_38);
lean::cnstr_set(x_108, 2, x_78);
lean::cnstr_set(x_108, 3, x_107);
return x_108;
}
}
}
}
else
{
obj* x_109; obj* x_112; 
x_109 = lean::cnstr_get(x_65, 0);
lean::inc(x_109);
lean::dec(x_65);
x_112 = l_Lean_Parser_Syntax_asNode___main(x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_114; 
x_113 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_114 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_114, 0, x_18);
lean::cnstr_set(x_114, 1, x_38);
lean::cnstr_set(x_114, 2, x_78);
lean::cnstr_set(x_114, 3, x_113);
return x_114;
}
else
{
obj* x_115; obj* x_117; obj* x_118; 
x_115 = lean::cnstr_get(x_112, 0);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_set(x_112, 0, lean::box(0));
 x_117 = x_112;
} else {
 lean::inc(x_115);
 lean::dec(x_112);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_118) == 0)
{
obj* x_122; obj* x_123; 
lean::dec(x_117);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_123, 0, x_18);
lean::cnstr_set(x_123, 1, x_38);
lean::cnstr_set(x_123, 2, x_78);
lean::cnstr_set(x_123, 3, x_122);
return x_123;
}
else
{
obj* x_124; 
x_124 = lean::cnstr_get(x_118, 1);
lean::inc(x_124);
if (lean::obj_tag(x_124) == 0)
{
obj* x_126; obj* x_129; obj* x_130; obj* x_133; obj* x_134; obj* x_135; 
x_126 = lean::cnstr_get(x_118, 0);
lean::inc(x_126);
lean::dec(x_118);
x_129 = l_Lean_Parser_Term_binderDefault_HasView;
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
lean::dec(x_129);
x_133 = lean::apply_1(x_130, x_126);
if (lean::is_scalar(x_117)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_117;
}
lean::cnstr_set(x_134, 0, x_133);
x_135 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_135, 0, x_18);
lean::cnstr_set(x_135, 1, x_38);
lean::cnstr_set(x_135, 2, x_78);
lean::cnstr_set(x_135, 3, x_134);
return x_135;
}
else
{
obj* x_139; obj* x_140; 
lean::dec(x_124);
lean::dec(x_118);
lean::dec(x_117);
x_139 = l_Lean_Parser_Term_binderContent_HasView_x_27___lambda__1___closed__1;
x_140 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_140, 0, x_18);
lean::cnstr_set(x_140, 1, x_38);
lean::cnstr_set(x_140, 2, x_78);
lean::cnstr_set(x_140, 3, x_139);
return x_140;
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
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structBinderContent_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_19; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_tokens___rarg(x_0);
x_2 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_3 = l_Lean_Parser_tokens___rarg(x_2);
x_4 = l_Lean_Parser_Term_binderDefault_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_0);
lean::dec(x_6);
x_10 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_8);
lean::dec(x_8);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_11);
lean::dec(x_11);
lean::dec(x_3);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_13);
lean::dec(x_13);
lean::dec(x_1);
x_19 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
return x_19;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_7 = 0;
x_8 = lean::box(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_10, 0, x_6);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault_Parser), 5, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_13, 0, x_12);
lean::closure_set(x_13, 1, x_8);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_Lean_Parser_command_structBinderContent;
x_21 = l_Lean_Parser_command_structBinderContent_HasView;
x_22 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_20, x_19, x_21);
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_22;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_3 = 0;
x_4 = lean::box(x_3);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault_Parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_command_structBinderContent_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_structBinderContent;
x_5 = l_Lean_Parser_command_structBinderContent_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structExplicitBinderContent");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_notationLike_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_structExplicitBinderContent;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_structBinderContent_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_structExplicitBinderContent;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_notationLike_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structExplicitBinderContent");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
lean::dec(x_39);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_58 = l_Lean_Parser_command_structBinderContent_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_52);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_68; obj* x_69; 
x_64 = l_Lean_Parser_command_notationLike_HasView;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
lean::dec(x_64);
x_68 = lean::apply_1(x_65, x_52);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_73 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_73;
}
}
}
}
}
}
}
else
{
obj* x_76; 
lean::dec(x_8);
lean::dec(x_17);
x_76 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1;
return x_76;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structExplicitBinder");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_command_structExplicitBinder;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_13);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(3);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_command_structExplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_structExplicitBinder;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_5, 0);
lean::inc(x_39);
lean::dec(x_5);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_13);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_12);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_33);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_structExplicitBinder;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_32; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 3:
{
obj* x_37; obj* x_38; 
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_26);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
default:
{
obj* x_40; obj* x_41; 
lean::dec(x_29);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_26);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_6, 0);
lean::inc(x_42);
lean::dec(x_6);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::box(0);
x_47 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_5, 1);
lean::inc(x_51);
lean::dec(x_5);
x_1 = x_45;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_54; 
x_54 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_60; 
x_55 = lean::cnstr_get(x_5, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::dec(x_5);
x_60 = lean::box(0);
x_1 = x_60;
x_2 = x_55;
x_3 = x_57;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; 
x_62 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_68; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
lean::dec(x_5);
x_68 = lean::box(0);
x_1 = x_68;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinder_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structExplicitBinder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structImplicitBinder");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_structBinderContent_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_command_structImplicitBinder;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_13);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(3);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_command_structImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_structImplicitBinder;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_5, 0);
lean::inc(x_39);
lean::dec(x_5);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_13);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_12);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_33);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_structImplicitBinder;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
}
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_structBinderContent_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_structBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_Lean_Parser_command_structBinderContent_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_32; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 3:
{
obj* x_37; obj* x_38; 
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_26);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
default:
{
obj* x_40; obj* x_41; 
lean::dec(x_29);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_26);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_6, 0);
lean::inc(x_42);
lean::dec(x_6);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::box(0);
x_47 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_5, 1);
lean::inc(x_51);
lean::dec(x_5);
x_1 = x_45;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_54; 
x_54 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_60; 
x_55 = lean::cnstr_get(x_5, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::dec(x_5);
x_60 = lean::box(0);
x_1 = x_60;
x_2 = x_55;
x_3 = x_57;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; 
x_62 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_68; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
lean::dec(x_5);
x_68 = lean::box(0);
x_1 = x_68;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structImplicitBinder_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("strictImplicitBinder");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_structBinderContent_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_command_strictImplicitBinder;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_13);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(3);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_command_strictImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_strictImplicitBinder;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_5, 0);
lean::inc(x_39);
lean::dec(x_5);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_13);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_12);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_33);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_strictImplicitBinder;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
}
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_structBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_Lean_Parser_command_structBinderContent_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_32; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 3:
{
obj* x_37; obj* x_38; 
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_26);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
default:
{
obj* x_40; obj* x_41; 
lean::dec(x_29);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_26);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_6, 0);
lean::inc(x_42);
lean::dec(x_6);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::box(0);
x_47 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_5, 1);
lean::inc(x_51);
lean::dec(x_5);
x_1 = x_45;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_54; 
x_54 = l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_60; 
x_55 = lean::cnstr_get(x_5, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::dec(x_5);
x_60 = lean::box(0);
x_1 = x_60;
x_2 = x_55;
x_3 = x_57;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; 
x_62 = l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_68; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
lean::dec(x_5);
x_68 = lean::box(0);
x_1 = x_68;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_strictImplicitBinder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("instImplicitBinder");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_structBinderContent_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = l_Lean_Parser_command_instImplicitBinder;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_13);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(3);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Parser_command_instImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_instImplicitBinder;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_5, 0);
lean::inc(x_39);
lean::dec(x_5);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_13);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_12);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_33);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_instImplicitBinder;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
}
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_structBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_Lean_Parser_command_structBinderContent_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
switch (lean::obj_tag(x_29)) {
case 0:
{
obj* x_32; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 3:
{
obj* x_37; obj* x_38; 
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_26);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
default:
{
obj* x_40; obj* x_41; 
lean::dec(x_29);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_26);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_6, 0);
lean::inc(x_42);
lean::dec(x_6);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::box(0);
x_47 = l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_5, 1);
lean::inc(x_51);
lean::dec(x_5);
x_1 = x_45;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_54; 
x_54 = l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_60; 
x_55 = lean::cnstr_get(x_5, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::dec(x_5);
x_60 = lean::box(0);
x_1 = x_60;
x_2 = x_55;
x_3 = x_57;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; 
x_62 = l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1;
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_68; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
lean::dec(x_5);
x_68 = lean::box(0);
x_1 = x_68;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instImplicitBinder_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_instImplicitBinder_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structureFieldBlock");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_structureFieldBlock;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_structImplicitBinder_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_structureFieldBlock;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
case 2:
{
obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_Parser_command_strictImplicitBinder_HasView;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::apply_1(x_34, x_30);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__4;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_1);
x_42 = l_Lean_Parser_command_structureFieldBlock;
x_43 = l_Lean_Parser_Syntax_mkNode(x_42, x_41);
return x_43;
}
default:
{
obj* x_44; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l_Lean_Parser_command_instImplicitBinder_HasView;
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::apply_1(x_48, x_44);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_1);
x_53 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__6;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_1);
x_56 = l_Lean_Parser_command_structureFieldBlock;
x_57 = l_Lean_Parser_Syntax_mkNode(x_56, x_55);
return x_57;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structureFieldBlock");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = lean::mk_nat_obj(1ul);
x_58 = lean::nat_dec_eq(x_39, x_57);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; 
x_59 = lean::mk_nat_obj(2ul);
x_60 = lean::nat_dec_eq(x_39, x_59);
lean::dec(x_39);
if (x_60 == 0)
{
obj* x_62; obj* x_63; obj* x_66; obj* x_67; 
x_62 = l_Lean_Parser_command_instImplicitBinder_HasView;
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
lean::dec(x_62);
x_66 = lean::apply_1(x_63, x_52);
x_67 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_72; obj* x_73; 
x_68 = l_Lean_Parser_command_strictImplicitBinder_HasView;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_52);
x_73 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
else
{
obj* x_75; obj* x_76; obj* x_79; obj* x_80; 
lean::dec(x_39);
x_75 = l_Lean_Parser_command_structImplicitBinder_HasView;
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
lean::dec(x_75);
x_79 = lean::apply_1(x_76, x_52);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
}
else
{
obj* x_82; obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_39);
x_82 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
lean::dec(x_82);
x_86 = lean::apply_1(x_83, x_52);
x_87 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
}
else
{
obj* x_91; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_91 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_91;
}
}
}
}
}
}
}
else
{
obj* x_94; 
lean::dec(x_8);
lean::dec(x_17);
x_94 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1;
return x_94;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structureFieldBlock_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_84; obj* x_87; obj* x_89; obj* x_91; 
x_0 = lean::mk_string("(");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_8);
lean::dec(x_8);
lean::dec(x_5);
x_12 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_6);
lean::dec(x_12);
x_16 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
x_18 = lean::mk_string(")");
x_19 = l_Lean_Parser_symbol_tokens___rarg(x_18, x_1);
lean::dec(x_18);
x_21 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_6);
lean::dec(x_19);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_16, x_21);
lean::dec(x_21);
lean::dec(x_16);
x_26 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_23);
lean::dec(x_23);
lean::dec(x_2);
x_29 = l_Lean_Parser_tokens___rarg(x_26);
lean::dec(x_26);
x_31 = lean::mk_string("{");
x_32 = l_Lean_Parser_symbol_tokens___rarg(x_31, x_1);
lean::dec(x_31);
x_34 = lean::mk_string("}");
x_35 = l_Lean_Parser_symbol_tokens___rarg(x_34, x_1);
lean::dec(x_34);
x_37 = l_Lean_Parser_List_cons_tokens___rarg(x_35, x_6);
lean::dec(x_35);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_37);
lean::dec(x_37);
x_41 = l_Lean_Parser_List_cons_tokens___rarg(x_32, x_39);
lean::dec(x_39);
lean::dec(x_32);
x_44 = l_Lean_Parser_tokens___rarg(x_41);
lean::dec(x_41);
x_46 = lean::mk_string("\xe2\xa6\x83");
x_47 = l_Lean_Parser_symbol_tokens___rarg(x_46, x_1);
lean::dec(x_46);
x_49 = lean::mk_string("\xe2\xa6\x84");
x_50 = l_Lean_Parser_symbol_tokens___rarg(x_49, x_1);
lean::dec(x_49);
x_52 = l_Lean_Parser_List_cons_tokens___rarg(x_50, x_6);
lean::dec(x_50);
x_54 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_52);
lean::dec(x_52);
x_56 = l_Lean_Parser_List_cons_tokens___rarg(x_47, x_54);
lean::dec(x_54);
lean::dec(x_47);
x_59 = l_Lean_Parser_tokens___rarg(x_56);
lean::dec(x_56);
x_61 = lean::mk_string("[");
x_62 = l_Lean_Parser_symbol_tokens___rarg(x_61, x_1);
lean::dec(x_61);
x_64 = lean::mk_string("]");
x_65 = l_Lean_Parser_symbol_tokens___rarg(x_64, x_1);
lean::dec(x_64);
x_67 = l_Lean_Parser_List_cons_tokens___rarg(x_65, x_6);
lean::dec(x_65);
x_69 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_67);
lean::dec(x_67);
x_71 = l_Lean_Parser_List_cons_tokens___rarg(x_62, x_69);
lean::dec(x_69);
lean::dec(x_62);
x_74 = l_Lean_Parser_tokens___rarg(x_71);
lean::dec(x_71);
x_76 = l_Lean_Parser_List_cons_tokens___rarg(x_74, x_6);
lean::dec(x_74);
x_78 = l_Lean_Parser_List_cons_tokens___rarg(x_59, x_76);
lean::dec(x_76);
lean::dec(x_59);
x_81 = l_Lean_Parser_List_cons_tokens___rarg(x_44, x_78);
lean::dec(x_78);
lean::dec(x_44);
x_84 = l_Lean_Parser_List_cons_tokens___rarg(x_29, x_81);
lean::dec(x_81);
lean::dec(x_29);
x_87 = l_Lean_Parser_tokens___rarg(x_84);
lean::dec(x_84);
x_89 = l_Lean_Parser_List_cons_tokens___rarg(x_87, x_6);
lean::dec(x_87);
x_91 = l_Lean_Parser_tokens___rarg(x_89);
lean::dec(x_89);
return x_91;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("(");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_Parser), 4, 0);
lean::inc(x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_18, 0, x_17);
lean::closure_set(x_18, 1, x_9);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
x_20 = l_Lean_Parser_command_structExplicitBinderContent;
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_19);
x_22 = lean::mk_string(")");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_26, 0, x_23);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_27, 0, x_23);
lean::closure_set(x_27, 1, x_9);
lean::closure_set(x_27, 2, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_13);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_10);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_structExplicitBinder;
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_32, 0, x_31);
lean::closure_set(x_32, 1, x_30);
x_33 = lean::mk_string("{");
x_34 = l_String_trim(x_33);
lean::dec(x_33);
lean::inc(x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_37, 0, x_34);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_38, 0, x_34);
lean::closure_set(x_38, 1, x_9);
lean::closure_set(x_38, 2, x_37);
x_39 = lean::mk_string("}");
x_40 = l_String_trim(x_39);
lean::dec(x_39);
lean::inc(x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_43, 0, x_40);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_44, 0, x_40);
lean::closure_set(x_44, 1, x_9);
lean::closure_set(x_44, 2, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_13);
lean::inc(x_14);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_14);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_38);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_Lean_Parser_command_structImplicitBinder;
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_50, 0, x_49);
lean::closure_set(x_50, 1, x_48);
x_51 = lean::mk_string("\xe2\xa6\x83");
x_52 = l_String_trim(x_51);
lean::dec(x_51);
lean::inc(x_52);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_55, 0, x_52);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_56, 0, x_52);
lean::closure_set(x_56, 1, x_9);
lean::closure_set(x_56, 2, x_55);
x_57 = lean::mk_string("\xe2\xa6\x84");
x_58 = l_String_trim(x_57);
lean::dec(x_57);
lean::inc(x_58);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_61, 0, x_58);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_62, 0, x_58);
lean::closure_set(x_62, 1, x_9);
lean::closure_set(x_62, 2, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_13);
lean::inc(x_14);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_14);
lean::cnstr_set(x_65, 1, x_63);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_56);
lean::cnstr_set(x_66, 1, x_65);
x_67 = l_Lean_Parser_command_strictImplicitBinder;
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_68, 0, x_67);
lean::closure_set(x_68, 1, x_66);
x_69 = lean::mk_string("[");
x_70 = l_String_trim(x_69);
lean::dec(x_69);
lean::inc(x_70);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_73, 0, x_70);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_74, 0, x_70);
lean::closure_set(x_74, 1, x_9);
lean::closure_set(x_74, 2, x_73);
x_75 = lean::mk_string("]");
x_76 = l_String_trim(x_75);
lean::dec(x_75);
lean::inc(x_76);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_79, 0, x_76);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_80, 0, x_76);
lean::closure_set(x_80, 1, x_9);
lean::closure_set(x_80, 2, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_13);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_14);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_74);
lean::cnstr_set(x_83, 1, x_82);
x_84 = l_Lean_Parser_command_instImplicitBinder;
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_85, 0, x_84);
lean::closure_set(x_85, 1, x_83);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_13);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_68);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_50);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_32);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_90, 0, x_89);
lean::closure_set(x_90, 1, x_9);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_13);
x_92 = l_Lean_Parser_command_structureFieldBlock;
x_93 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_94 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_92, x_91, x_93);
lean::dec(x_91);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_94;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_0 = lean::mk_string("(");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_Parser), 4, 0);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_14, 0, x_13);
lean::closure_set(x_14, 1, x_5);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_9);
x_16 = l_Lean_Parser_command_structExplicitBinderContent;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = lean::mk_string(")");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_22, 0, x_19);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_5);
lean::closure_set(x_23, 2, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_9);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_17);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_structExplicitBinder;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::mk_string("{");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_33, 0, x_30);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_30);
lean::closure_set(x_34, 1, x_5);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::mk_string("}");
x_36 = l_String_trim(x_35);
lean::dec(x_35);
lean::inc(x_36);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_39, 0, x_36);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_5);
lean::closure_set(x_40, 2, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_9);
lean::inc(x_10);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_10);
lean::cnstr_set(x_43, 1, x_41);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_Parser_command_structImplicitBinder;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_46, 0, x_45);
lean::closure_set(x_46, 1, x_44);
x_47 = lean::mk_string("\xe2\xa6\x83");
x_48 = l_String_trim(x_47);
lean::dec(x_47);
lean::inc(x_48);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_51, 0, x_48);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_52, 0, x_48);
lean::closure_set(x_52, 1, x_5);
lean::closure_set(x_52, 2, x_51);
x_53 = lean::mk_string("\xe2\xa6\x84");
x_54 = l_String_trim(x_53);
lean::dec(x_53);
lean::inc(x_54);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_57, 0, x_54);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_58, 0, x_54);
lean::closure_set(x_58, 1, x_5);
lean::closure_set(x_58, 2, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_9);
lean::inc(x_10);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_10);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_52);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_Lean_Parser_command_strictImplicitBinder;
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_64, 0, x_63);
lean::closure_set(x_64, 1, x_62);
x_65 = lean::mk_string("[");
x_66 = l_String_trim(x_65);
lean::dec(x_65);
lean::inc(x_66);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_69, 0, x_66);
x_70 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_70, 0, x_66);
lean::closure_set(x_70, 1, x_5);
lean::closure_set(x_70, 2, x_69);
x_71 = lean::mk_string("]");
x_72 = l_String_trim(x_71);
lean::dec(x_71);
lean::inc(x_72);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_75, 0, x_72);
x_76 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_76, 0, x_72);
lean::closure_set(x_76, 1, x_5);
lean::closure_set(x_76, 2, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_9);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_10);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_70);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_Lean_Parser_command_instImplicitBinder;
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_81, 0, x_80);
lean::closure_set(x_81, 1, x_79);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_9);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_64);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_46);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_28);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_86, 0, x_85);
lean::closure_set(x_86, 1, x_5);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_9);
return x_87;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_structureFieldBlock;
x_5 = l_Lean_Parser_command_structureFieldBlock_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("oldUnivParams");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(x_3);
x_9 = l_Lean_Parser_noKind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
x_11 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::box(3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_Lean_Parser_command_oldUnivParams;
x_17 = l_Lean_Parser_Syntax_mkNode(x_16, x_15);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_11);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_10);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::box(3);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_command_oldUnivParams;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
}
else
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_oldUnivParams;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
lean::dec(x_5);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_10);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_31);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_Parser_command_oldUnivParams;
x_45 = l_Lean_Parser_Syntax_mkNode(x_44, x_43);
return x_45;
}
}
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_0);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_0);
return x_12;
}
}
}
obj* l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
x_36 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(0);
if (lean::obj_tag(x_27) == 0)
{
obj* x_38; obj* x_39; 
x_38 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_18);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set(x_39, 2, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_27, 0);
lean::inc(x_40);
lean::dec(x_27);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_43);
x_47 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
case 3:
{
obj* x_49; obj* x_50; 
x_49 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_18);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_37);
return x_50;
}
default:
{
obj* x_52; obj* x_53; 
lean::dec(x_40);
x_52 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_18);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_37);
return x_53;
}
}
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_60; 
x_54 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_56 = x_36;
} else {
 lean::inc(x_54);
 lean::dec(x_36);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_57);
if (lean::obj_tag(x_27) == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_56);
x_62 = lean::box(0);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_18);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set(x_63, 2, x_62);
return x_63;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_27, 0);
lean::inc(x_64);
lean::dec(x_27);
switch (lean::obj_tag(x_64)) {
case 0:
{
obj* x_67; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
if (lean::is_scalar(x_56)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_56;
}
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_18);
lean::cnstr_set(x_71, 1, x_60);
lean::cnstr_set(x_71, 2, x_70);
return x_71;
}
case 3:
{
obj* x_73; obj* x_74; 
lean::dec(x_56);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_18);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
default:
{
obj* x_77; obj* x_78; 
lean::dec(x_64);
lean::dec(x_56);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_18);
lean::cnstr_set(x_78, 1, x_60);
lean::cnstr_set(x_78, 2, x_77);
return x_78;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_oldUnivParams_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; 
x_0 = lean::mk_string("{");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::mk_string("}");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_1);
lean::dec(x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_4);
lean::dec(x_7);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_11);
lean::dec(x_11);
lean::dec(x_2);
x_17 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
return x_17;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("{");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::mk_string("}");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_9);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_10);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_oldUnivParams;
x_24 = l_Lean_Parser_command_oldUnivParams_HasView;
x_25 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_23, x_22, x_24);
lean::dec(x_22);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_25;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string("{");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("}");
x_10 = l_String_trim(x_9);
lean::dec(x_9);
lean::inc(x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_13, 0, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_14, 0, x_10);
lean::closure_set(x_14, 1, x_5);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l_Lean_Parser_command_oldUnivParams_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_oldUnivParams;
x_5 = l_Lean_Parser_command_oldUnivParams_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_univParams() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("univParams");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_univParams_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___elambda__1___spec__1(x_3);
x_9 = l_Lean_Parser_noKind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
x_11 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::box(3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_Lean_Parser_command_univParams;
x_17 = l_Lean_Parser_Syntax_mkNode(x_16, x_15);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_11);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_10);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::box(3);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = l_Lean_Parser_command_univParams;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
}
else
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_univParams;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
lean::dec(x_5);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_10);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_31);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_Parser_command_univParams;
x_45 = l_Lean_Parser_Syntax_mkNode(x_44, x_43);
return x_45;
}
}
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_0);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_0);
return x_12;
}
}
}
obj* l_Lean_Parser_command_univParams_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_29:
{
obj* x_36; 
x_36 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(0);
if (lean::obj_tag(x_27) == 0)
{
obj* x_38; obj* x_39; 
x_38 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_18);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set(x_39, 2, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_27, 0);
lean::inc(x_40);
lean::dec(x_27);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_43);
x_47 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set(x_48, 2, x_46);
return x_48;
}
case 3:
{
obj* x_49; obj* x_50; 
x_49 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_18);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_37);
return x_50;
}
default:
{
obj* x_52; obj* x_53; 
lean::dec(x_40);
x_52 = l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_18);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_37);
return x_53;
}
}
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_60; 
x_54 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_56 = x_36;
} else {
 lean::inc(x_54);
 lean::dec(x_36);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x_27___spec__1(x_57);
if (lean::obj_tag(x_27) == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_56);
x_62 = lean::box(0);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_18);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set(x_63, 2, x_62);
return x_63;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_27, 0);
lean::inc(x_64);
lean::dec(x_27);
switch (lean::obj_tag(x_64)) {
case 0:
{
obj* x_67; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
if (lean::is_scalar(x_56)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_56;
}
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_18);
lean::cnstr_set(x_71, 1, x_60);
lean::cnstr_set(x_71, 2, x_70);
return x_71;
}
case 3:
{
obj* x_73; obj* x_74; 
lean::dec(x_56);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_18);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
default:
{
obj* x_77; obj* x_78; 
lean::dec(x_64);
lean::dec(x_56);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_18);
lean::cnstr_set(x_78, 1, x_60);
lean::cnstr_set(x_78, 2, x_77);
return x_78;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_univParams_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_univParams_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_univParams_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("identUnivParams");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_detailIdent_HasView_x_27___elambda__1___closed__1;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_command_identUnivParams;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_command_univParams_HasView;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_11);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
x_21 = l_Lean_Parser_noKind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_14);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_command_identUnivParams;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
return x_26;
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOTAnIdent");
lean::inc(x_1);
x_3 = l_Lean_Parser_Substring_ofString(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = l_Lean_Parser_command_univParams_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::box(3);
x_13 = lean::apply_1(x_9, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOTAnIdent");
lean::inc(x_1);
x_3 = l_Lean_Parser_Substring_ofString(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1;
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
x_10 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = l_Lean_Parser_command_univParams_HasView;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
x_20 = lean::apply_1(x_17, x_13);
if (lean::is_scalar(x_5)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_5;
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_27; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_5);
x_27 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1;
return x_27;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_univParams_HasView;
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
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3;
return x_0;
}
}
obj* l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5;
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
switch (lean::obj_tag(x_2)) {
case 1:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_29);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_20);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_41 = l_Lean_Parser_command_univParams_HasView;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_38);
if (lean::is_scalar(x_29)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_29;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_29);
x_51 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_20);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_56; obj* x_59; 
x_53 = lean::cnstr_get(x_2, 0);
lean::inc(x_53);
lean::dec(x_2);
x_56 = lean::cnstr_get(x_1, 0);
lean::inc(x_56);
lean::dec(x_1);
x_59 = l_Lean_Parser_Syntax_asNode___main(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; 
x_60 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4;
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_53);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
else
{
obj* x_62; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_set(x_59, 0, lean::box(0));
 x_64 = x_59;
} else {
 lean::inc(x_62);
 lean::dec(x_59);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
if (lean::obj_tag(x_65) == 0)
{
obj* x_69; obj* x_70; 
lean::dec(x_64);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_53);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_65, 1);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_76; obj* x_77; obj* x_80; obj* x_81; obj* x_82; 
x_73 = lean::cnstr_get(x_65, 0);
lean::inc(x_73);
lean::dec(x_65);
x_76 = l_Lean_Parser_command_univParams_HasView;
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
lean::dec(x_76);
x_80 = lean::apply_1(x_77, x_73);
if (lean::is_scalar(x_64)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_64;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_53);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
else
{
obj* x_86; obj* x_87; 
lean::dec(x_64);
lean::dec(x_65);
lean::dec(x_71);
x_86 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4;
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_53);
lean::cnstr_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
case 3:
{
obj* x_88; 
x_88 = lean::box(0);
x_18 = x_88;
goto lbl_19;
}
default:
{
obj* x_90; 
lean::dec(x_2);
x_90 = lean::box(0);
x_18 = x_90;
goto lbl_19;
}
}
lbl_19:
{
lean::dec(x_18);
if (lean::obj_tag(x_1) == 0)
{
obj* x_92; 
x_92 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3;
return x_92;
}
else
{
obj* x_93; obj* x_96; 
x_93 = lean::cnstr_get(x_1, 0);
lean::inc(x_93);
lean::dec(x_1);
x_96 = l_Lean_Parser_Syntax_asNode___main(x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; 
x_97 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1;
return x_97;
}
else
{
obj* x_98; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_set(x_96, 0, lean::box(0));
 x_100 = x_96;
} else {
 lean::inc(x_98);
 lean::dec(x_96);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
if (lean::obj_tag(x_101) == 0)
{
obj* x_105; 
lean::dec(x_100);
x_105 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2;
return x_105;
}
else
{
obj* x_106; 
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_108; obj* x_111; obj* x_112; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_108 = lean::cnstr_get(x_101, 0);
lean::inc(x_108);
lean::dec(x_101);
x_111 = l_Lean_Parser_command_univParams_HasView;
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
lean::dec(x_111);
x_115 = lean::apply_1(x_112, x_108);
if (lean::is_scalar(x_100)) {
 x_116 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_116 = x_100;
}
lean::cnstr_set(x_116, 0, x_115);
x_117 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
else
{
obj* x_122; 
lean::dec(x_100);
lean::dec(x_106);
lean::dec(x_101);
x_122 = l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1;
return x_122;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_identUnivParams_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".{");
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_Parser_tokens___rarg(x_0);
x_6 = lean::mk_string("}");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_2);
lean::dec(x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_0);
lean::dec(x_7);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_11);
lean::dec(x_11);
lean::dec(x_3);
x_17 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
x_19 = l_Lean_Parser_tokens___rarg(x_17);
lean::dec(x_17);
x_21 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_0);
lean::dec(x_19);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_21);
lean::dec(x_21);
x_25 = l_Lean_Parser_tokens___rarg(x_23);
lean::dec(x_23);
return x_25;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string(".{");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = lean::mk_string("}");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_18, 0, x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_19, 0, x_15);
lean::closure_set(x_19, 1, x_9);
lean::closure_set(x_19, 2, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_13);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_10);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_command_univParams;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean::box(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_20);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_11);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_identUnivParams;
x_32 = l_Lean_Parser_command_identUnivParams_HasView;
x_33 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_31, x_30, x_32);
lean::dec(x_30);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_33;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_0 = lean::mk_string(".{");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::mk_string("}");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_15, 0, x_11);
lean::closure_set(x_15, 1, x_5);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_6);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_Lean_Parser_command_univParams;
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_19);
x_22 = 0;
x_23 = lean::box(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_24, 0, x_21);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
obj* l_Lean_Parser_command_identUnivParams_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_identUnivParams;
x_5 = l_Lean_Parser_command_identUnivParams_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structureKw() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structureKw");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_structureKw;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_structureKw;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_structureKw;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_structureKw;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structureKw");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0ul);
x_60 = lean::nat_dec_eq(x_41, x_59);
lean::dec(x_41);
if (x_60 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_62; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_26;
}
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
case 3:
{
obj* x_68; 
lean::dec(x_26);
x_68 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1;
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_56);
lean::dec(x_26);
x_71 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_56, 0);
lean::inc(x_72);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_26;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
case 3:
{
obj* x_78; 
lean::dec(x_26);
x_78 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2;
return x_78;
}
default:
{
obj* x_81; 
lean::dec(x_56);
lean::dec(x_26);
x_81 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2;
return x_81;
}
}
}
}
else
{
obj* x_86; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_86 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_86;
}
}
}
}
}
}
}
else
{
obj* x_89; 
lean::dec(x_8);
lean::dec(x_17);
x_89 = l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3;
return x_89;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structureKw_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_extends() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("extends");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_extends_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_List_map___main___at_Lean_Parser_Term_tuple_HasView_x_27___elambda__1___spec__1(x_3);
x_7 = l_List_join___main___rarg(x_6);
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
x_14 = l_Lean_Parser_command_extends;
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
x_21 = l_Lean_Parser_command_extends;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 x_8 = x_2;
} else {
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_4, 0);
x_18 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_20 = x_4;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_4);
 x_20 = lean::box(0);
}
x_21 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(x_0, x_1, x_18);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_16, 0);
lean::inc(x_22);
lean::dec(x_16);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_13);
lean::cnstr_set(x_27, 1, x_26);
if (lean::is_scalar(x_20)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_20;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
return x_28;
}
case 3:
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_13);
lean::cnstr_set(x_30, 1, x_29);
if (lean::is_scalar(x_20)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_20;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_21);
return x_31;
}
default:
{
obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_16);
x_33 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_13);
lean::cnstr_set(x_34, 1, x_33);
if (lean::is_scalar(x_20)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_20;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_21);
return x_35;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_Term_tuple_HasView_x_27___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1;
x_12 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
x_13 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(x_11, x_12, x_8);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2;
return x_0;
}
}
obj* l_Lean_Parser_command_extends_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3;
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
obj* x_18; obj* x_19; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::box(3);
x_26 = l_Lean_Parser_Syntax_asNode___main(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; 
x_27 = l_Lean_Parser_Term_tuple_HasView_x_27___lambda__1___closed__1;
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1;
x_36 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
x_37 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(x_35, x_36, x_32);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_24);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_1, 0);
lean::inc(x_39);
lean::dec(x_1);
x_18 = x_24;
x_19 = x_39;
goto lbl_20;
}
}
case 3:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_42; 
x_42 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2;
return x_42;
}
else
{
obj* x_43; obj* x_46; 
x_43 = lean::cnstr_get(x_1, 0);
lean::inc(x_43);
lean::dec(x_1);
x_46 = lean::box(0);
x_18 = x_46;
x_19 = x_43;
goto lbl_20;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_48; 
x_48 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2;
return x_48;
}
else
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_1, 0);
lean::inc(x_49);
lean::dec(x_1);
x_52 = lean::box(0);
x_18 = x_52;
x_19 = x_49;
goto lbl_20;
}
}
}
lbl_20:
{
obj* x_53; 
x_53 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_55; 
x_54 = l_Lean_Parser_Term_tuple_HasView_x_27___lambda__1___closed__1;
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_18);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
else
{
obj* x_56; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
lean::dec(x_53);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_62 = l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1;
x_63 = l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3;
x_64 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(x_62, x_63, x_59);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_18);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_extends_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_extends_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_extends_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_extends_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structureCtor() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structureCtor");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_structureCtor_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_1);
x_9 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = l_Lean_Parser_Term_paren_HasView_x_27___elambda__1___closed__2;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_command_structureCtor;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_5, 0);
lean::inc(x_14);
lean::dec(x_5);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
x_19 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_command_structureCtor;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
return x_23;
}
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_24 = lean::cnstr_get(x_3, 0);
lean::inc(x_24);
lean::dec(x_3);
x_27 = l_Lean_Parser_command_inferModifier_HasView;
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
lean::dec(x_27);
x_31 = lean::apply_1(x_28, x_24);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
x_33 = l_Lean_Parser_noKind;
x_34 = l_Lean_Parser_Syntax_mkNode(x_33, x_32);
if (lean::obj_tag(x_5) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___elambda__1___closed__2;
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_8);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_command_structureCtor;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_5, 0);
lean::inc(x_40);
lean::dec(x_5);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_9);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_34);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_8);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_Lean_Parser_command_structureCtor;
x_48 = l_Lean_Parser_Syntax_mkNode(x_47, x_46);
return x_48;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_4 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_8);
x_13 = lean::box(0);
x_14 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
lean::dec(x_9);
x_21 = l_Lean_Parser_command_inferModifier_HasView;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
lean::dec(x_21);
x_25 = lean::apply_1(x_22, x_18);
if (lean::is_scalar(x_8)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_8;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_27);
return x_29;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_16);
x_33 = lean::box(0);
x_34 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_35 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set(x_36, 2, x_33);
return x_36;
}
}
}
}
}
obj* l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_18 = x_20;
goto lbl_19;
}
case 3:
{
obj* x_23; 
x_23 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_18 = x_23;
goto lbl_19;
}
default:
{
obj* x_25; 
lean::dec(x_2);
x_25 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_18 = x_25;
goto lbl_19;
}
}
lbl_19:
{
obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_32; 
x_32 = lean::box(3);
x_29 = x_1;
x_30 = x_32;
goto lbl_31;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_1, 1);
lean::inc(x_35);
lean::dec(x_1);
x_29 = x_35;
x_30 = x_33;
goto lbl_31;
}
lbl_28:
{
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_27, 0);
lean::inc(x_38);
lean::dec(x_27);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_18);
lean::cnstr_set(x_42, 1, x_26);
lean::cnstr_set(x_42, 2, x_41);
return x_42;
}
case 3:
{
obj* x_43; obj* x_44; 
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_18);
lean::cnstr_set(x_44, 1, x_26);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
default:
{
obj* x_46; obj* x_47; 
lean::dec(x_27);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_18);
lean::cnstr_set(x_47, 1, x_26);
lean::cnstr_set(x_47, 2, x_46);
return x_47;
}
}
}
lbl_31:
{
obj* x_48; 
x_48 = l_Lean_Parser_Syntax_asNode___main(x_30);
if (lean::obj_tag(x_48) == 0)
{
if (lean::obj_tag(x_29) == 0)
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::box(0);
x_50 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_18);
lean::cnstr_set(x_51, 1, x_50);
lean::cnstr_set(x_51, 2, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_29, 0);
lean::inc(x_52);
lean::dec(x_29);
x_55 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_26 = x_55;
x_27 = x_52;
goto lbl_28;
}
}
else
{
obj* x_56; obj* x_58; obj* x_59; 
x_56 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 x_58 = x_48;
} else {
 lean::inc(x_56);
 lean::dec(x_48);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_59) == 0)
{
obj* x_63; 
lean::dec(x_58);
x_63 = lean::box(0);
if (lean::obj_tag(x_29) == 0)
{
obj* x_64; 
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_18);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set(x_64, 2, x_63);
return x_64;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_29, 0);
lean::inc(x_65);
lean::dec(x_29);
x_26 = x_63;
x_27 = x_65;
goto lbl_28;
}
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_59, 1);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_74; obj* x_77; obj* x_78; 
x_70 = lean::cnstr_get(x_59, 0);
lean::inc(x_70);
lean::dec(x_59);
x_73 = l_Lean_Parser_command_inferModifier_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_70);
if (lean::is_scalar(x_58)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_58;
}
lean::cnstr_set(x_78, 0, x_77);
if (lean::obj_tag(x_29) == 0)
{
obj* x_79; obj* x_80; 
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_18);
lean::cnstr_set(x_80, 1, x_78);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_29, 0);
lean::inc(x_81);
lean::dec(x_29);
x_26 = x_78;
x_27 = x_81;
goto lbl_28;
}
}
else
{
lean::dec(x_58);
lean::dec(x_59);
lean::dec(x_68);
if (lean::obj_tag(x_29) == 0)
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = lean::box(0);
x_88 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_18);
lean::cnstr_set(x_89, 1, x_88);
lean::cnstr_set(x_89, 2, x_87);
return x_89;
}
else
{
obj* x_90; obj* x_93; 
x_90 = lean::cnstr_get(x_29, 0);
lean::inc(x_90);
lean::dec(x_29);
x_93 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1;
x_26 = x_93;
x_27 = x_90;
goto lbl_28;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structureCtor_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureCtor_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureCtor_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structureCtor_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structure() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_structure_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 7);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_Lean_Parser_command_structureKw_HasView;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_1);
x_23 = l_Lean_Parser_command_identUnivParams_HasView;
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_5);
x_28 = l_Lean_Parser_command_optDeclSig_HasView;
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
lean::dec(x_28);
x_32 = lean::apply_1(x_29, x_7);
x_33 = l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1;
x_34 = l_List_map___main___rarg(x_33, x_15);
x_35 = l_Lean_Parser_noKind;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
if (lean::obj_tag(x_3) == 0)
{
obj* x_41; 
x_41 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_39 = x_41;
goto lbl_40;
}
else
{
obj* x_42; obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_42 = lean::cnstr_get(x_3, 0);
lean::inc(x_42);
lean::dec(x_3);
x_45 = l_Lean_Parser_command_oldUnivParams_HasView;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
lean::dec(x_45);
x_49 = lean::apply_1(x_46, x_42);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_37);
x_51 = l_Lean_Parser_Syntax_mkNode(x_35, x_50);
x_39 = x_51;
goto lbl_40;
}
lbl_40:
{
obj* x_52; obj* x_54; obj* x_55; 
if (lean::obj_tag(x_9) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_57; 
x_57 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_52 = x_57;
goto lbl_53;
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_11, 0);
lean::inc(x_58);
lean::dec(x_11);
x_61 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_54 = x_61;
x_55 = x_58;
goto lbl_56;
}
}
else
{
obj* x_62; obj* x_65; obj* x_66; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_9, 0);
lean::inc(x_62);
lean::dec(x_9);
x_65 = l_Lean_Parser_command_extends_HasView;
x_66 = lean::cnstr_get(x_65, 1);
lean::inc(x_66);
lean::dec(x_65);
x_69 = lean::apply_1(x_66, x_62);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_37);
x_71 = l_Lean_Parser_Syntax_mkNode(x_35, x_70);
if (lean::obj_tag(x_11) == 0)
{
x_52 = x_71;
goto lbl_53;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_11, 0);
lean::inc(x_72);
lean::dec(x_11);
x_54 = x_71;
x_55 = x_72;
goto lbl_56;
}
}
lbl_53:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_75 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_38);
x_77 = lean::box(3);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_52);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_32);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_27);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_39);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_22);
lean::cnstr_set(x_83, 1, x_82);
x_84 = l_Lean_Parser_command_structure;
x_85 = l_Lean_Parser_Syntax_mkNode(x_84, x_83);
return x_85;
}
else
{
obj* x_86; obj* x_89; obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_86 = lean::cnstr_get(x_13, 0);
lean::inc(x_86);
lean::dec(x_13);
x_89 = l_Lean_Parser_command_structureCtor_HasView;
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
x_93 = lean::apply_1(x_90, x_86);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_37);
x_95 = l_Lean_Parser_Syntax_mkNode(x_35, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_38);
x_97 = lean::box(3);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_96);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_52);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_32);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_27);
lean::cnstr_set(x_101, 1, x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_39);
lean::cnstr_set(x_102, 1, x_101);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_22);
lean::cnstr_set(x_103, 1, x_102);
x_104 = l_Lean_Parser_command_structure;
x_105 = l_Lean_Parser_Syntax_mkNode(x_104, x_103);
return x_105;
}
}
lbl_56:
{
obj* x_106; 
x_106 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_106, 0, x_55);
if (lean::obj_tag(x_13) == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_107 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_38);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_106);
lean::cnstr_set(x_109, 1, x_108);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_54);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_32);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_27);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_39);
lean::cnstr_set(x_113, 1, x_112);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_22);
lean::cnstr_set(x_114, 1, x_113);
x_115 = l_Lean_Parser_command_structure;
x_116 = l_Lean_Parser_Syntax_mkNode(x_115, x_114);
return x_116;
}
else
{
obj* x_117; obj* x_120; obj* x_121; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_117 = lean::cnstr_get(x_13, 0);
lean::inc(x_117);
lean::dec(x_13);
x_120 = l_Lean_Parser_command_structureCtor_HasView;
x_121 = lean::cnstr_get(x_120, 1);
lean::inc(x_121);
lean::dec(x_120);
x_124 = lean::apply_1(x_121, x_117);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_37);
x_126 = l_Lean_Parser_Syntax_mkNode(x_35, x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_38);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_106);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_54);
lean::cnstr_set(x_129, 1, x_128);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_32);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_27);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_39);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_22);
lean::cnstr_set(x_133, 1, x_132);
x_134 = l_Lean_Parser_command_structure;
x_135 = l_Lean_Parser_Syntax_mkNode(x_134, x_133);
return x_135;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_command_structureFieldBlock_HasView;
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
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_structureCtor_HasView;
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
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_extends_HasView;
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
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_oldUnivParams_HasView;
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
obj* _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_0 = l_Lean_Parser_command_structureKw_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_8 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_6 = x_9;
goto lbl_7;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_12 = x_8;
} else {
 lean::inc(x_10);
 lean::dec(x_8);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_12);
x_17 = lean::box(0);
x_6 = x_17;
goto lbl_7;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_23; obj* x_24; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_23 = l_Lean_Parser_command_oldUnivParams_HasView;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_20);
if (lean::is_scalar(x_12)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_12;
}
lean::cnstr_set(x_28, 0, x_27);
x_6 = x_28;
goto lbl_7;
}
else
{
obj* x_32; 
lean::dec(x_12);
lean::dec(x_13);
lean::dec(x_18);
x_32 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_6 = x_32;
goto lbl_7;
}
}
}
lbl_7:
{
obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_45; 
x_33 = l_Lean_Parser_command_identUnivParams_HasView;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::apply_1(x_34, x_4);
x_38 = l_Lean_Parser_command_optDeclSig_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_4);
x_45 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4;
x_43 = x_46;
goto lbl_44;
}
else
{
obj* x_47; obj* x_49; obj* x_50; 
x_47 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_set(x_45, 0, lean::box(0));
 x_49 = x_45;
} else {
 lean::inc(x_47);
 lean::dec(x_45);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; 
lean::dec(x_49);
x_54 = lean::box(0);
x_43 = x_54;
goto lbl_44;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; obj* x_60; obj* x_61; obj* x_64; obj* x_65; 
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
x_60 = l_Lean_Parser_command_extends_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::apply_1(x_61, x_57);
if (lean::is_scalar(x_49)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_49;
}
lean::cnstr_set(x_65, 0, x_64);
x_43 = x_65;
goto lbl_44;
}
else
{
obj* x_69; 
lean::dec(x_50);
lean::dec(x_55);
lean::dec(x_49);
x_69 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4;
x_43 = x_69;
goto lbl_44;
}
}
}
lbl_44:
{
obj* x_70; obj* x_71; obj* x_73; 
x_70 = lean::box(0);
x_73 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; 
x_74 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_71 = x_74;
goto lbl_72;
}
else
{
obj* x_75; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_77 = x_73;
} else {
 lean::inc(x_75);
 lean::dec(x_73);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
if (lean::obj_tag(x_78) == 0)
{
lean::dec(x_77);
x_71 = x_70;
goto lbl_72;
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_78, 1);
lean::inc(x_82);
if (lean::obj_tag(x_82) == 0)
{
obj* x_84; obj* x_87; obj* x_88; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_78, 0);
lean::inc(x_84);
lean::dec(x_78);
x_87 = l_Lean_Parser_command_structureCtor_HasView;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
lean::dec(x_87);
x_91 = lean::apply_1(x_88, x_84);
if (lean::is_scalar(x_77)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_77;
}
lean::cnstr_set(x_92, 0, x_91);
x_71 = x_92;
goto lbl_72;
}
else
{
obj* x_96; 
lean::dec(x_77);
lean::dec(x_82);
lean::dec(x_78);
x_96 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_71 = x_96;
goto lbl_72;
}
}
}
lbl_72:
{
obj* x_97; 
x_97 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; 
x_98 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1;
x_99 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_99, 0, x_5);
lean::cnstr_set(x_99, 1, x_6);
lean::cnstr_set(x_99, 2, x_37);
lean::cnstr_set(x_99, 3, x_42);
lean::cnstr_set(x_99, 4, x_43);
lean::cnstr_set(x_99, 5, x_70);
lean::cnstr_set(x_99, 6, x_71);
lean::cnstr_set(x_99, 7, x_98);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_100 = lean::cnstr_get(x_97, 0);
lean::inc(x_100);
lean::dec(x_97);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2;
x_107 = l_List_map___main___rarg(x_106, x_103);
x_108 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_108, 0, x_5);
lean::cnstr_set(x_108, 1, x_6);
lean::cnstr_set(x_108, 2, x_37);
lean::cnstr_set(x_108, 3, x_42);
lean::cnstr_set(x_108, 4, x_43);
lean::cnstr_set(x_108, 5, x_70);
lean::cnstr_set(x_108, 6, x_71);
lean::cnstr_set(x_108, 7, x_107);
return x_108;
}
}
}
}
}
}
obj* l_Lean_Parser_command_structure_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6;
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
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_18 = l_Lean_Parser_command_structureKw_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_26; 
x_26 = lean::box(3);
x_23 = x_1;
x_24 = x_26;
goto lbl_25;
}
else
{
obj* x_27; obj* x_29; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_1, 1);
lean::inc(x_29);
lean::dec(x_1);
x_23 = x_29;
x_24 = x_27;
goto lbl_25;
}
lbl_25:
{
obj* x_32; obj* x_34; 
x_34 = l_Lean_Parser_Syntax_asNode___main(x_24);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; 
x_35 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_32 = x_35;
goto lbl_33;
}
else
{
obj* x_36; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_34, 0);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_set(x_34, 0, lean::box(0));
 x_38 = x_34;
} else {
 lean::inc(x_36);
 lean::dec(x_34);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; 
lean::dec(x_38);
x_43 = lean::box(0);
x_32 = x_43;
goto lbl_33;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_49; obj* x_50; obj* x_53; obj* x_54; 
x_46 = lean::cnstr_get(x_39, 0);
lean::inc(x_46);
lean::dec(x_39);
x_49 = l_Lean_Parser_command_oldUnivParams_HasView;
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
lean::dec(x_49);
x_53 = lean::apply_1(x_50, x_46);
if (lean::is_scalar(x_38)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_38;
}
lean::cnstr_set(x_54, 0, x_53);
x_32 = x_54;
goto lbl_33;
}
else
{
obj* x_58; 
lean::dec(x_44);
lean::dec(x_38);
lean::dec(x_39);
x_58 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_32 = x_58;
goto lbl_33;
}
}
}
lbl_33:
{
obj* x_59; obj* x_60; 
if (lean::obj_tag(x_23) == 0)
{
obj* x_62; 
x_62 = lean::box(3);
x_59 = x_23;
x_60 = x_62;
goto lbl_61;
}
else
{
obj* x_63; obj* x_65; 
x_63 = lean::cnstr_get(x_23, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_23, 1);
lean::inc(x_65);
lean::dec(x_23);
x_59 = x_65;
x_60 = x_63;
goto lbl_61;
}
lbl_61:
{
obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_74; 
x_68 = l_Lean_Parser_command_identUnivParams_HasView;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_60);
if (lean::obj_tag(x_59) == 0)
{
obj* x_76; 
x_76 = lean::box(3);
x_73 = x_59;
x_74 = x_76;
goto lbl_75;
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_59, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_59, 1);
lean::inc(x_79);
lean::dec(x_59);
x_73 = x_79;
x_74 = x_77;
goto lbl_75;
}
lbl_75:
{
obj* x_82; obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
x_82 = l_Lean_Parser_command_optDeclSig_HasView;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
lean::dec(x_82);
x_86 = lean::apply_1(x_83, x_74);
if (lean::obj_tag(x_73) == 0)
{
obj* x_90; 
x_90 = lean::box(3);
x_87 = x_73;
x_88 = x_90;
goto lbl_89;
}
else
{
obj* x_91; obj* x_93; 
x_91 = lean::cnstr_get(x_73, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_73, 1);
lean::inc(x_93);
lean::dec(x_73);
x_87 = x_93;
x_88 = x_91;
goto lbl_89;
}
lbl_89:
{
obj* x_96; obj* x_98; 
x_98 = l_Lean_Parser_Syntax_asNode___main(x_88);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; 
x_99 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4;
x_96 = x_99;
goto lbl_97;
}
else
{
obj* x_100; obj* x_102; obj* x_103; 
x_100 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_set(x_98, 0, lean::box(0));
 x_102 = x_98;
} else {
 lean::inc(x_100);
 lean::dec(x_98);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
if (lean::obj_tag(x_103) == 0)
{
obj* x_107; 
lean::dec(x_102);
x_107 = lean::box(0);
x_96 = x_107;
goto lbl_97;
}
else
{
obj* x_108; 
x_108 = lean::cnstr_get(x_103, 1);
lean::inc(x_108);
if (lean::obj_tag(x_108) == 0)
{
obj* x_110; obj* x_113; obj* x_114; obj* x_117; obj* x_118; 
x_110 = lean::cnstr_get(x_103, 0);
lean::inc(x_110);
lean::dec(x_103);
x_113 = l_Lean_Parser_command_extends_HasView;
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
lean::dec(x_113);
x_117 = lean::apply_1(x_114, x_110);
if (lean::is_scalar(x_102)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_102;
}
lean::cnstr_set(x_118, 0, x_117);
x_96 = x_118;
goto lbl_97;
}
else
{
obj* x_122; 
lean::dec(x_102);
lean::dec(x_108);
lean::dec(x_103);
x_122 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4;
x_96 = x_122;
goto lbl_97;
}
}
}
lbl_97:
{
obj* x_123; obj* x_124; 
if (lean::obj_tag(x_87) == 0)
{
obj* x_126; 
x_126 = lean::box(3);
x_123 = x_87;
x_124 = x_126;
goto lbl_125;
}
else
{
obj* x_127; obj* x_129; 
x_127 = lean::cnstr_get(x_87, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_87, 1);
lean::inc(x_129);
lean::dec(x_87);
x_123 = x_129;
x_124 = x_127;
goto lbl_125;
}
lbl_125:
{
obj* x_132; 
switch (lean::obj_tag(x_124)) {
case 0:
{
obj* x_134; obj* x_137; 
x_134 = lean::cnstr_get(x_124, 0);
lean::inc(x_134);
lean::dec(x_124);
x_137 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_137, 0, x_134);
x_132 = x_137;
goto lbl_133;
}
case 3:
{
obj* x_138; 
x_138 = lean::box(0);
x_132 = x_138;
goto lbl_133;
}
default:
{
obj* x_140; 
lean::dec(x_124);
x_140 = lean::box(0);
x_132 = x_140;
goto lbl_133;
}
}
lbl_133:
{
obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_147; 
if (lean::obj_tag(x_123) == 0)
{
obj* x_149; 
x_149 = lean::box(3);
x_146 = x_123;
x_147 = x_149;
goto lbl_148;
}
else
{
obj* x_150; obj* x_152; 
x_150 = lean::cnstr_get(x_123, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_123, 1);
lean::inc(x_152);
lean::dec(x_123);
x_146 = x_152;
x_147 = x_150;
goto lbl_148;
}
lbl_142:
{
obj* x_155; obj* x_156; 
x_155 = lean::box(3);
x_156 = l_Lean_Parser_Syntax_asNode___main(x_155);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; 
x_157 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1;
x_158 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_158, 0, x_22);
lean::cnstr_set(x_158, 1, x_32);
lean::cnstr_set(x_158, 2, x_72);
lean::cnstr_set(x_158, 3, x_86);
lean::cnstr_set(x_158, 4, x_96);
lean::cnstr_set(x_158, 5, x_132);
lean::cnstr_set(x_158, 6, x_141);
lean::cnstr_set(x_158, 7, x_157);
return x_158;
}
else
{
obj* x_159; obj* x_162; obj* x_165; obj* x_166; obj* x_167; 
x_159 = lean::cnstr_get(x_156, 0);
lean::inc(x_159);
lean::dec(x_156);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
x_165 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2;
x_166 = l_List_map___main___rarg(x_165, x_162);
x_167 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_167, 0, x_22);
lean::cnstr_set(x_167, 1, x_32);
lean::cnstr_set(x_167, 2, x_72);
lean::cnstr_set(x_167, 3, x_86);
lean::cnstr_set(x_167, 4, x_96);
lean::cnstr_set(x_167, 5, x_132);
lean::cnstr_set(x_167, 6, x_141);
lean::cnstr_set(x_167, 7, x_166);
return x_167;
}
}
lbl_145:
{
obj* x_168; 
x_168 = l_Lean_Parser_Syntax_asNode___main(x_144);
if (lean::obj_tag(x_168) == 0)
{
obj* x_169; obj* x_170; 
x_169 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1;
x_170 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_170, 0, x_22);
lean::cnstr_set(x_170, 1, x_32);
lean::cnstr_set(x_170, 2, x_72);
lean::cnstr_set(x_170, 3, x_86);
lean::cnstr_set(x_170, 4, x_96);
lean::cnstr_set(x_170, 5, x_132);
lean::cnstr_set(x_170, 6, x_143);
lean::cnstr_set(x_170, 7, x_169);
return x_170;
}
else
{
obj* x_171; obj* x_174; obj* x_177; obj* x_178; obj* x_179; 
x_171 = lean::cnstr_get(x_168, 0);
lean::inc(x_171);
lean::dec(x_168);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
lean::dec(x_171);
x_177 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2;
x_178 = l_List_map___main___rarg(x_177, x_174);
x_179 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_179, 0, x_22);
lean::cnstr_set(x_179, 1, x_32);
lean::cnstr_set(x_179, 2, x_72);
lean::cnstr_set(x_179, 3, x_86);
lean::cnstr_set(x_179, 4, x_96);
lean::cnstr_set(x_179, 5, x_132);
lean::cnstr_set(x_179, 6, x_143);
lean::cnstr_set(x_179, 7, x_178);
return x_179;
}
}
lbl_148:
{
obj* x_180; 
x_180 = l_Lean_Parser_Syntax_asNode___main(x_147);
if (lean::obj_tag(x_180) == 0)
{
if (lean::obj_tag(x_146) == 0)
{
obj* x_181; 
x_181 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_141 = x_181;
goto lbl_142;
}
else
{
obj* x_182; obj* x_185; 
x_182 = lean::cnstr_get(x_146, 0);
lean::inc(x_182);
lean::dec(x_146);
x_185 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_143 = x_185;
x_144 = x_182;
goto lbl_145;
}
}
else
{
obj* x_186; obj* x_188; obj* x_189; 
x_186 = lean::cnstr_get(x_180, 0);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_set(x_180, 0, lean::box(0));
 x_188 = x_180;
} else {
 lean::inc(x_186);
 lean::dec(x_180);
 x_188 = lean::box(0);
}
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
lean::dec(x_186);
if (lean::obj_tag(x_189) == 0)
{
obj* x_193; 
lean::dec(x_188);
x_193 = lean::box(0);
if (lean::obj_tag(x_146) == 0)
{
x_141 = x_193;
goto lbl_142;
}
else
{
obj* x_194; 
x_194 = lean::cnstr_get(x_146, 0);
lean::inc(x_194);
lean::dec(x_146);
x_143 = x_193;
x_144 = x_194;
goto lbl_145;
}
}
else
{
obj* x_197; 
x_197 = lean::cnstr_get(x_189, 1);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_199; obj* x_202; obj* x_203; obj* x_206; obj* x_207; 
x_199 = lean::cnstr_get(x_189, 0);
lean::inc(x_199);
lean::dec(x_189);
x_202 = l_Lean_Parser_command_structureCtor_HasView;
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
lean::dec(x_202);
x_206 = lean::apply_1(x_203, x_199);
if (lean::is_scalar(x_188)) {
 x_207 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_207 = x_188;
}
lean::cnstr_set(x_207, 0, x_206);
if (lean::obj_tag(x_146) == 0)
{
x_141 = x_207;
goto lbl_142;
}
else
{
obj* x_208; 
x_208 = lean::cnstr_get(x_146, 0);
lean::inc(x_208);
lean::dec(x_146);
x_143 = x_207;
x_144 = x_208;
goto lbl_145;
}
}
else
{
lean::dec(x_189);
lean::dec(x_197);
lean::dec(x_188);
if (lean::obj_tag(x_146) == 0)
{
obj* x_214; 
x_214 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_141 = x_214;
goto lbl_142;
}
else
{
obj* x_215; obj* x_218; 
x_215 = lean::cnstr_get(x_146, 0);
lean::inc(x_215);
lean::dec(x_146);
x_218 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3;
x_143 = x_218;
x_144 = x_215;
goto lbl_145;
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
}
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_structure_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_33; obj* x_35; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_68; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_83; obj* x_86; 
x_0 = lean::mk_string("structure");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string("class");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_7);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
x_13 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_13, x_7);
lean::dec(x_13);
x_17 = l_Lean_Parser_tokens___rarg(x_15);
lean::dec(x_15);
x_19 = l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
x_20 = l_Lean_Parser_tokens___rarg(x_19);
x_21 = lean::mk_string("extends");
x_22 = l_Lean_Parser_symbol_tokens___rarg(x_21, x_1);
lean::dec(x_21);
x_24 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_1);
x_25 = l_Lean_Parser_tokens___rarg(x_24);
lean::dec(x_24);
x_27 = lean::mk_string(",");
x_28 = l_Lean_Parser_symbol_tokens___rarg(x_27, x_1);
lean::dec(x_27);
x_30 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_25, x_28);
lean::dec(x_28);
lean::dec(x_25);
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_30, x_7);
lean::dec(x_30);
x_35 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_33);
lean::dec(x_33);
lean::dec(x_22);
x_38 = l_Lean_Parser_tokens___rarg(x_35);
lean::dec(x_35);
x_40 = l_Lean_Parser_tokens___rarg(x_38);
lean::dec(x_38);
x_42 = lean::mk_string(":=");
x_43 = l_Lean_Parser_symbol_tokens___rarg(x_42, x_1);
lean::dec(x_42);
x_45 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_46 = l_Lean_Parser_tokens___rarg(x_45);
x_47 = lean::mk_string("::");
x_48 = l_Lean_Parser_symbol_tokens___rarg(x_47, x_1);
lean::dec(x_47);
x_50 = l_Lean_Parser_List_cons_tokens___rarg(x_48, x_7);
lean::dec(x_48);
x_52 = l_Lean_Parser_List_cons_tokens___rarg(x_46, x_50);
lean::dec(x_50);
lean::dec(x_46);
x_55 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_52);
lean::dec(x_52);
x_57 = l_Lean_Parser_tokens___rarg(x_55);
lean::dec(x_55);
x_59 = l_Lean_Parser_tokens___rarg(x_57);
lean::dec(x_57);
x_61 = l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens;
x_62 = l_Lean_Parser_tokens___rarg(x_61);
x_63 = l_Lean_Parser_List_cons_tokens___rarg(x_62, x_7);
lean::dec(x_62);
x_65 = l_Lean_Parser_List_cons_tokens___rarg(x_59, x_63);
lean::dec(x_63);
lean::dec(x_59);
x_68 = l_Lean_Parser_List_cons_tokens___rarg(x_43, x_65);
lean::dec(x_65);
lean::dec(x_43);
x_71 = l_Lean_Parser_List_cons_tokens___rarg(x_40, x_68);
lean::dec(x_68);
lean::dec(x_40);
x_74 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_75 = l_Lean_Parser_List_cons_tokens___rarg(x_74, x_71);
lean::dec(x_71);
x_77 = l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
x_78 = l_Lean_Parser_List_cons_tokens___rarg(x_77, x_75);
lean::dec(x_75);
x_80 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_78);
lean::dec(x_78);
lean::dec(x_20);
x_83 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_80);
lean::dec(x_80);
lean::dec(x_17);
x_86 = l_Lean_Parser_tokens___rarg(x_83);
lean::dec(x_83);
return x_86;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("structure");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::mk_string("class");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_9);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_9);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_17);
x_22 = l_Lean_Parser_command_structureKw;
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_25 = 0;
x_26 = lean::box(x_25);
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_28, 0, x_24);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::mk_string("extends");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_33, 0, x_30);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_30);
lean::closure_set(x_34, 1, x_9);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_35, 0, x_9);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_36, 0, x_35);
x_37 = lean::mk_string(",");
x_38 = l_String_trim(x_37);
lean::dec(x_37);
lean::inc(x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_41, 0, x_38);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_42, 0, x_38);
lean::closure_set(x_42, 1, x_9);
lean::closure_set(x_42, 2, x_41);
x_43 = 1;
x_44 = lean::box(x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_45, 0, x_36);
lean::closure_set(x_45, 1, x_42);
lean::closure_set(x_45, 2, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_17);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_34);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_command_extends;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_49, 0, x_48);
lean::closure_set(x_49, 1, x_47);
lean::inc(x_26);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_51, 0, x_49);
lean::closure_set(x_51, 1, x_26);
x_52 = lean::mk_string(":=");
x_53 = l_String_trim(x_52);
lean::dec(x_52);
lean::inc(x_53);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_56, 0, x_53);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_57, 0, x_53);
lean::closure_set(x_57, 1, x_9);
lean::closure_set(x_57, 2, x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
lean::inc(x_26);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_60, 0, x_58);
lean::closure_set(x_60, 1, x_26);
x_61 = lean::mk_string("::");
x_62 = l_String_trim(x_61);
lean::dec(x_61);
lean::inc(x_62);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_65, 0, x_62);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_66, 0, x_62);
lean::closure_set(x_66, 1, x_9);
lean::closure_set(x_66, 2, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_17);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_60);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
x_71 = l_Lean_Parser_command_structureCtor;
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_72, 0, x_71);
lean::closure_set(x_72, 1, x_70);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_73, 0, x_72);
lean::closure_set(x_73, 1, x_26);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_Parser), 4, 0);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_17);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_57);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_51);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_28);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_23);
lean::cnstr_set(x_85, 1, x_84);
x_86 = l_Lean_Parser_command_structure;
x_87 = l_Lean_Parser_command_structure_HasView;
x_88 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_86, x_85, x_87);
lean::dec(x_85);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_88;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_0 = lean::mk_string("structure");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("class");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_5);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
x_18 = l_Lean_Parser_command_structureKw;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_21 = 0;
x_22 = lean::box(x_21);
lean::inc(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::mk_string("extends");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_31, 0, x_5);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = lean::mk_string(",");
x_34 = l_String_trim(x_33);
lean::dec(x_33);
lean::inc(x_34);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_37, 0, x_34);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_38, 0, x_34);
lean::closure_set(x_38, 1, x_5);
lean::closure_set(x_38, 2, x_37);
x_39 = 1;
x_40 = lean::box(x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_41, 0, x_32);
lean::closure_set(x_41, 1, x_38);
lean::closure_set(x_41, 2, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_13);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_30);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_Parser_command_extends;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_45, 0, x_44);
lean::closure_set(x_45, 1, x_43);
lean::inc(x_22);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_47, 0, x_45);
lean::closure_set(x_47, 1, x_22);
x_48 = lean::mk_string(":=");
x_49 = l_String_trim(x_48);
lean::dec(x_48);
lean::inc(x_49);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_52, 0, x_49);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_53, 0, x_49);
lean::closure_set(x_53, 1, x_5);
lean::closure_set(x_53, 2, x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
lean::inc(x_22);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_56, 0, x_54);
lean::closure_set(x_56, 1, x_22);
x_57 = lean::mk_string("::");
x_58 = l_String_trim(x_57);
lean::dec(x_57);
lean::inc(x_58);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_61, 0, x_58);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_62, 0, x_58);
lean::closure_set(x_62, 1, x_5);
lean::closure_set(x_62, 2, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_13);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_56);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
x_67 = l_Lean_Parser_command_structureCtor;
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_68, 0, x_67);
lean::closure_set(x_68, 1, x_66);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_69, 0, x_68);
lean::closure_set(x_69, 1, x_22);
x_70 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_Parser), 4, 0);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_71, 0, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_13);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_53);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_47);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_77);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_24);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_19);
lean::cnstr_set(x_81, 1, x_80);
return x_81;
}
}
obj* l_Lean_Parser_command_structure_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_structure;
x_5 = l_Lean_Parser_command_structure_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("defLike");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_defLike_kind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_defLike_kind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_defLike_kind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(3ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_defLike_kind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(4ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_defLike_kind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_defLike_kind;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
}
case 1:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_defLike_kind;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
}
case 2:
{
obj* x_30; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; 
x_33 = l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3;
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__4;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_1);
x_42 = l_Lean_Parser_command_defLike_kind;
x_43 = l_Lean_Parser_Syntax_mkNode(x_42, x_41);
return x_43;
}
}
case 3:
{
obj* x_44; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; 
x_47 = l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4;
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
lean::dec(x_44);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_1);
x_53 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__6;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_1);
x_56 = l_Lean_Parser_command_defLike_kind;
x_57 = l_Lean_Parser_Syntax_mkNode(x_56, x_55);
return x_57;
}
}
default:
{
obj* x_58; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
lean::dec(x_0);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; 
x_61 = l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5;
return x_61;
}
else
{
obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_58, 0);
lean::inc(x_62);
lean::dec(x_58);
x_65 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___elambda__1___closed__6;
x_68 = l_Lean_Parser_Syntax_mkNode(x_67, x_66);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_1);
x_70 = l_Lean_Parser_command_defLike_kind;
x_71 = l_Lean_Parser_Syntax_mkNode(x_70, x_69);
return x_71;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("defLike");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0ul);
x_60 = lean::nat_dec_eq(x_41, x_59);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::mk_nat_obj(1ul);
x_62 = lean::nat_dec_eq(x_41, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(2ul);
x_64 = lean::nat_dec_eq(x_41, x_63);
if (x_64 == 0)
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(3ul);
x_66 = lean::nat_dec_eq(x_41, x_65);
lean::dec(x_41);
if (x_66 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_68; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_56, 0);
lean::inc(x_68);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_26;
}
lean::cnstr_set(x_71, 0, x_68);
x_72 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
case 3:
{
obj* x_74; 
lean::dec(x_26);
x_74 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1;
return x_74;
}
default:
{
obj* x_77; 
lean::dec(x_56);
lean::dec(x_26);
x_77 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1;
return x_77;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_78; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_56, 0);
lean::inc(x_78);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_26;
}
lean::cnstr_set(x_81, 0, x_78);
x_82 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
case 3:
{
obj* x_84; 
lean::dec(x_26);
x_84 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2;
return x_84;
}
default:
{
obj* x_87; 
lean::dec(x_56);
lean::dec(x_26);
x_87 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2;
return x_87;
}
}
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_89; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_56, 0);
lean::inc(x_89);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_26;
}
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
case 3:
{
obj* x_95; 
lean::dec(x_26);
x_95 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3;
return x_95;
}
default:
{
obj* x_98; 
lean::dec(x_56);
lean::dec(x_26);
x_98 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3;
return x_98;
}
}
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_100; obj* x_103; obj* x_104; 
x_100 = lean::cnstr_get(x_56, 0);
lean::inc(x_100);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_26;
}
lean::cnstr_set(x_103, 0, x_100);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
case 3:
{
obj* x_106; 
lean::dec(x_26);
x_106 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4;
return x_106;
}
default:
{
obj* x_109; 
lean::dec(x_56);
lean::dec(x_26);
x_109 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4;
return x_109;
}
}
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_111; obj* x_114; obj* x_115; 
x_111 = lean::cnstr_get(x_56, 0);
lean::inc(x_111);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_114 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_114 = x_26;
}
lean::cnstr_set(x_114, 0, x_111);
x_115 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_115, 0, x_114);
return x_115;
}
case 3:
{
obj* x_117; 
lean::dec(x_26);
x_117 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5;
return x_117;
}
default:
{
obj* x_120; 
lean::dec(x_56);
lean::dec(x_26);
x_120 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5;
return x_120;
}
}
}
}
else
{
obj* x_125; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_125 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_125;
}
}
}
}
}
}
}
else
{
obj* x_128; 
lean::dec(x_8);
lean::dec(x_17);
x_128 = l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6;
return x_128;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_defLike_kind_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_defLike() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("defLike");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_defLike_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_Lean_Parser_command_defLike_kind_HasView;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_16 = lean::apply_1(x_13, x_1);
x_17 = l_Lean_Parser_command_identUnivParams_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_5);
x_22 = l_Lean_Parser_command_optDeclSig_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_7);
x_27 = l_Lean_Parser_command_declVal_HasView;
x_28 = lean::cnstr_get(x_27, 1);
lean::inc(x_28);
lean::dec(x_27);
x_31 = lean::apply_1(x_28, x_9);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_26);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_34);
if (lean::obj_tag(x_3) == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_16);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_command_defLike;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_41 = lean::cnstr_get(x_3, 0);
lean::inc(x_41);
lean::dec(x_3);
x_44 = l_Lean_Parser_command_oldUnivParams_HasView;
x_45 = lean::cnstr_get(x_44, 1);
lean::inc(x_45);
lean::dec(x_44);
x_48 = lean::apply_1(x_45, x_41);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_32);
x_50 = l_Lean_Parser_noKind;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_35);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_16);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_Lean_Parser_command_defLike;
x_55 = l_Lean_Parser_Syntax_mkNode(x_54, x_53);
return x_55;
}
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_identUnivParams_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_declVal_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_defLike_kind_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_8 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_9 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_10 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_9);
lean::cnstr_set(x_11, 4, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_14 = x_6;
} else {
 lean::inc(x_12);
 lean::dec(x_6);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_14);
x_19 = lean::box(0);
x_20 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_21 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_22 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_23 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_20);
lean::cnstr_set(x_23, 3, x_21);
lean::cnstr_set(x_23, 4, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
lean::dec(x_15);
x_29 = l_Lean_Parser_command_oldUnivParams_HasView;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
lean::dec(x_29);
x_33 = lean::apply_1(x_30, x_26);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
x_35 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_36 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_37 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_38 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_38, 0, x_5);
lean::cnstr_set(x_38, 1, x_34);
lean::cnstr_set(x_38, 2, x_35);
lean::cnstr_set(x_38, 3, x_36);
lean::cnstr_set(x_38, 4, x_37);
return x_38;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_14);
lean::dec(x_15);
lean::dec(x_24);
x_42 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_43 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_44 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_45 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_46 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_42);
lean::cnstr_set(x_46, 2, x_43);
lean::cnstr_set(x_46, 3, x_44);
lean::cnstr_set(x_46, 4, x_45);
return x_46;
}
}
}
}
}
obj* l_Lean_Parser_command_defLike_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3;
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
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
x_18 = l_Lean_Parser_command_defLike_kind_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_30; 
x_30 = lean::box(3);
x_27 = x_1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
lean::dec(x_1);
x_27 = x_33;
x_28 = x_31;
goto lbl_29;
}
lbl_26:
{
obj* x_36; obj* x_37; obj* x_40; 
x_36 = l_Lean_Parser_command_identUnivParams_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_42 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_43 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_23);
lean::cnstr_set(x_43, 2, x_40);
lean::cnstr_set(x_43, 3, x_41);
lean::cnstr_set(x_43, 4, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_53; 
x_44 = lean::cnstr_get(x_25, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_25, 1);
lean::inc(x_46);
lean::dec(x_25);
x_49 = l_Lean_Parser_command_optDeclSig_HasView;
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
lean::dec(x_49);
x_53 = lean::apply_1(x_50, x_44);
if (lean::obj_tag(x_46) == 0)
{
obj* x_54; obj* x_55; 
x_54 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_55 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_55, 0, x_22);
lean::cnstr_set(x_55, 1, x_23);
lean::cnstr_set(x_55, 2, x_40);
lean::cnstr_set(x_55, 3, x_53);
lean::cnstr_set(x_55, 4, x_54);
return x_55;
}
else
{
obj* x_56; obj* x_59; obj* x_60; obj* x_63; obj* x_64; 
x_56 = lean::cnstr_get(x_46, 0);
lean::inc(x_56);
lean::dec(x_46);
x_59 = l_Lean_Parser_command_declVal_HasView;
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
lean::dec(x_59);
x_63 = lean::apply_1(x_60, x_56);
x_64 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_64, 0, x_22);
lean::cnstr_set(x_64, 1, x_23);
lean::cnstr_set(x_64, 2, x_40);
lean::cnstr_set(x_64, 3, x_53);
lean::cnstr_set(x_64, 4, x_63);
return x_64;
}
}
}
lbl_29:
{
obj* x_65; 
x_65 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_65) == 0)
{
if (lean::obj_tag(x_27) == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_67 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_68 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_69 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_70 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_70, 0, x_22);
lean::cnstr_set(x_70, 1, x_66);
lean::cnstr_set(x_70, 2, x_67);
lean::cnstr_set(x_70, 3, x_68);
lean::cnstr_set(x_70, 4, x_69);
return x_70;
}
else
{
obj* x_71; obj* x_73; obj* x_76; 
x_71 = lean::cnstr_get(x_27, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_27, 1);
lean::inc(x_73);
lean::dec(x_27);
x_76 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_23 = x_76;
x_24 = x_71;
x_25 = x_73;
goto lbl_26;
}
}
else
{
obj* x_77; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_set(x_65, 0, lean::box(0));
 x_79 = x_65;
} else {
 lean::inc(x_77);
 lean::dec(x_65);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
lean::dec(x_77);
if (lean::obj_tag(x_80) == 0)
{
obj* x_84; 
lean::dec(x_79);
x_84 = lean::box(0);
if (lean::obj_tag(x_27) == 0)
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_85 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_86 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_87 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_88 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_88, 0, x_22);
lean::cnstr_set(x_88, 1, x_84);
lean::cnstr_set(x_88, 2, x_85);
lean::cnstr_set(x_88, 3, x_86);
lean::cnstr_set(x_88, 4, x_87);
return x_88;
}
else
{
obj* x_89; obj* x_91; 
x_89 = lean::cnstr_get(x_27, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_27, 1);
lean::inc(x_91);
lean::dec(x_27);
x_23 = x_84;
x_24 = x_89;
x_25 = x_91;
goto lbl_26;
}
}
else
{
obj* x_94; 
x_94 = lean::cnstr_get(x_80, 1);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_96; obj* x_99; obj* x_100; obj* x_103; obj* x_104; 
x_96 = lean::cnstr_get(x_80, 0);
lean::inc(x_96);
lean::dec(x_80);
x_99 = l_Lean_Parser_command_oldUnivParams_HasView;
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
lean::dec(x_99);
x_103 = lean::apply_1(x_100, x_96);
if (lean::is_scalar(x_79)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_79;
}
lean::cnstr_set(x_104, 0, x_103);
if (lean::obj_tag(x_27) == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_106 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_107 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_108 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_108, 0, x_22);
lean::cnstr_set(x_108, 1, x_104);
lean::cnstr_set(x_108, 2, x_105);
lean::cnstr_set(x_108, 3, x_106);
lean::cnstr_set(x_108, 4, x_107);
return x_108;
}
else
{
obj* x_109; obj* x_111; 
x_109 = lean::cnstr_get(x_27, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_27, 1);
lean::inc(x_111);
lean::dec(x_27);
x_23 = x_104;
x_24 = x_109;
x_25 = x_111;
goto lbl_26;
}
}
else
{
lean::dec(x_80);
lean::dec(x_79);
lean::dec(x_94);
if (lean::obj_tag(x_27) == 0)
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_117 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_118 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_119 = l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2;
x_120 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_121 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_121, 0, x_22);
lean::cnstr_set(x_121, 1, x_117);
lean::cnstr_set(x_121, 2, x_118);
lean::cnstr_set(x_121, 3, x_119);
lean::cnstr_set(x_121, 4, x_120);
return x_121;
}
else
{
obj* x_122; obj* x_124; obj* x_127; 
x_122 = lean::cnstr_get(x_27, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_27, 1);
lean::inc(x_124);
lean::dec(x_27);
x_127 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_23 = x_127;
x_24 = x_122;
x_25 = x_124;
goto lbl_26;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_defLike_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_instance() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("instance");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_instance_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_Lean_Parser_command_declSig_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::apply_1(x_11, x_5);
x_15 = l_Lean_Parser_command_declVal_HasView;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_7);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_command_instance;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
x_32 = l_Lean_Parser_command_identUnivParams_HasView;
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::apply_1(x_33, x_29);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_20);
x_38 = l_Lean_Parser_noKind;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_22);
x_41 = lean::box(3);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_Lean_Parser_command_instance;
x_44 = l_Lean_Parser_Syntax_mkNode(x_43, x_42);
return x_44;
}
}
else
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_1, 0);
lean::inc(x_45);
lean::dec(x_1);
x_48 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_48, 0, x_45);
if (lean::obj_tag(x_3) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_49 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_22);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_Lean_Parser_command_instance;
x_53 = l_Lean_Parser_Syntax_mkNode(x_52, x_51);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_54 = lean::cnstr_get(x_3, 0);
lean::inc(x_54);
lean::dec(x_3);
x_57 = l_Lean_Parser_command_identUnivParams_HasView;
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
lean::dec(x_57);
x_61 = lean::apply_1(x_58, x_54);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_20);
x_63 = l_Lean_Parser_noKind;
x_64 = l_Lean_Parser_Syntax_mkNode(x_63, x_62);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_22);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_48);
lean::cnstr_set(x_66, 1, x_65);
x_67 = l_Lean_Parser_command_instance;
x_68 = l_Lean_Parser_Syntax_mkNode(x_67, x_66);
return x_68;
}
}
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_identUnivParams_HasView;
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
obj* _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_declSig_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_4 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_5 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_4);
lean::cnstr_set(x_6, 3, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_9);
x_14 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_15 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_0);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
lean::dec(x_10);
x_22 = l_Lean_Parser_command_identUnivParams_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_19);
if (lean::is_scalar(x_9)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_9;
}
lean::cnstr_set(x_27, 0, x_26);
x_28 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_29 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_28);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_9);
lean::dec(x_17);
lean::dec(x_10);
x_34 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_35 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_36 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_0);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set(x_37, 2, x_35);
lean::cnstr_set(x_37, 3, x_36);
return x_37;
}
}
}
}
}
obj* l_Lean_Parser_command_instance_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_34; 
x_34 = lean::box(3);
x_31 = x_1;
x_32 = x_34;
goto lbl_33;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
lean::dec(x_1);
x_31 = x_37;
x_32 = x_35;
goto lbl_33;
}
lbl_30:
{
obj* x_40; obj* x_41; obj* x_44; 
x_40 = l_Lean_Parser_command_declSig_HasView;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
lean::dec(x_40);
x_44 = lean::apply_1(x_41, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_45; obj* x_46; 
x_45 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_18);
lean::cnstr_set(x_46, 1, x_27);
lean::cnstr_set(x_46, 2, x_44);
lean::cnstr_set(x_46, 3, x_45);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_51; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_29, 0);
lean::inc(x_47);
lean::dec(x_29);
x_50 = l_Lean_Parser_command_declVal_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_47);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_18);
lean::cnstr_set(x_55, 1, x_27);
lean::cnstr_set(x_55, 2, x_44);
lean::cnstr_set(x_55, 3, x_54);
return x_55;
}
}
lbl_33:
{
obj* x_56; 
x_56 = l_Lean_Parser_Syntax_asNode___main(x_32);
if (lean::obj_tag(x_56) == 0)
{
if (lean::obj_tag(x_31) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_58 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_59 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_18);
lean::cnstr_set(x_60, 1, x_57);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_59);
return x_60;
}
else
{
obj* x_61; obj* x_63; obj* x_66; 
x_61 = lean::cnstr_get(x_31, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_31, 1);
lean::inc(x_63);
lean::dec(x_31);
x_66 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_27 = x_66;
x_28 = x_61;
x_29 = x_63;
goto lbl_30;
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 x_69 = x_56;
} else {
 lean::inc(x_67);
 lean::dec(x_56);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_74; 
lean::dec(x_69);
x_74 = lean::box(0);
if (lean::obj_tag(x_31) == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_76 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_18);
lean::cnstr_set(x_77, 1, x_74);
lean::cnstr_set(x_77, 2, x_75);
lean::cnstr_set(x_77, 3, x_76);
return x_77;
}
else
{
obj* x_78; obj* x_80; 
x_78 = lean::cnstr_get(x_31, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_31, 1);
lean::inc(x_80);
lean::dec(x_31);
x_27 = x_74;
x_28 = x_78;
x_29 = x_80;
goto lbl_30;
}
}
else
{
obj* x_83; 
x_83 = lean::cnstr_get(x_70, 1);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_85; obj* x_88; obj* x_89; obj* x_92; obj* x_93; 
x_85 = lean::cnstr_get(x_70, 0);
lean::inc(x_85);
lean::dec(x_70);
x_88 = l_Lean_Parser_command_identUnivParams_HasView;
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
lean::dec(x_88);
x_92 = lean::apply_1(x_89, x_85);
if (lean::is_scalar(x_69)) {
 x_93 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_93 = x_69;
}
lean::cnstr_set(x_93, 0, x_92);
if (lean::obj_tag(x_31) == 0)
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_95 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_18);
lean::cnstr_set(x_96, 1, x_93);
lean::cnstr_set(x_96, 2, x_94);
lean::cnstr_set(x_96, 3, x_95);
return x_96;
}
else
{
obj* x_97; obj* x_99; 
x_97 = lean::cnstr_get(x_31, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_31, 1);
lean::inc(x_99);
lean::dec(x_31);
x_27 = x_93;
x_28 = x_97;
x_29 = x_99;
goto lbl_30;
}
}
else
{
lean::dec(x_69);
lean::dec(x_70);
lean::dec(x_83);
if (lean::obj_tag(x_31) == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_106 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_107 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_18);
lean::cnstr_set(x_108, 1, x_105);
lean::cnstr_set(x_108, 2, x_106);
lean::cnstr_set(x_108, 3, x_107);
return x_108;
}
else
{
obj* x_109; obj* x_111; obj* x_114; 
x_109 = lean::cnstr_get(x_31, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_31, 1);
lean::inc(x_111);
lean::dec(x_31);
x_114 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1;
x_27 = x_114;
x_28 = x_109;
x_29 = x_111;
goto lbl_30;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instance_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instance_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_instance_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_instance_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_example() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("example");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_example_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_declSig_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_3);
x_13 = l_Lean_Parser_command_declVal_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::apply_1(x_14, x_5);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_19);
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::box(3);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_command_example;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
lean::dec(x_1);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_20);
x_30 = l_Lean_Parser_command_example;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
return x_31;
}
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_command_declSig_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_2, x_5);
x_7 = l_Lean_Parser_command_declVal_HasView;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::apply_1(x_8, x_5);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_6);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_command_example_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_Lean_Parser_command_declSig_HasView;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
x_27 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_33; obj* x_36; obj* x_37; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
x_32 = l_Lean_Parser_command_declVal_HasView;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::apply_1(x_33, x_29);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_26);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_38; obj* x_41; 
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
lean::dec(x_6);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
if (lean::obj_tag(x_5) == 0)
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_43 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
else
{
obj* x_45; obj* x_47; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_5, 1);
lean::inc(x_47);
lean::dec(x_5);
x_1 = x_41;
x_2 = x_45;
x_3 = x_47;
goto lbl_4;
}
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_50; 
x_50 = l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1;
return x_50;
}
else
{
obj* x_51; obj* x_53; obj* x_56; 
x_51 = lean::cnstr_get(x_5, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_5, 1);
lean::inc(x_53);
lean::dec(x_5);
x_56 = lean::box(0);
x_1 = x_56;
x_2 = x_51;
x_3 = x_53;
goto lbl_4;
}
}
default:
{
lean::dec(x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_58; 
x_58 = l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1;
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_64; 
x_59 = lean::cnstr_get(x_5, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_5, 1);
lean::inc(x_61);
lean::dec(x_5);
x_64 = lean::box(0);
x_1 = x_64;
x_2 = x_59;
x_3 = x_61;
goto lbl_4;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_example_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_example_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_example_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_example_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("constantKeyword");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_Lean_Parser_Syntax_mkNode(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_command_constantKeyword;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
x_11 = l_Lean_Parser_command_constantKeyword;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("constantKeyword");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_42; uint8 x_43; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_39, x_42);
lean::dec(x_39);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_26);
lean::dec(x_36);
x_47 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_49; 
lean::dec(x_26);
x_49 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_36, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; 
x_52 = lean::cnstr_get(x_36, 0);
lean::inc(x_52);
lean::dec(x_36);
switch (lean::obj_tag(x_52)) {
case 0:
{
obj* x_55; obj* x_58; 
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
lean::dec(x_52);
if (lean::is_scalar(x_26)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_26;
}
lean::cnstr_set(x_58, 0, x_55);
return x_58;
}
case 3:
{
obj* x_60; 
lean::dec(x_26);
x_60 = lean::box(0);
return x_60;
}
default:
{
obj* x_63; 
lean::dec(x_26);
lean::dec(x_52);
x_63 = lean::box(0);
return x_63;
}
}
}
else
{
obj* x_67; 
lean::dec(x_50);
lean::dec(x_26);
lean::dec(x_36);
x_67 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_67;
}
}
}
}
}
}
}
else
{
obj* x_70; 
lean::dec(x_8);
lean::dec(x_17);
x_70 = l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1;
return x_70;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_constantKeyword_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_axiom() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("axiom");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_axiom_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_command_constantKeyword_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_1);
x_13 = l_Lean_Parser_command_identUnivParams_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::apply_1(x_14, x_3);
x_18 = l_Lean_Parser_command_declSig_HasView;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_5);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_17);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_12);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_axiom;
x_28 = l_Lean_Parser_Syntax_mkNode(x_27, x_26);
return x_28;
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_0 = l_Lean_Parser_command_constantKeyword_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_command_identUnivParams_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_4);
x_11 = l_Lean_Parser_command_declSig_HasView;
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::apply_1(x_12, x_4);
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
return x_16;
}
}
obj* l_Lean_Parser_command_axiom_HasView_x_27___elambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_19; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
lean::dec(x_6);
x_15 = l_Lean_Parser_command_constantKeyword_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1;
x_21 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_32; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
x_28 = l_Lean_Parser_command_identUnivParams_HasView;
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
lean::dec(x_28);
x_32 = lean::apply_1(x_29, x_23);
if (lean::obj_tag(x_25) == 0)
{
obj* x_33; obj* x_34; 
x_33 = l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2;
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_19);
lean::cnstr_set(x_34, 1, x_32);
lean::cnstr_set(x_34, 2, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_42; obj* x_43; 
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
lean::dec(x_25);
x_38 = l_Lean_Parser_command_declSig_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_35);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_19);
lean::cnstr_set(x_43, 1, x_32);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_axiom_HasView_x_27___elambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_axiom_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_axiom_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_inductive() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inductive");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_introRule_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_command_inductive_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_command_identUnivParams_HasView;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_21 = lean::apply_1(x_18, x_7);
x_22 = l_Lean_Parser_command_optDeclSig_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_26 = lean::apply_1(x_23, x_9);
x_27 = l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1;
x_28 = l_List_map___main___rarg(x_27, x_13);
x_29 = l_Lean_Parser_noKind;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_16);
if (lean::obj_tag(x_1) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_32 = x_34;
goto lbl_33;
}
else
{
obj* x_35; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
lean::dec(x_1);
if (lean::obj_tag(x_35) == 0)
{
obj* x_38; 
x_38 = l_Lean_Parser_command_notation_HasView_x_27___elambda__1___closed__1;
x_32 = x_38;
goto lbl_33;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_35, 0);
lean::inc(x_39);
lean::dec(x_35);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_16);
x_44 = l_Lean_Parser_Syntax_mkNode(x_29, x_43);
x_32 = x_44;
goto lbl_33;
}
}
lbl_33:
{
obj* x_45; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_47; 
x_47 = lean::box(3);
x_45 = x_47;
goto lbl_46;
}
else
{
obj* x_48; obj* x_51; 
x_48 = lean::cnstr_get(x_3, 0);
lean::inc(x_48);
lean::dec(x_3);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_48);
x_45 = x_51;
goto lbl_46;
}
lbl_46:
{
obj* x_52; obj* x_53; obj* x_54; 
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_45);
lean::cnstr_set(x_52, 1, x_16);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_32);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_Lean_Parser_Syntax_mkNode(x_29, x_53);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_55 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_31);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_26);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_21);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_59);
x_61 = l_Lean_Parser_command_inductive;
x_62 = l_Lean_Parser_Syntax_mkNode(x_61, x_60);
return x_62;
}
else
{
obj* x_63; obj* x_66; obj* x_67; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_63 = lean::cnstr_get(x_11, 0);
lean::inc(x_63);
lean::dec(x_11);
x_66 = l_Lean_Parser_command_notationLike_HasView;
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
lean::dec(x_66);
x_70 = lean::apply_1(x_67, x_63);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_16);
x_72 = l_Lean_Parser_Syntax_mkNode(x_29, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_31);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_26);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_21);
lean::cnstr_set(x_75, 1, x_74);
x_76 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_54);
lean::cnstr_set(x_78, 1, x_77);
x_79 = l_Lean_Parser_command_inductive;
x_80 = l_Lean_Parser_Syntax_mkNode(x_79, x_78);
return x_80;
}
}
else
{
obj* x_81; obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; 
x_81 = lean::cnstr_get(x_5, 0);
lean::inc(x_81);
lean::dec(x_5);
x_84 = l_Lean_Parser_command_oldUnivParams_HasView;
x_85 = lean::cnstr_get(x_84, 1);
lean::inc(x_85);
lean::dec(x_84);
x_88 = lean::apply_1(x_85, x_81);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_16);
x_90 = l_Lean_Parser_Syntax_mkNode(x_29, x_89);
if (lean::obj_tag(x_11) == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_91 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_31);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_26);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_21);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_90);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_54);
lean::cnstr_set(x_96, 1, x_95);
x_97 = l_Lean_Parser_command_inductive;
x_98 = l_Lean_Parser_Syntax_mkNode(x_97, x_96);
return x_98;
}
else
{
obj* x_99; obj* x_102; obj* x_103; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_99 = lean::cnstr_get(x_11, 0);
lean::inc(x_99);
lean::dec(x_11);
x_102 = l_Lean_Parser_command_notationLike_HasView;
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
lean::dec(x_102);
x_106 = lean::apply_1(x_103, x_99);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_16);
x_108 = l_Lean_Parser_Syntax_mkNode(x_29, x_107);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_31);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_26);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_21);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_90);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_54);
lean::cnstr_set(x_113, 1, x_112);
x_114 = l_Lean_Parser_command_inductive;
x_115 = l_Lean_Parser_Syntax_mkNode(x_114, x_113);
return x_115;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_Lean_Parser_command_introRule_HasView;
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
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_command_introRule_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_notationLike_HasView;
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
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_4;
goto lbl_1;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::box(0);
x_0 = x_12;
goto lbl_1;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_0 = x_22;
goto lbl_1;
}
case 3:
{
obj* x_24; 
lean::dec(x_7);
x_24 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_24;
goto lbl_1;
}
default:
{
obj* x_27; 
lean::dec(x_7);
lean::dec(x_15);
x_27 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_27;
goto lbl_1;
}
}
}
else
{
obj* x_31; 
lean::dec(x_13);
lean::dec(x_8);
lean::dec(x_7);
x_31 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_0 = x_31;
goto lbl_1;
}
}
}
lbl_1:
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
x_32 = lean::box(0);
x_35 = lean::box(3);
x_36 = l_Lean_Parser_Syntax_asNode___main(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_33 = x_37;
goto lbl_34;
}
else
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_40 = x_36;
} else {
 lean::inc(x_38);
 lean::dec(x_36);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_40);
x_33 = x_32;
goto lbl_34;
}
else
{
obj* x_45; 
x_45 = lean::cnstr_get(x_41, 1);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_50; obj* x_51; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
lean::dec(x_41);
x_50 = l_Lean_Parser_command_oldUnivParams_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_47);
if (lean::is_scalar(x_40)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_40;
}
lean::cnstr_set(x_55, 0, x_54);
x_33 = x_55;
goto lbl_34;
}
else
{
obj* x_59; 
lean::dec(x_45);
lean::dec(x_40);
lean::dec(x_41);
x_59 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_33 = x_59;
goto lbl_34;
}
}
}
lbl_34:
{
obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_70; obj* x_71; obj* x_73; 
x_60 = l_Lean_Parser_command_identUnivParams_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::box(3);
x_65 = lean::apply_1(x_61, x_64);
x_66 = l_Lean_Parser_command_optDeclSig_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
lean::dec(x_66);
x_70 = lean::apply_1(x_67, x_64);
x_73 = l_Lean_Parser_Syntax_asNode___main(x_64);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; 
x_74 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_71 = x_74;
goto lbl_72;
}
else
{
obj* x_75; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_set(x_73, 0, lean::box(0));
 x_77 = x_73;
} else {
 lean::inc(x_75);
 lean::dec(x_73);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
if (lean::obj_tag(x_78) == 0)
{
lean::dec(x_77);
x_71 = x_32;
goto lbl_72;
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_78, 1);
lean::inc(x_82);
if (lean::obj_tag(x_82) == 0)
{
obj* x_84; obj* x_87; obj* x_88; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_78, 0);
lean::inc(x_84);
lean::dec(x_78);
x_87 = l_Lean_Parser_command_notationLike_HasView;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
lean::dec(x_87);
x_91 = lean::apply_1(x_88, x_84);
if (lean::is_scalar(x_77)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_77;
}
lean::cnstr_set(x_92, 0, x_91);
x_71 = x_92;
goto lbl_72;
}
else
{
obj* x_96; 
lean::dec(x_77);
lean::dec(x_82);
lean::dec(x_78);
x_96 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_71 = x_96;
goto lbl_72;
}
}
}
lbl_72:
{
obj* x_97; 
x_97 = l_Lean_Parser_Syntax_asNode___main(x_64);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; 
x_98 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1;
x_99 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_99, 0, x_0);
lean::cnstr_set(x_99, 1, x_32);
lean::cnstr_set(x_99, 2, x_33);
lean::cnstr_set(x_99, 3, x_65);
lean::cnstr_set(x_99, 4, x_70);
lean::cnstr_set(x_99, 5, x_71);
lean::cnstr_set(x_99, 6, x_98);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
x_100 = lean::cnstr_get(x_97, 0);
lean::inc(x_100);
lean::dec(x_97);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2;
x_107 = l_List_map___main___rarg(x_106, x_103);
x_108 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_108, 0, x_0);
lean::cnstr_set(x_108, 1, x_32);
lean::cnstr_set(x_108, 2, x_33);
lean::cnstr_set(x_108, 3, x_65);
lean::cnstr_set(x_108, 4, x_70);
lean::cnstr_set(x_108, 5, x_71);
lean::cnstr_set(x_108, 6, x_107);
return x_108;
}
}
}
}
}
}
obj* l_Lean_Parser_command_inductive_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4;
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
obj* x_13; obj* x_15; obj* x_18; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::dec(x_9);
x_18 = l_Lean_Parser_Syntax_asNode___main(x_13);
if (lean::obj_tag(x_18) == 0)
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; 
x_19 = lean::box(3);
x_1 = x_15;
x_2 = x_19;
goto lbl_3;
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::dec(x_15);
x_1 = x_22;
x_2 = x_20;
goto lbl_3;
}
}
else
{
obj* x_25; obj* x_28; obj* x_31; 
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
lean::dec(x_18);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_List_append___rarg(x_28, x_15);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = lean::box(3);
x_1 = x_31;
x_2 = x_32;
goto lbl_3;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_31, 1);
lean::inc(x_35);
lean::dec(x_31);
x_1 = x_35;
x_2 = x_33;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_38; obj* x_40; 
x_40 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; 
x_41 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_38 = x_41;
goto lbl_39;
}
else
{
obj* x_42; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 x_44 = x_40;
} else {
 lean::inc(x_42);
 lean::dec(x_40);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_49; 
lean::dec(x_44);
x_49 = lean::box(0);
x_38 = x_49;
goto lbl_39;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; 
x_52 = lean::cnstr_get(x_45, 0);
lean::inc(x_52);
lean::dec(x_45);
switch (lean::obj_tag(x_52)) {
case 0:
{
obj* x_55; obj* x_58; obj* x_59; 
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
lean::dec(x_52);
if (lean::is_scalar(x_44)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_44;
}
lean::cnstr_set(x_58, 0, x_55);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_38 = x_59;
goto lbl_39;
}
case 3:
{
obj* x_61; 
lean::dec(x_44);
x_61 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_38 = x_61;
goto lbl_39;
}
default:
{
obj* x_64; 
lean::dec(x_44);
lean::dec(x_52);
x_64 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_38 = x_64;
goto lbl_39;
}
}
}
else
{
obj* x_68; 
lean::dec(x_44);
lean::dec(x_50);
lean::dec(x_45);
x_68 = l_Lean_Parser_command_notation_HasView_x_27___lambda__1___closed__1;
x_38 = x_68;
goto lbl_39;
}
}
}
lbl_39:
{
obj* x_69; obj* x_70; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_72; 
x_72 = lean::box(3);
x_69 = x_1;
x_70 = x_72;
goto lbl_71;
}
else
{
obj* x_73; obj* x_75; 
x_73 = lean::cnstr_get(x_1, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_1, 1);
lean::inc(x_75);
lean::dec(x_1);
x_69 = x_75;
x_70 = x_73;
goto lbl_71;
}
lbl_71:
{
obj* x_78; 
switch (lean::obj_tag(x_70)) {
case 0:
{
obj* x_80; obj* x_83; 
x_80 = lean::cnstr_get(x_70, 0);
lean::inc(x_80);
lean::dec(x_70);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_80);
x_78 = x_83;
goto lbl_79;
}
case 3:
{
obj* x_84; 
x_84 = lean::box(0);
x_78 = x_84;
goto lbl_79;
}
default:
{
obj* x_86; 
lean::dec(x_70);
x_86 = lean::box(0);
x_78 = x_86;
goto lbl_79;
}
}
lbl_79:
{
obj* x_87; obj* x_88; 
if (lean::obj_tag(x_69) == 0)
{
obj* x_90; 
x_90 = lean::box(3);
x_87 = x_69;
x_88 = x_90;
goto lbl_89;
}
else
{
obj* x_91; obj* x_93; 
x_91 = lean::cnstr_get(x_69, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_69, 1);
lean::inc(x_93);
lean::dec(x_69);
x_87 = x_93;
x_88 = x_91;
goto lbl_89;
}
lbl_89:
{
obj* x_96; obj* x_98; 
x_98 = l_Lean_Parser_Syntax_asNode___main(x_88);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; 
x_99 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_96 = x_99;
goto lbl_97;
}
else
{
obj* x_100; obj* x_102; obj* x_103; 
x_100 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_set(x_98, 0, lean::box(0));
 x_102 = x_98;
} else {
 lean::inc(x_100);
 lean::dec(x_98);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
if (lean::obj_tag(x_103) == 0)
{
obj* x_107; 
lean::dec(x_102);
x_107 = lean::box(0);
x_96 = x_107;
goto lbl_97;
}
else
{
obj* x_108; 
x_108 = lean::cnstr_get(x_103, 1);
lean::inc(x_108);
if (lean::obj_tag(x_108) == 0)
{
obj* x_110; obj* x_113; obj* x_114; obj* x_117; obj* x_118; 
x_110 = lean::cnstr_get(x_103, 0);
lean::inc(x_110);
lean::dec(x_103);
x_113 = l_Lean_Parser_command_oldUnivParams_HasView;
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
lean::dec(x_113);
x_117 = lean::apply_1(x_114, x_110);
if (lean::is_scalar(x_102)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_102;
}
lean::cnstr_set(x_118, 0, x_117);
x_96 = x_118;
goto lbl_97;
}
else
{
obj* x_122; 
lean::dec(x_108);
lean::dec(x_103);
lean::dec(x_102);
x_122 = l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5;
x_96 = x_122;
goto lbl_97;
}
}
}
lbl_97:
{
obj* x_123; obj* x_124; 
if (lean::obj_tag(x_87) == 0)
{
obj* x_126; 
x_126 = lean::box(3);
x_123 = x_87;
x_124 = x_126;
goto lbl_125;
}
else
{
obj* x_127; obj* x_129; 
x_127 = lean::cnstr_get(x_87, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_87, 1);
lean::inc(x_129);
lean::dec(x_87);
x_123 = x_129;
x_124 = x_127;
goto lbl_125;
}
lbl_125:
{
obj* x_132; obj* x_133; obj* x_136; obj* x_137; obj* x_138; 
x_132 = l_Lean_Parser_command_identUnivParams_HasView;
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
lean::dec(x_132);
x_136 = lean::apply_1(x_133, x_124);
if (lean::obj_tag(x_123) == 0)
{
obj* x_140; 
x_140 = lean::box(3);
x_137 = x_123;
x_138 = x_140;
goto lbl_139;
}
else
{
obj* x_141; obj* x_143; 
x_141 = lean::cnstr_get(x_123, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_123, 1);
lean::inc(x_143);
lean::dec(x_123);
x_137 = x_143;
x_138 = x_141;
goto lbl_139;
}
lbl_139:
{
obj* x_146; obj* x_147; obj* x_150; obj* x_151; obj* x_153; obj* x_154; obj* x_156; obj* x_157; 
x_146 = l_Lean_Parser_command_optDeclSig_HasView;
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
lean::dec(x_146);
x_150 = lean::apply_1(x_147, x_138);
if (lean::obj_tag(x_137) == 0)
{
obj* x_159; 
x_159 = lean::box(3);
x_156 = x_137;
x_157 = x_159;
goto lbl_158;
}
else
{
obj* x_160; obj* x_162; 
x_160 = lean::cnstr_get(x_137, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_137, 1);
lean::inc(x_162);
lean::dec(x_137);
x_156 = x_162;
x_157 = x_160;
goto lbl_158;
}
lbl_152:
{
obj* x_165; obj* x_166; 
x_165 = lean::box(3);
x_166 = l_Lean_Parser_Syntax_asNode___main(x_165);
if (lean::obj_tag(x_166) == 0)
{
obj* x_167; obj* x_168; 
x_167 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1;
x_168 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_168, 0, x_38);
lean::cnstr_set(x_168, 1, x_78);
lean::cnstr_set(x_168, 2, x_96);
lean::cnstr_set(x_168, 3, x_136);
lean::cnstr_set(x_168, 4, x_150);
lean::cnstr_set(x_168, 5, x_151);
lean::cnstr_set(x_168, 6, x_167);
return x_168;
}
else
{
obj* x_169; obj* x_172; obj* x_175; obj* x_176; obj* x_177; 
x_169 = lean::cnstr_get(x_166, 0);
lean::inc(x_169);
lean::dec(x_166);
x_172 = lean::cnstr_get(x_169, 1);
lean::inc(x_172);
lean::dec(x_169);
x_175 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2;
x_176 = l_List_map___main___rarg(x_175, x_172);
x_177 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_177, 0, x_38);
lean::cnstr_set(x_177, 1, x_78);
lean::cnstr_set(x_177, 2, x_96);
lean::cnstr_set(x_177, 3, x_136);
lean::cnstr_set(x_177, 4, x_150);
lean::cnstr_set(x_177, 5, x_151);
lean::cnstr_set(x_177, 6, x_176);
return x_177;
}
}
lbl_155:
{
obj* x_178; 
x_178 = l_Lean_Parser_Syntax_asNode___main(x_154);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_180; 
x_179 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1;
x_180 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_180, 0, x_38);
lean::cnstr_set(x_180, 1, x_78);
lean::cnstr_set(x_180, 2, x_96);
lean::cnstr_set(x_180, 3, x_136);
lean::cnstr_set(x_180, 4, x_150);
lean::cnstr_set(x_180, 5, x_153);
lean::cnstr_set(x_180, 6, x_179);
return x_180;
}
else
{
obj* x_181; obj* x_184; obj* x_187; obj* x_188; obj* x_189; 
x_181 = lean::cnstr_get(x_178, 0);
lean::inc(x_181);
lean::dec(x_178);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
lean::dec(x_181);
x_187 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2;
x_188 = l_List_map___main___rarg(x_187, x_184);
x_189 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_189, 0, x_38);
lean::cnstr_set(x_189, 1, x_78);
lean::cnstr_set(x_189, 2, x_96);
lean::cnstr_set(x_189, 3, x_136);
lean::cnstr_set(x_189, 4, x_150);
lean::cnstr_set(x_189, 5, x_153);
lean::cnstr_set(x_189, 6, x_188);
return x_189;
}
}
lbl_158:
{
obj* x_190; 
x_190 = l_Lean_Parser_Syntax_asNode___main(x_157);
if (lean::obj_tag(x_190) == 0)
{
if (lean::obj_tag(x_156) == 0)
{
obj* x_191; 
x_191 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_151 = x_191;
goto lbl_152;
}
else
{
obj* x_192; obj* x_195; 
x_192 = lean::cnstr_get(x_156, 0);
lean::inc(x_192);
lean::dec(x_156);
x_195 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_153 = x_195;
x_154 = x_192;
goto lbl_155;
}
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
if (lean::obj_tag(x_199) == 0)
{
obj* x_203; 
lean::dec(x_198);
x_203 = lean::box(0);
if (lean::obj_tag(x_156) == 0)
{
x_151 = x_203;
goto lbl_152;
}
else
{
obj* x_204; 
x_204 = lean::cnstr_get(x_156, 0);
lean::inc(x_204);
lean::dec(x_156);
x_153 = x_203;
x_154 = x_204;
goto lbl_155;
}
}
else
{
obj* x_207; 
x_207 = lean::cnstr_get(x_199, 1);
lean::inc(x_207);
if (lean::obj_tag(x_207) == 0)
{
obj* x_209; obj* x_212; obj* x_213; obj* x_216; obj* x_217; 
x_209 = lean::cnstr_get(x_199, 0);
lean::inc(x_209);
lean::dec(x_199);
x_212 = l_Lean_Parser_command_notationLike_HasView;
x_213 = lean::cnstr_get(x_212, 0);
lean::inc(x_213);
lean::dec(x_212);
x_216 = lean::apply_1(x_213, x_209);
if (lean::is_scalar(x_198)) {
 x_217 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_217 = x_198;
}
lean::cnstr_set(x_217, 0, x_216);
if (lean::obj_tag(x_156) == 0)
{
x_151 = x_217;
goto lbl_152;
}
else
{
obj* x_218; 
x_218 = lean::cnstr_get(x_156, 0);
lean::inc(x_218);
lean::dec(x_156);
x_153 = x_217;
x_154 = x_218;
goto lbl_155;
}
}
else
{
lean::dec(x_207);
lean::dec(x_199);
lean::dec(x_198);
if (lean::obj_tag(x_156) == 0)
{
obj* x_224; 
x_224 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_151 = x_224;
goto lbl_152;
}
else
{
obj* x_225; obj* x_228; 
x_225 = lean::cnstr_get(x_156, 0);
lean::inc(x_225);
lean::dec(x_156);
x_228 = l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3;
x_153 = x_228;
x_154 = x_225;
goto lbl_155;
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
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inductive_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inductive_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_inductive_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("inner");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_command_defLike_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_command_declaration_inner;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_Lean_Parser_command_instance_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x_27___elambda__1___closed__3;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_Lean_Parser_command_declaration_inner;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
case 2:
{
obj* x_30; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_Parser_command_example_HasView;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::apply_1(x_34, x_30);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__4;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_1);
x_42 = l_Lean_Parser_command_declaration_inner;
x_43 = l_Lean_Parser_Syntax_mkNode(x_42, x_41);
return x_43;
}
case 3:
{
obj* x_44; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l_Lean_Parser_command_axiom_HasView;
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::apply_1(x_48, x_44);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_1);
x_53 = l_Lean_Parser_number_HasView_x_27___elambda__1___closed__6;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_1);
x_56 = l_Lean_Parser_command_declaration_inner;
x_57 = l_Lean_Parser_Syntax_mkNode(x_56, x_55);
return x_57;
}
case 4:
{
obj* x_58; obj* x_61; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
lean::dec(x_0);
x_61 = l_Lean_Parser_command_inductive_HasView;
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
lean::dec(x_61);
x_65 = lean::apply_1(x_62, x_58);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_Lean_Parser_command_mixfix_kind_HasView_x_27___elambda__1___closed__6;
x_68 = l_Lean_Parser_Syntax_mkNode(x_67, x_66);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_1);
x_70 = l_Lean_Parser_command_declaration_inner;
x_71 = l_Lean_Parser_Syntax_mkNode(x_70, x_69);
return x_71;
}
default:
{
obj* x_72; obj* x_75; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
lean::dec(x_0);
x_75 = l_Lean_Parser_command_structure_HasView;
x_76 = lean::cnstr_get(x_75, 1);
lean::inc(x_76);
lean::dec(x_75);
x_79 = lean::apply_1(x_76, x_72);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_1);
x_81 = l_Lean_Parser_Level_leading_HasView_x_27___elambda__1___closed__3;
x_82 = l_Lean_Parser_Syntax_mkNode(x_81, x_80);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_1);
x_84 = l_Lean_Parser_command_declaration_inner;
x_85 = l_Lean_Parser_Syntax_mkNode(x_84, x_83);
return x_85;
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_command_defLike_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string("inner");
x_10 = lean_name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; 
lean::dec(x_24);
x_30 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_30;
}
case 1:
{
obj* x_33; 
lean::dec(x_27);
lean::dec(x_24);
x_33 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_33;
}
default:
{
obj* x_34; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
lean::dec(x_24);
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean_name_dec_eq(x_37, x_42);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_47; 
lean::dec(x_34);
lean::dec(x_39);
x_47 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_47;
}
else
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_49; 
lean::dec(x_39);
x_49 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_34, 0);
lean::inc(x_52);
lean::dec(x_34);
x_55 = lean::mk_nat_obj(0ul);
x_56 = lean::nat_dec_eq(x_39, x_55);
if (x_56 == 0)
{
obj* x_57; uint8 x_58; 
x_57 = lean::mk_nat_obj(1ul);
x_58 = lean::nat_dec_eq(x_39, x_57);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; 
x_59 = lean::mk_nat_obj(2ul);
x_60 = lean::nat_dec_eq(x_39, x_59);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::mk_nat_obj(3ul);
x_62 = lean::nat_dec_eq(x_39, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(4ul);
x_64 = lean::nat_dec_eq(x_39, x_63);
lean::dec(x_39);
if (x_64 == 0)
{
obj* x_66; obj* x_67; obj* x_70; obj* x_71; 
x_66 = l_Lean_Parser_command_structure_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
lean::dec(x_66);
x_70 = lean::apply_1(x_67, x_52);
x_71 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_76; obj* x_77; 
x_72 = l_Lean_Parser_command_inductive_HasView;
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
lean::dec(x_72);
x_76 = lean::apply_1(x_73, x_52);
x_77 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
else
{
obj* x_79; obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_39);
x_79 = l_Lean_Parser_command_axiom_HasView;
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
lean::dec(x_79);
x_83 = lean::apply_1(x_80, x_52);
x_84 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
}
else
{
obj* x_86; obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_39);
x_86 = l_Lean_Parser_command_example_HasView;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_90 = lean::apply_1(x_87, x_52);
x_91 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
}
else
{
obj* x_93; obj* x_94; obj* x_97; obj* x_98; 
lean::dec(x_39);
x_93 = l_Lean_Parser_command_instance_HasView;
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
lean::dec(x_93);
x_97 = lean::apply_1(x_94, x_52);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
return x_98;
}
}
else
{
obj* x_100; obj* x_101; obj* x_104; obj* x_105; 
lean::dec(x_39);
x_100 = l_Lean_Parser_command_defLike_HasView;
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
lean::dec(x_100);
x_104 = lean::apply_1(x_101, x_52);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
else
{
obj* x_109; 
lean::dec(x_50);
lean::dec(x_34);
lean::dec(x_39);
x_109 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_109;
}
}
}
}
}
}
}
else
{
obj* x_112; 
lean::dec(x_8);
lean::dec(x_17);
x_112 = l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1;
return x_112;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_inner_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declaration_inner_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declaration() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_command_declModifiers_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_1);
x_11 = l_Lean_Parser_command_declaration_inner_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::apply_1(x_12, x_3);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_command_declaration;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_0 = l_Lean_Parser_command_declModifiers_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_command_declaration_inner_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_4);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_Lean_Parser_command_declaration_inner_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_command_declaration_HasView_x_27___elambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_19; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
lean::dec(x_6);
x_15 = l_Lean_Parser_command_declModifiers_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = lean::apply_1(x_16, x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
lean::dec(x_12);
x_25 = l_Lean_Parser_command_declaration_inner_HasView;
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_29 = lean::apply_1(x_26, x_22);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_HasView_x_27___elambda__2), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_HasView_x_27___elambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_command_declaration_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_119; obj* x_122; obj* x_124; obj* x_126; obj* x_129; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_139; obj* x_142; obj* x_145; obj* x_148; obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; 
x_0 = lean::mk_string("def");
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
x_4 = lean::mk_string("abbreviation");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_1);
lean::dec(x_4);
x_7 = lean::mk_string("abbrev");
x_8 = l_Lean_Parser_symbol_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_10 = lean::mk_string("theorem");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_1);
lean::dec(x_10);
x_13 = lean::mk_string("constant");
x_14 = l_Lean_Parser_symbol_tokens___rarg(x_13, x_1);
lean::dec(x_13);
x_16 = lean::box(0);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_16);
lean::dec(x_14);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_8, x_19);
lean::dec(x_19);
lean::dec(x_8);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_25);
lean::dec(x_25);
lean::dec(x_2);
x_31 = l_Lean_Parser_tokens___rarg(x_28);
lean::dec(x_28);
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_31, x_16);
lean::dec(x_31);
x_35 = l_Lean_Parser_tokens___rarg(x_33);
lean::dec(x_33);
x_37 = l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
x_38 = l_Lean_Parser_tokens___rarg(x_37);
x_39 = l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens;
x_40 = l_Lean_Parser_List_cons_tokens___rarg(x_39, x_16);
x_41 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_42 = l_Lean_Parser_List_cons_tokens___rarg(x_41, x_40);
x_43 = l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
x_44 = l_Lean_Parser_List_cons_tokens___rarg(x_43, x_42);
lean::dec(x_42);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_38, x_44);
lean::dec(x_44);
x_48 = l_Lean_Parser_List_cons_tokens___rarg(x_35, x_46);
lean::dec(x_46);
lean::dec(x_35);
x_51 = l_Lean_Parser_tokens___rarg(x_48);
lean::dec(x_48);
x_53 = lean::mk_string("instance");
x_54 = l_Lean_Parser_symbol_tokens___rarg(x_53, x_1);
lean::dec(x_53);
x_56 = l_Lean_Parser_tokens___rarg(x_43);
x_57 = l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens;
x_58 = l_Lean_Parser_List_cons_tokens___rarg(x_57, x_40);
lean::dec(x_40);
x_60 = l_Lean_Parser_List_cons_tokens___rarg(x_56, x_58);
lean::dec(x_56);
x_62 = l_Lean_Parser_List_cons_tokens___rarg(x_54, x_60);
lean::dec(x_60);
lean::dec(x_54);
x_65 = l_Lean_Parser_tokens___rarg(x_62);
lean::dec(x_62);
x_67 = lean::mk_string("example");
x_68 = l_Lean_Parser_symbol_tokens___rarg(x_67, x_1);
lean::dec(x_67);
x_70 = l_Lean_Parser_List_cons_tokens___rarg(x_68, x_58);
lean::dec(x_58);
lean::dec(x_68);
x_73 = l_Lean_Parser_tokens___rarg(x_70);
lean::dec(x_70);
x_75 = lean::mk_string("axiom");
x_76 = l_Lean_Parser_symbol_tokens___rarg(x_75, x_1);
lean::dec(x_75);
x_78 = l_Lean_Parser_List_cons_tokens___rarg(x_76, x_16);
lean::dec(x_76);
x_80 = l_Lean_Parser_tokens___rarg(x_78);
lean::dec(x_78);
x_82 = l_Lean_Parser_List_cons_tokens___rarg(x_80, x_16);
lean::dec(x_80);
x_84 = l_Lean_Parser_tokens___rarg(x_82);
lean::dec(x_82);
x_86 = l_Lean_Parser_List_cons_tokens___rarg(x_57, x_16);
x_87 = l_Lean_Parser_List_cons_tokens___rarg(x_43, x_86);
lean::dec(x_86);
x_89 = l_Lean_Parser_List_cons_tokens___rarg(x_84, x_87);
lean::dec(x_87);
lean::dec(x_84);
x_92 = l_Lean_Parser_tokens___rarg(x_89);
lean::dec(x_89);
x_94 = lean::mk_string("class");
x_95 = l_Lean_Parser_symbol_tokens___rarg(x_94, x_1);
lean::dec(x_94);
x_97 = l_Lean_Parser_tokens___rarg(x_95);
lean::dec(x_95);
x_99 = lean::mk_string("inductive");
x_100 = l_Lean_Parser_symbol_tokens___rarg(x_99, x_1);
lean::dec(x_99);
x_102 = l_Lean_Parser_List_cons_tokens___rarg(x_100, x_16);
lean::dec(x_100);
x_104 = l_Lean_Parser_List_cons_tokens___rarg(x_97, x_102);
lean::dec(x_102);
lean::dec(x_97);
x_107 = l_Lean_Parser_tokens___rarg(x_104);
lean::dec(x_104);
x_109 = l_Lean_Parser_tokens___rarg(x_107);
lean::dec(x_107);
x_111 = l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
x_112 = l_Lean_Parser_tokens___rarg(x_111);
x_113 = l_Lean_Parser_tokens___rarg(x_112);
lean::dec(x_112);
x_115 = l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens;
x_116 = l_Lean_Parser_tokens___rarg(x_115);
x_117 = l_Lean_Parser_List_cons_tokens___rarg(x_116, x_16);
lean::dec(x_116);
x_119 = l_Lean_Parser_List_cons_tokens___rarg(x_113, x_117);
lean::dec(x_117);
lean::dec(x_113);
x_122 = l_Lean_Parser_List_cons_tokens___rarg(x_41, x_119);
lean::dec(x_119);
x_124 = l_Lean_Parser_List_cons_tokens___rarg(x_43, x_122);
lean::dec(x_122);
x_126 = l_Lean_Parser_List_cons_tokens___rarg(x_38, x_124);
lean::dec(x_124);
lean::dec(x_38);
x_129 = l_Lean_Parser_List_cons_tokens___rarg(x_109, x_126);
lean::dec(x_126);
lean::dec(x_109);
x_132 = l_Lean_Parser_tokens___rarg(x_129);
lean::dec(x_129);
x_134 = l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens;
x_135 = l_Lean_Parser_List_cons_tokens___rarg(x_134, x_16);
x_136 = l_Lean_Parser_List_cons_tokens___rarg(x_132, x_135);
lean::dec(x_135);
lean::dec(x_132);
x_139 = l_Lean_Parser_List_cons_tokens___rarg(x_92, x_136);
lean::dec(x_136);
lean::dec(x_92);
x_142 = l_Lean_Parser_List_cons_tokens___rarg(x_73, x_139);
lean::dec(x_139);
lean::dec(x_73);
x_145 = l_Lean_Parser_List_cons_tokens___rarg(x_65, x_142);
lean::dec(x_142);
lean::dec(x_65);
x_148 = l_Lean_Parser_List_cons_tokens___rarg(x_51, x_145);
lean::dec(x_145);
lean::dec(x_51);
x_151 = l_Lean_Parser_tokens___rarg(x_148);
lean::dec(x_148);
x_153 = l_Lean_Parser_List_cons_tokens___rarg(x_151, x_16);
lean::dec(x_151);
x_155 = l_Lean_Parser_tokens___rarg(x_153);
lean::dec(x_153);
x_157 = l_Lean_Parser_List_cons_tokens___rarg(x_155, x_16);
lean::dec(x_155);
x_159 = l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens;
x_160 = l_Lean_Parser_List_cons_tokens___rarg(x_159, x_157);
lean::dec(x_157);
x_162 = l_Lean_Parser_tokens___rarg(x_160);
lean::dec(x_160);
return x_162;
}
}
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = l_Lean_Parser_noKind;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_7);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_111; obj* x_112; obj* x_114; obj* x_115; obj* x_116; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_0 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_1 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_4 = lean::mk_string("def");
x_5 = l_String_trim(x_4);
lean::dec(x_4);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_8);
x_11 = lean::mk_string("abbreviation");
x_12 = l_String_trim(x_11);
lean::dec(x_11);
lean::inc(x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_12);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_9);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::mk_string("abbrev");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_21, 0, x_18);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_9);
lean::closure_set(x_22, 2, x_21);
x_23 = lean::mk_string("theorem");
x_24 = l_String_trim(x_23);
lean::dec(x_23);
lean::inc(x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_27, 0, x_24);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_28, 0, x_24);
lean::closure_set(x_28, 1, x_9);
lean::closure_set(x_28, 2, x_27);
x_29 = lean::mk_string("constant");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_33, 0, x_30);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_30);
lean::closure_set(x_34, 1, x_9);
lean::closure_set(x_34, 2, x_33);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_22);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_16);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_10);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_9);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
x_43 = l_Lean_Parser_command_defLike_kind;
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_44, 0, x_43);
lean::closure_set(x_44, 1, x_42);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_46 = 0;
x_47 = lean::box(x_46);
lean::inc(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_49, 0, x_45);
lean::closure_set(x_49, 1, x_47);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_Parser), 4, 0);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_35);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
lean::inc(x_51);
lean::inc(x_52);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_51);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
lean::inc(x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_55);
lean::inc(x_49);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_49);
lean::cnstr_set(x_60, 1, x_58);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_44);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_Lean_Parser_command_defLike;
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_63, 0, x_62);
lean::closure_set(x_63, 1, x_61);
x_64 = lean::mk_string("instance");
x_65 = l_String_trim(x_64);
lean::dec(x_64);
lean::inc(x_65);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_68, 0, x_65);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_69, 0, x_65);
lean::closure_set(x_69, 1, x_9);
lean::closure_set(x_69, 2, x_68);
lean::inc(x_47);
lean::inc(x_56);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_72, 0, x_56);
lean::closure_set(x_72, 1, x_47);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_Parser), 4, 0);
lean::inc(x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_51);
lean::inc(x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_72);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_69);
lean::cnstr_set(x_78, 1, x_77);
x_79 = l_Lean_Parser_command_instance;
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_80, 0, x_79);
lean::closure_set(x_80, 1, x_78);
x_81 = lean::mk_string("example");
x_82 = l_String_trim(x_81);
lean::dec(x_81);
lean::inc(x_82);
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_85, 0, x_82);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_86, 0, x_82);
lean::closure_set(x_86, 1, x_9);
lean::closure_set(x_86, 2, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_75);
x_88 = l_Lean_Parser_command_example;
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_89, 0, x_88);
lean::closure_set(x_89, 1, x_87);
x_90 = lean::mk_string("axiom");
x_91 = l_String_trim(x_90);
lean::dec(x_90);
lean::inc(x_91);
x_94 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_94, 0, x_91);
x_95 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_95, 0, x_91);
lean::closure_set(x_95, 1, x_9);
lean::closure_set(x_95, 2, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_35);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_97, 0, x_96);
lean::closure_set(x_97, 1, x_9);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_35);
x_99 = l_Lean_Parser_command_constantKeyword;
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_100, 0, x_99);
lean::closure_set(x_100, 1, x_98);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_73);
lean::cnstr_set(x_101, 1, x_35);
lean::inc(x_56);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_56);
lean::cnstr_set(x_103, 1, x_101);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set(x_104, 1, x_103);
x_105 = l_Lean_Parser_command_axiom;
x_106 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_106, 0, x_105);
lean::closure_set(x_106, 1, x_104);
x_107 = lean::mk_string("class");
x_108 = l_String_trim(x_107);
lean::dec(x_107);
lean::inc(x_108);
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_111, 0, x_108);
x_112 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_112, 0, x_108);
lean::closure_set(x_112, 1, x_9);
lean::closure_set(x_112, 2, x_111);
lean::inc(x_47);
x_114 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_114, 0, x_112);
lean::closure_set(x_114, 1, x_47);
x_115 = lean::mk_string("inductive");
x_116 = l_String_trim(x_115);
lean::dec(x_115);
lean::inc(x_116);
x_119 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_119, 0, x_116);
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_120, 0, x_116);
lean::closure_set(x_120, 1, x_9);
lean::closure_set(x_120, 2, x_119);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_35);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_114);
lean::cnstr_set(x_122, 1, x_121);
x_123 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_123, 0, x_122);
x_124 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_125 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_125, 0, x_124);
x_126 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_126, 0, x_125);
lean::closure_set(x_126, 1, x_47);
x_127 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_Parser), 4, 0);
x_128 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_128, 0, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_35);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_56);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_49);
lean::cnstr_set(x_133, 1, x_132);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_123);
lean::cnstr_set(x_134, 1, x_133);
x_135 = l_Lean_Parser_command_inductive;
x_136 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_136, 0, x_135);
lean::closure_set(x_136, 1, x_134);
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_Parser), 4, 0);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_35);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set(x_139, 1, x_138);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_106);
lean::cnstr_set(x_140, 1, x_139);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_89);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_80);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_63);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_144, 0, x_143);
lean::closure_set(x_144, 1, x_9);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_35);
x_146 = l_Lean_Parser_command_declaration_inner;
x_147 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_147, 0, x_146);
lean::closure_set(x_147, 1, x_145);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_35);
x_149 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_Parser), 4, 0);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_148);
x_151 = l_Lean_Parser_command_declaration;
x_152 = l_Lean_Parser_command_declaration_HasView;
x_153 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_151, x_150, x_152);
lean::dec(x_150);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
return x_153;
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; uint8 x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_0 = lean::mk_string("def");
x_1 = l_String_trim(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_4);
x_7 = lean::mk_string("abbreviation");
x_8 = l_String_trim(x_7);
lean::dec(x_7);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_5);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::mk_string("abbrev");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_17, 0, x_14);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_5);
lean::closure_set(x_18, 2, x_17);
x_19 = lean::mk_string("theorem");
x_20 = l_String_trim(x_19);
lean::dec(x_19);
lean::inc(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_23, 0, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_5);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::mk_string("constant");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_29, 0, x_26);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_5);
lean::closure_set(x_30, 2, x_29);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_18);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_5);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
x_39 = l_Lean_Parser_command_defLike_kind;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_40, 0, x_39);
lean::closure_set(x_40, 1, x_38);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_42 = 0;
x_43 = lean::box(x_42);
lean::inc(x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_45, 0, x_41);
lean::closure_set(x_45, 1, x_43);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_Parser), 4, 0);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_31);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
lean::inc(x_47);
lean::inc(x_48);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_47);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
lean::inc(x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_51);
lean::inc(x_45);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_45);
lean::cnstr_set(x_56, 1, x_54);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_40);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_Lean_Parser_command_defLike;
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_59, 0, x_58);
lean::closure_set(x_59, 1, x_57);
x_60 = lean::mk_string("instance");
x_61 = l_String_trim(x_60);
lean::dec(x_60);
lean::inc(x_61);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_64, 0, x_61);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_65, 0, x_61);
lean::closure_set(x_65, 1, x_5);
lean::closure_set(x_65, 2, x_64);
lean::inc(x_43);
lean::inc(x_52);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_68, 0, x_52);
lean::closure_set(x_68, 1, x_43);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_Parser), 4, 0);
lean::inc(x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_47);
lean::inc(x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_68);
lean::cnstr_set(x_73, 1, x_71);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_65);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_Lean_Parser_command_instance;
x_76 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_76, 0, x_75);
lean::closure_set(x_76, 1, x_74);
x_77 = lean::mk_string("example");
x_78 = l_String_trim(x_77);
lean::dec(x_77);
lean::inc(x_78);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_81, 0, x_78);
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_82, 0, x_78);
lean::closure_set(x_82, 1, x_5);
lean::closure_set(x_82, 2, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_71);
x_84 = l_Lean_Parser_command_example;
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_85, 0, x_84);
lean::closure_set(x_85, 1, x_83);
x_86 = lean::mk_string("axiom");
x_87 = l_String_trim(x_86);
lean::dec(x_86);
lean::inc(x_87);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_90, 0, x_87);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_91, 0, x_87);
lean::closure_set(x_91, 1, x_5);
lean::closure_set(x_91, 2, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_31);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_93, 0, x_92);
lean::closure_set(x_93, 1, x_5);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_31);
x_95 = l_Lean_Parser_command_constantKeyword;
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_96, 0, x_95);
lean::closure_set(x_96, 1, x_94);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_69);
lean::cnstr_set(x_97, 1, x_31);
lean::inc(x_52);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_52);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_99);
x_101 = l_Lean_Parser_command_axiom;
x_102 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_102, 0, x_101);
lean::closure_set(x_102, 1, x_100);
x_103 = lean::mk_string("class");
x_104 = l_String_trim(x_103);
lean::dec(x_103);
lean::inc(x_104);
x_107 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_107, 0, x_104);
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_108, 0, x_104);
lean::closure_set(x_108, 1, x_5);
lean::closure_set(x_108, 2, x_107);
lean::inc(x_43);
x_110 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_110, 0, x_108);
lean::closure_set(x_110, 1, x_43);
x_111 = lean::mk_string("inductive");
x_112 = l_String_trim(x_111);
lean::dec(x_111);
lean::inc(x_112);
x_115 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_115, 0, x_112);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_116, 0, x_112);
lean::closure_set(x_116, 1, x_5);
lean::closure_set(x_116, 2, x_115);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_31);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_110);
lean::cnstr_set(x_118, 1, x_117);
x_119 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_119, 0, x_118);
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_121 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_121, 0, x_120);
x_122 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_122, 0, x_121);
lean::closure_set(x_122, 1, x_43);
x_123 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_Parser), 4, 0);
x_124 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_124, 0, x_123);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_31);
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set(x_126, 1, x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_48);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_52);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_45);
lean::cnstr_set(x_129, 1, x_128);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_119);
lean::cnstr_set(x_130, 1, x_129);
x_131 = l_Lean_Parser_command_inductive;
x_132 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_132, 0, x_131);
lean::closure_set(x_132, 1, x_130);
x_133 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_Parser), 4, 0);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_31);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_132);
lean::cnstr_set(x_135, 1, x_134);
x_136 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_136, 0, x_102);
lean::cnstr_set(x_136, 1, x_135);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_85);
lean::cnstr_set(x_137, 1, x_136);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_76);
lean::cnstr_set(x_138, 1, x_137);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_59);
lean::cnstr_set(x_139, 1, x_138);
x_140 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_140, 0, x_139);
lean::closure_set(x_140, 1, x_5);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_31);
x_142 = l_Lean_Parser_command_declaration_inner;
x_143 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_143, 0, x_142);
lean::closure_set(x_143, 1, x_141);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_31);
x_145 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_Parser), 4, 0);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_144);
return x_146;
}
}
obj* l_Lean_Parser_command_declaration_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_command_declaration;
x_5 = l_Lean_Parser_command_declaration_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* initialize_init_lean_parser_term(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_declaration(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_term(w);
if (io_result_is_error(w)) return w;
 l_Lean_Parser_command_docComment = _init_l_Lean_Parser_command_docComment();
lean::mark_persistent(l_Lean_Parser_command_docComment);
 l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_docComment_HasView_x_27 = _init_l_Lean_Parser_command_docComment_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x_27);
 l_Lean_Parser_command_docComment_HasView = _init_l_Lean_Parser_command_docComment_HasView();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView);
 l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_docComment_Parser___closed__1 = _init_l_Lean_Parser_command_docComment_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_docComment_Parser___closed__1);
 l_Lean_Parser_command_attrInstance = _init_l_Lean_Parser_command_attrInstance();
lean::mark_persistent(l_Lean_Parser_command_attrInstance);
 l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_attrInstance_HasView_x_27 = _init_l_Lean_Parser_command_attrInstance_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x_27);
 l_Lean_Parser_command_attrInstance_HasView = _init_l_Lean_Parser_command_attrInstance_HasView();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView);
 l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_attrInstance_Parser___closed__1 = _init_l_Lean_Parser_command_attrInstance_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_Parser___closed__1);
 l_Lean_Parser_command_declAttributes = _init_l_Lean_Parser_command_declAttributes();
lean::mark_persistent(l_Lean_Parser_command_declAttributes);
 l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_declAttributes_HasView_x_27 = _init_l_Lean_Parser_command_declAttributes_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x_27);
 l_Lean_Parser_command_declAttributes_HasView = _init_l_Lean_Parser_command_declAttributes_HasView();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView);
 l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_declAttributes_Parser___closed__1 = _init_l_Lean_Parser_command_declAttributes_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_Parser___closed__1);
 l_Lean_Parser_command_visibility = _init_l_Lean_Parser_command_visibility();
lean::mark_persistent(l_Lean_Parser_command_visibility);
 l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2 = _init_l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___elambda__1___closed__2);
 l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_visibility_HasView_x_27 = _init_l_Lean_Parser_command_visibility_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x_27);
 l_Lean_Parser_command_visibility_HasView = _init_l_Lean_Parser_command_visibility_HasView();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView);
 l_Lean_Parser_command_declModifiers = _init_l_Lean_Parser_command_declModifiers();
lean::mark_persistent(l_Lean_Parser_command_declModifiers);
 l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___elambda__1___closed__2);
 l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_declModifiers_HasView_x_27 = _init_l_Lean_Parser_command_declModifiers_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x_27);
 l_Lean_Parser_command_declModifiers_HasView = _init_l_Lean_Parser_command_declModifiers_HasView();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView);
 l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_declModifiers_Parser___closed__1 = _init_l_Lean_Parser_command_declModifiers_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_Parser___closed__1);
 l_Lean_Parser_command_declSig = _init_l_Lean_Parser_command_declSig();
lean::mark_persistent(l_Lean_Parser_command_declSig);
 l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1 = _init_l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__1);
 l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2 = _init_l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x_27___elambda__2___closed__2);
 l_Lean_Parser_command_declSig_HasView_x_27 = _init_l_Lean_Parser_command_declSig_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x_27);
 l_Lean_Parser_command_declSig_HasView = _init_l_Lean_Parser_command_declSig_HasView();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView);
 l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_declSig_Parser___closed__1 = _init_l_Lean_Parser_command_declSig_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declSig_Parser___closed__1);
 l_Lean_Parser_command_optDeclSig = _init_l_Lean_Parser_command_optDeclSig();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig);
 l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_optDeclSig_HasView_x_27 = _init_l_Lean_Parser_command_optDeclSig_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_HasView_x_27);
 l_Lean_Parser_command_optDeclSig_HasView = _init_l_Lean_Parser_command_optDeclSig_HasView();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_HasView);
 l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_optDeclSig_Parser___closed__1 = _init_l_Lean_Parser_command_optDeclSig_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_Parser___closed__1);
 l_Lean_Parser_command_equation = _init_l_Lean_Parser_command_equation();
lean::mark_persistent(l_Lean_Parser_command_equation);
 l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_equation_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_equation_HasView_x_27 = _init_l_Lean_Parser_command_equation_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_equation_HasView_x_27);
 l_Lean_Parser_command_equation_HasView = _init_l_Lean_Parser_command_equation_HasView();
lean::mark_persistent(l_Lean_Parser_command_equation_HasView);
 l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_equation_Parser___closed__1 = _init_l_Lean_Parser_command_equation_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_equation_Parser___closed__1);
 l_Lean_Parser_command_simpleDeclVal = _init_l_Lean_Parser_command_simpleDeclVal();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal);
 l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1 = _init_l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView_x_27___elambda__2___closed__1);
 l_Lean_Parser_command_simpleDeclVal_HasView_x_27 = _init_l_Lean_Parser_command_simpleDeclVal_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView_x_27);
 l_Lean_Parser_command_simpleDeclVal_HasView = _init_l_Lean_Parser_command_simpleDeclVal_HasView();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView);
 l_Lean_Parser_command_declVal = _init_l_Lean_Parser_command_declVal();
lean::mark_persistent(l_Lean_Parser_command_declVal);
 l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2 = _init_l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___elambda__1___closed__2);
 l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_declVal_HasView_x_27 = _init_l_Lean_Parser_command_declVal_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x_27);
 l_Lean_Parser_command_declVal_HasView = _init_l_Lean_Parser_command_declVal_HasView();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView);
 l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_declVal_Parser___closed__1 = _init_l_Lean_Parser_command_declVal_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declVal_Parser___closed__1);
 l_Lean_Parser_command_relaxedInferModifier = _init_l_Lean_Parser_command_relaxedInferModifier();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier);
 l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_relaxedInferModifier_HasView_x_27 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x_27);
 l_Lean_Parser_command_relaxedInferModifier_HasView = _init_l_Lean_Parser_command_relaxedInferModifier_HasView();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView);
 l_Lean_Parser_command_strictInferModifier = _init_l_Lean_Parser_command_strictInferModifier();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier);
 l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_strictInferModifier_HasView_x_27 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x_27);
 l_Lean_Parser_command_strictInferModifier_HasView = _init_l_Lean_Parser_command_strictInferModifier_HasView();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView);
 l_Lean_Parser_command_inferModifier = _init_l_Lean_Parser_command_inferModifier();
lean::mark_persistent(l_Lean_Parser_command_inferModifier);
 l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_inferModifier_HasView_x_27 = _init_l_Lean_Parser_command_inferModifier_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x_27);
 l_Lean_Parser_command_inferModifier_HasView = _init_l_Lean_Parser_command_inferModifier_HasView();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView);
 l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_inferModifier_Parser___closed__1 = _init_l_Lean_Parser_command_inferModifier_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_Parser___closed__1);
 l_Lean_Parser_command_introRule = _init_l_Lean_Parser_command_introRule();
lean::mark_persistent(l_Lean_Parser_command_introRule);
 l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_introRule_HasView_x_27 = _init_l_Lean_Parser_command_introRule_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x_27);
 l_Lean_Parser_command_introRule_HasView = _init_l_Lean_Parser_command_introRule_HasView();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView);
 l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_introRule_Parser___closed__1 = _init_l_Lean_Parser_command_introRule_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_introRule_Parser___closed__1);
 l_Lean_Parser_command_structBinderContent = _init_l_Lean_Parser_command_structBinderContent();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent);
 l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structBinderContent_HasView_x_27 = _init_l_Lean_Parser_command_structBinderContent_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x_27);
 l_Lean_Parser_command_structBinderContent_HasView = _init_l_Lean_Parser_command_structBinderContent_HasView();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView);
 l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_structBinderContent_Parser___closed__1 = _init_l_Lean_Parser_command_structBinderContent_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_Parser___closed__1);
 l_Lean_Parser_command_structExplicitBinderContent = _init_l_Lean_Parser_command_structExplicitBinderContent();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent);
 l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x_27);
 l_Lean_Parser_command_structExplicitBinderContent_HasView = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView);
 l_Lean_Parser_command_structExplicitBinder = _init_l_Lean_Parser_command_structExplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder);
 l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_structExplicitBinder_HasView_x_27 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x_27);
 l_Lean_Parser_command_structExplicitBinder_HasView = _init_l_Lean_Parser_command_structExplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView);
 l_Lean_Parser_command_structImplicitBinder = _init_l_Lean_Parser_command_structImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder);
 l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_structImplicitBinder_HasView_x_27 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x_27);
 l_Lean_Parser_command_structImplicitBinder_HasView = _init_l_Lean_Parser_command_structImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView);
 l_Lean_Parser_command_strictImplicitBinder = _init_l_Lean_Parser_command_strictImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder);
 l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_strictImplicitBinder_HasView_x_27 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x_27);
 l_Lean_Parser_command_strictImplicitBinder_HasView = _init_l_Lean_Parser_command_strictImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView);
 l_Lean_Parser_command_instImplicitBinder = _init_l_Lean_Parser_command_instImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder);
 l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_instImplicitBinder_HasView_x_27 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x_27);
 l_Lean_Parser_command_instImplicitBinder_HasView = _init_l_Lean_Parser_command_instImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView);
 l_Lean_Parser_command_structureFieldBlock = _init_l_Lean_Parser_command_structureFieldBlock();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock);
 l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structureFieldBlock_HasView_x_27 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x_27);
 l_Lean_Parser_command_structureFieldBlock_HasView = _init_l_Lean_Parser_command_structureFieldBlock_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView);
 l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_structureFieldBlock_Parser___closed__1 = _init_l_Lean_Parser_command_structureFieldBlock_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_Parser___closed__1);
 l_Lean_Parser_command_oldUnivParams = _init_l_Lean_Parser_command_oldUnivParams();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams);
 l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_oldUnivParams_HasView_x_27 = _init_l_Lean_Parser_command_oldUnivParams_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_HasView_x_27);
 l_Lean_Parser_command_oldUnivParams_HasView = _init_l_Lean_Parser_command_oldUnivParams_HasView();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_HasView);
 l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_oldUnivParams_Parser___closed__1 = _init_l_Lean_Parser_command_oldUnivParams_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_Parser___closed__1);
 l_Lean_Parser_command_univParams = _init_l_Lean_Parser_command_univParams();
lean::mark_persistent(l_Lean_Parser_command_univParams);
 l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_univParams_HasView_x_27 = _init_l_Lean_Parser_command_univParams_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView_x_27);
 l_Lean_Parser_command_univParams_HasView = _init_l_Lean_Parser_command_univParams_HasView();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView);
 l_Lean_Parser_command_identUnivParams = _init_l_Lean_Parser_command_identUnivParams();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams);
 l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_identUnivParams_HasView_x_27 = _init_l_Lean_Parser_command_identUnivParams_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x_27);
 l_Lean_Parser_command_identUnivParams_HasView = _init_l_Lean_Parser_command_identUnivParams_HasView();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView);
 l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_identUnivParams_Parser___closed__1 = _init_l_Lean_Parser_command_identUnivParams_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_Parser___closed__1);
 l_Lean_Parser_command_structureKw = _init_l_Lean_Parser_command_structureKw();
lean::mark_persistent(l_Lean_Parser_command_structureKw);
 l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___elambda__1___closed__2);
 l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_structureKw_HasView_x_27 = _init_l_Lean_Parser_command_structureKw_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x_27);
 l_Lean_Parser_command_structureKw_HasView = _init_l_Lean_Parser_command_structureKw_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView);
 l_Lean_Parser_command_extends = _init_l_Lean_Parser_command_extends();
lean::mark_persistent(l_Lean_Parser_command_extends);
 l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_extends_HasView_x_27 = _init_l_Lean_Parser_command_extends_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x_27);
 l_Lean_Parser_command_extends_HasView = _init_l_Lean_Parser_command_extends_HasView();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView);
 l_Lean_Parser_command_structureCtor = _init_l_Lean_Parser_command_structureCtor();
lean::mark_persistent(l_Lean_Parser_command_structureCtor);
 l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structureCtor_HasView_x_27 = _init_l_Lean_Parser_command_structureCtor_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView_x_27);
 l_Lean_Parser_command_structureCtor_HasView = _init_l_Lean_Parser_command_structureCtor_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView);
 l_Lean_Parser_command_structure = _init_l_Lean_Parser_command_structure();
lean::mark_persistent(l_Lean_Parser_command_structure);
 l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_command_structure_HasView_x_27 = _init_l_Lean_Parser_command_structure_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x_27);
 l_Lean_Parser_command_structure_HasView = _init_l_Lean_Parser_command_structure_HasView();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView);
 l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_structure_Parser___closed__1 = _init_l_Lean_Parser_command_structure_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structure_Parser___closed__1);
 l_Lean_Parser_command_defLike_kind = _init_l_Lean_Parser_command_defLike_kind();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__2);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__3);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__4);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___elambda__1___closed__5);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27___lambda__1___closed__7);
 l_Lean_Parser_command_defLike_kind_HasView_x_27 = _init_l_Lean_Parser_command_defLike_kind_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x_27);
 l_Lean_Parser_command_defLike_kind_HasView = _init_l_Lean_Parser_command_defLike_kind_HasView();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView);
 l_Lean_Parser_command_defLike = _init_l_Lean_Parser_command_defLike();
lean::mark_persistent(l_Lean_Parser_command_defLike);
 l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_defLike_HasView_x_27 = _init_l_Lean_Parser_command_defLike_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x_27);
 l_Lean_Parser_command_defLike_HasView = _init_l_Lean_Parser_command_defLike_HasView();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView);
 l_Lean_Parser_command_instance = _init_l_Lean_Parser_command_instance();
lean::mark_persistent(l_Lean_Parser_command_instance);
 l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_instance_HasView_x_27 = _init_l_Lean_Parser_command_instance_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x_27);
 l_Lean_Parser_command_instance_HasView = _init_l_Lean_Parser_command_instance_HasView();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView);
 l_Lean_Parser_command_example = _init_l_Lean_Parser_command_example();
lean::mark_persistent(l_Lean_Parser_command_example);
 l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_example_HasView_x_27 = _init_l_Lean_Parser_command_example_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x_27);
 l_Lean_Parser_command_example_HasView = _init_l_Lean_Parser_command_example_HasView();
lean::mark_persistent(l_Lean_Parser_command_example_HasView);
 l_Lean_Parser_command_constantKeyword = _init_l_Lean_Parser_command_constantKeyword();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword);
 l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_constantKeyword_HasView_x_27 = _init_l_Lean_Parser_command_constantKeyword_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x_27);
 l_Lean_Parser_command_constantKeyword_HasView = _init_l_Lean_Parser_command_constantKeyword_HasView();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView);
 l_Lean_Parser_command_axiom = _init_l_Lean_Parser_command_axiom();
lean::mark_persistent(l_Lean_Parser_command_axiom);
 l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1 = _init_l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView_x_27___elambda__2___closed__1);
 l_Lean_Parser_command_axiom_HasView_x_27 = _init_l_Lean_Parser_command_axiom_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView_x_27);
 l_Lean_Parser_command_axiom_HasView = _init_l_Lean_Parser_command_axiom_HasView();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView);
 l_Lean_Parser_command_inductive = _init_l_Lean_Parser_command_inductive();
lean::mark_persistent(l_Lean_Parser_command_inductive);
 l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1 = _init_l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27___elambda__1___closed__1);
 l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_command_inductive_HasView_x_27 = _init_l_Lean_Parser_command_inductive_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x_27);
 l_Lean_Parser_command_inductive_HasView = _init_l_Lean_Parser_command_inductive_HasView();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView);
 l_Lean_Parser_command_declaration_inner = _init_l_Lean_Parser_command_declaration_inner();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner);
 l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_command_declaration_inner_HasView_x_27 = _init_l_Lean_Parser_command_declaration_inner_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x_27);
 l_Lean_Parser_command_declaration_inner_HasView = _init_l_Lean_Parser_command_declaration_inner_HasView();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView);
 l_Lean_Parser_command_declaration = _init_l_Lean_Parser_command_declaration();
lean::mark_persistent(l_Lean_Parser_command_declaration);
 l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1 = _init_l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__1);
 l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2 = _init_l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x_27___elambda__2___closed__2);
 l_Lean_Parser_command_declaration_HasView_x_27 = _init_l_Lean_Parser_command_declaration_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x_27);
 l_Lean_Parser_command_declaration_HasView = _init_l_Lean_Parser_command_declaration_HasView();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView);
 l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView);
 l_Lean_Parser_command_declaration_Parser___closed__1 = _init_l_Lean_Parser_command_declaration_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declaration_Parser___closed__1);
return w;
}
