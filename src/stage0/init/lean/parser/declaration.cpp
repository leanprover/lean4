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
obj* l_Lean_Parser_command_univParams_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_HasView;
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_relaxedInferModifier;
obj* l_Lean_Parser_command_equation_Parser___closed__1;
extern obj* l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27;
obj* l_Lean_Parser_command_structExplicitBinder_HasView;
obj* l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_declAttributes_HasView_x27;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView;
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_typeSpec_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
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
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x27(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_binderDefault_HasView;
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6;
obj* l_Lean_Parser_command_example_HasView_x27;
obj* l_Lean_Parser_command_declVal_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1;
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x27;
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2;
extern obj* l_Lean_Parser_Term_paren_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_simpleDeclVal;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes;
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3;
extern obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_termParser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_defLike_HasView_x27;
obj* l_Lean_Parser_command_structureFieldBlock_Parser___closed__1;
obj* l_Lean_Parser_command_structure_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_structureKw;
obj* l_Lean_Parser_command_inferModifier_Parser___closed__1;
obj* l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structureCtor;
obj* l_Lean_Parser_command_optDeclSig_HasView_x27;
obj* l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_docComment_HasView_x27;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_extends;
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_Parser___closed__1;
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___elambda__1(obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_constantKeyword;
obj* l_Lean_Parser_command_defLike;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView;
obj* l_Lean_Parser_command_docComment_Parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_declSig;
obj* l_Lean_Parser_command_attrInstance_HasView_x27;
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_declSig_Parser(obj*, obj*, obj*, obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(obj*, obj*, obj*);
extern obj* l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declVal_HasView;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1;
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9(obj*, obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structImplicitBinder;
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_Parser___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
obj* l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_oldUnivParams;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_command_structBinderContent_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27;
obj* l_Lean_Parser_command_declModifiers_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_command_structureCtor_HasView;
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView_x27;
obj* l_Lean_Parser_command_declAttributes_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x27;
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_axiom_HasView;
obj* l_Lean_Parser_command_declaration_HasView;
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3;
extern obj* l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_declVal_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x27;
obj* l_Lean_Parser_MonadParsec_many_x27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structImplicitBinder_HasView;
obj* l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_command_inferModifier_HasView;
obj* l_Lean_Parser_command_inductive_HasView;
obj* l_Lean_Parser_command_declaration_HasView_x27;
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_attrInstance_HasView;
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_introRule_HasView;
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView;
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8(obj*);
obj* l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x27___elambda__1___spec__1(obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_declSig_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
obj* l___private_init_lean_parser_parsec_2__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_optDeclSig_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Term_Parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_declaration_inner_HasView;
obj* l_Lean_Parser_command_declVal_HasView_x27;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView;
obj* l_Lean_Parser_command_structureFieldBlock;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams;
obj* l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView;
obj* l_Lean_Parser_command_optDeclSig_HasView_x27___elambda__1(obj*);
extern obj* l_Lean_Parser_command_notationLike_HasView;
obj* l_List_join___main___rarg(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structure;
obj* l_Lean_Parser_command_structure_HasView_x27;
obj* l_Lean_Parser_command_declAttributes_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_axiom;
obj* l_Lean_Parser_Term_binderDefault_Parser(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_command_instImplicitBinder;
obj* l_String_OldIterator_next___main(obj*);
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_declaration_inner;
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3;
extern obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
obj* l_Lean_Parser_command_inferModifier;
obj* l_Lean_Parser_command_extends_HasView_x27;
obj* l_Lean_Parser_command_declaration_inner_HasView_x27;
obj* l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1(obj*);
extern obj* l_Lean_Parser_command_notation_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_declModifiers_HasView;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_strictInferModifier_HasView;
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_declModifiers_Parser___closed__1;
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_univParams_HasView_x27;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___elambda__1(obj*);
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_command_visibility_HasView;
obj* l_Lean_Parser_command_univParams_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1;
extern obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_command_extends_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x27;
obj* l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView;
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1;
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_tokens___rarg(obj*);
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1(obj*);
extern obj* l_Lean_Parser_Term_tuple_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4;
extern obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5;
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2;
obj* l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_oldUnivParams_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_instance_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5;
obj* l_Lean_Parser_Term_optType_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig;
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4;
extern obj* l_Lean_Parser_Term_optType_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_attrInstance;
obj* l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structureFieldBlock_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_example_HasView;
obj* l_Lean_Parser_command_introRule_Parser___closed__1;
extern obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_command_declSig_HasView_x27;
obj* l_Lean_Parser_command_docComment_HasView;
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_instImplicitBinder_HasView;
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_example_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_HasView;
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_declAttributes_Parser___closed__1;
obj* l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structBinderContent_HasView_x27;
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_Term_bracketedBinders_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_structure_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(obj*);
obj* l_Lean_Parser_command_declVal_Parser___closed__1;
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1;
extern obj* l_Lean_Parser_maxPrec;
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_example_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_equation_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4;
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declVal;
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_command_structBinderContent_Parser___closed__1;
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
obj* l_String_trim(obj*);
obj* l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_command_declModifiers;
obj* l_Lean_Parser_command_structure_HasView;
obj* l_Lean_Parser_command_declModifiers_HasView_x27;
extern obj* l_Lean_Parser_Term_binderDefault_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structureFieldBlock_HasView;
extern obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_declaration;
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, uint8, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_instance;
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_extends_HasView;
obj* l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3;
extern obj* l_Lean_Parser_Term_bracketedBinders_HasView;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_Parser___closed__1;
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27;
obj* l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
obj* l_Lean_Parser_command_identUnivParams_HasView;
obj* l_Lean_Parser_command_simpleDeclVal_HasView;
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1(obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_equation_HasView_x27;
obj* l_Lean_Parser_command_inductive;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_constantKeyword_HasView;
obj* l_Lean_Parser_command_docComment;
obj* l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4(obj*);
extern obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_defLike_kind;
obj* l_Lean_Parser_command_attrInstance_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_equation;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_termParserCommandParserCoe(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_introRule_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_docComment_Parser___closed__1;
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5;
extern obj* l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictInferModifier;
obj* l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27;
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_command_declaration_Parser___closed__1;
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2;
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declAttributes_HasView;
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_command_univParams_HasView;
obj* l_Lean_Parser_command_structure_Parser___closed__1;
obj* l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1(obj*);
extern obj* l_Lean_Parser_command_mixfix_kind_HasView_x27___elambda__1___closed__6;
obj* l_Lean_Parser_command_docComment_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27;
obj* l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens;
extern obj* l_Lean_Parser_Term_typeSpec_HasView;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1(obj*);
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27;
obj* l_Lean_Parser_command_docComment_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_CommandParserM_Alternative(obj*);
obj* l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_defLike_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_declaration_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_CommandParserM_Monad(obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x27;
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
obj* l_Lean_Parser_command_optDeclSig_Parser___closed__1;
obj* l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27;
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_strictImplicitBinder;
obj* l_String_quote(obj*);
obj* l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_structExplicitBinderContent;
obj* l_Lean_Parser_Term_typeSpec_Parser(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_command_instance_HasView;
obj* l_List_map___main___at_Lean_Parser_Term_tuple_HasView_x27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_optDeclSig_HasView;
obj* l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(obj*);
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_docComment_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_command_visibility;
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_inductive_HasView_x27;
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_command_example;
obj* l_Lean_Parser_command_docComment_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27;
extern obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_command_structureKw_HasView_x27;
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_command_axiom_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_CommandParserM_MonadExcept(obj*);
obj* l_Lean_Parser_command_declSig_Parser___closed__1;
obj* l_Lean_Parser_command_introRule_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_command_equation_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_introRule;
obj* l_Lean_Parser_command_inferModifier_HasView_x27;
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_command_structureCtor_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_command_structExplicitBinder;
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_termParserCommandParserCoe(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_termParser_run(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_docComment() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("docComment");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_command_docComment;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
return x_7;
}
}
obj* l_Lean_Parser_command_docComment_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_command_docComment;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
if (lean::obj_tag(x_4) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_docComment;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_5);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_16);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = l_Lean_Parser_command_docComment;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3;
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_docComment;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_5);
x_40 = lean::box(3);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_command_docComment;
x_44 = l_Lean_Parser_Syntax_mkNode(x_43, x_42);
return x_44;
}
}
else
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
if (lean::obj_tag(x_4) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_32);
lean::cnstr_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_command_docComment;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_4, 0);
lean::inc(x_52);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_5);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_46);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_32);
lean::cnstr_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_command_docComment;
x_58 = l_Lean_Parser_Syntax_mkNode(x_57, x_56);
return x_58;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_Lean_Parser_command_docComment_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_32; 
x_32 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; 
x_33 = l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1;
return x_33;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
lean::dec(x_32);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; 
x_36 = lean::box(3);
x_2 = x_35;
x_3 = x_36;
goto block_31;
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_2 = x_38;
x_3 = x_37;
goto block_31;
}
}
block_31:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_4 = x_29;
goto block_27;
}
else
{
obj* x_30; 
lean::dec(x_3);
x_30 = lean::box(0);
x_4 = x_30;
goto block_27;
}
block_27:
{
obj* x_5; obj* x_6; obj* x_13; obj* x_14; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_13 = x_2;
x_14 = x_24;
goto block_23;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
lean::dec(x_2);
x_13 = x_26;
x_14 = x_25;
goto block_23;
}
block_12:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
block_23:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_16;
x_6 = x_19;
goto block_12;
}
}
else
{
obj* x_20; 
lean::dec(x_14);
x_20 = lean::box(0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; 
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_20);
return x_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
lean::dec(x_13);
x_5 = x_20;
x_6 = x_22;
goto block_12;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_docComment_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_docComment_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_docComment_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_docComment_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
lean::inc(x_6);
lean::inc(x_9);
x_10 = l_Lean_Parser_token(x_9, x_6, x_7);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_10, 1);
x_14 = lean::cnstr_get(x_10, 0);
lean::dec(x_14);
x_15 = !lean::is_exclusive(x_11);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
x_17 = lean::cnstr_get(x_11, 1);
x_18 = lean::cnstr_get(x_11, 2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_40; obj* x_41; uint8 x_42; 
x_40 = lean::cnstr_get(x_16, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_42 = lean::string_dec_eq(x_1, x_41);
lean::dec(x_1);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::free_heap_obj(x_11);
lean::free_heap_obj(x_10);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_6);
x_44 = lean::box(0);
x_45 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_41, x_3, x_43, x_44, x_9, x_17, x_13);
lean::dec(x_9);
lean::dec(x_43);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_45);
if (x_47 == 0)
{
obj* x_48; uint8 x_49; 
x_48 = lean::cnstr_get(x_45, 0);
lean::dec(x_48);
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = lean::cnstr_get(x_46, 2);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_46, 2, x_52);
lean::cnstr_set(x_46, 0, x_16);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_46);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_54);
x_56 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_55, x_8);
x_57 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_56);
lean::cnstr_set(x_45, 0, x_57);
return x_45;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_58 = lean::cnstr_get(x_46, 1);
x_59 = lean::cnstr_get(x_46, 2);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_46);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_16);
lean::cnstr_set(x_61, 1, x_58);
lean::cnstr_set(x_61, 2, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_63);
x_65 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_64, x_8);
x_66 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_65);
lean::cnstr_set(x_45, 0, x_66);
return x_45;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_67 = lean::cnstr_get(x_45, 1);
lean::inc(x_67);
lean::dec(x_45);
x_68 = lean::cnstr_get(x_46, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_46, 2);
lean::inc(x_69);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 lean::cnstr_release(x_46, 2);
 x_70 = x_46;
} else {
 lean::dec_ref(x_46);
 x_70 = lean::box(0);
}
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_16);
lean::cnstr_set(x_72, 1, x_68);
lean::cnstr_set(x_72, 2, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_73);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_74);
x_76 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_75, x_8);
x_77 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_67);
return x_78;
}
}
else
{
uint8 x_79; 
lean::dec(x_16);
x_79 = !lean::is_exclusive(x_45);
if (x_79 == 0)
{
obj* x_80; uint8 x_81; 
x_80 = lean::cnstr_get(x_45, 0);
lean::dec(x_80);
x_81 = !lean::is_exclusive(x_46);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_46);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_82);
x_85 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_84, x_8);
x_86 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_85);
lean::cnstr_set(x_45, 0, x_86);
return x_45;
}
else
{
obj* x_87; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_87 = lean::cnstr_get(x_46, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
lean::inc(x_87);
lean::dec(x_46);
x_89 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_88);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_89);
x_91 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_90);
x_93 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_92, x_8);
x_94 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_93);
lean::cnstr_set(x_45, 0, x_94);
return x_45;
}
}
else
{
obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_95 = lean::cnstr_get(x_45, 1);
lean::inc(x_95);
lean::dec(x_45);
x_96 = lean::cnstr_get(x_46, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_98 = x_46;
} else {
 lean::dec_ref(x_46);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_99);
x_101 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_100);
x_103 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_102, x_8);
x_104 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_103);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_95);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_41);
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_3);
x_106 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_11, 2, x_106);
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_11);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_108, x_107);
x_110 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_109, x_8);
x_111 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_110);
lean::cnstr_set(x_10, 0, x_111);
return x_10;
}
}
else
{
obj* x_112; 
lean::free_heap_obj(x_11);
lean::dec(x_16);
lean::free_heap_obj(x_10);
lean::dec(x_1);
x_112 = lean::box(0);
x_19 = x_112;
goto block_39;
}
block_39:
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
lean::dec(x_19);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_6);
x_21 = lean::box(0);
x_22 = l_String_splitAux___main___closed__1;
x_23 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_22, x_3, x_20, x_21, x_9, x_17, x_13);
lean::dec(x_9);
lean::dec(x_20);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_23, 0);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_25);
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_26);
x_29 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_28, x_8);
x_30 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_29);
lean::cnstr_set(x_23, 0, x_30);
return x_23;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_23, 0);
x_32 = lean::cnstr_get(x_23, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_23);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_31);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_33);
x_36 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_35, x_8);
x_37 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_113 = lean::cnstr_get(x_11, 0);
x_114 = lean::cnstr_get(x_11, 1);
x_115 = lean::cnstr_get(x_11, 2);
lean::inc(x_115);
lean::inc(x_114);
lean::inc(x_113);
lean::dec(x_11);
if (lean::obj_tag(x_113) == 0)
{
obj* x_131; obj* x_132; uint8 x_133; 
x_131 = lean::cnstr_get(x_113, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_131, 1);
lean::inc(x_132);
lean::dec(x_131);
x_133 = lean::string_dec_eq(x_1, x_132);
lean::dec(x_1);
if (x_133 == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::free_heap_obj(x_10);
x_134 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_134, 0, x_6);
x_135 = lean::box(0);
x_136 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_132, x_3, x_134, x_135, x_9, x_114, x_13);
lean::dec(x_9);
lean::dec(x_134);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_138 = lean::cnstr_get(x_136, 1);
lean::inc(x_138);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_139 = x_136;
} else {
 lean::dec_ref(x_136);
 x_139 = lean::box(0);
}
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
x_143 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_142)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_142;
}
lean::cnstr_set(x_144, 0, x_113);
lean::cnstr_set(x_144, 1, x_140);
lean::cnstr_set(x_144, 2, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_144);
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_145);
x_147 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_143, x_146);
x_148 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_147, x_8);
x_149 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_148);
if (lean::is_scalar(x_139)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_139;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_138);
return x_150;
}
else
{
obj* x_151; obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_113);
x_151 = lean::cnstr_get(x_136, 1);
lean::inc(x_151);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_152 = x_136;
} else {
 lean::dec_ref(x_136);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_137, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get_scalar<uint8>(x_137, sizeof(void*)*1);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_155 = x_137;
} else {
 lean::dec_ref(x_137);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_156);
x_158 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_158, x_157);
x_160 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_159, x_8);
x_161 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_160);
if (lean::is_scalar(x_152)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_152;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_151);
return x_162;
}
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_132);
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_3);
x_163 = l_Lean_Parser_finishCommentBlock___closed__2;
x_164 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_164, 0, x_113);
lean::cnstr_set(x_164, 1, x_114);
lean::cnstr_set(x_164, 2, x_163);
x_165 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_164);
x_166 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_167 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_166, x_165);
x_168 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_167, x_8);
x_169 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_168);
lean::cnstr_set(x_10, 0, x_169);
return x_10;
}
}
else
{
obj* x_170; 
lean::dec(x_113);
lean::free_heap_obj(x_10);
lean::dec(x_1);
x_170 = lean::box(0);
x_116 = x_170;
goto block_130;
}
block_130:
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_116);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_6);
x_118 = lean::box(0);
x_119 = l_String_splitAux___main___closed__1;
x_120 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_119, x_3, x_117, x_118, x_9, x_114, x_13);
lean::dec(x_9);
lean::dec(x_117);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_120, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_123 = x_120;
} else {
 lean::dec_ref(x_120);
 x_123 = lean::box(0);
}
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_115, x_121);
x_125 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_125, x_124);
x_127 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_126, x_8);
x_128 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_127);
if (lean::is_scalar(x_123)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_123;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_122);
return x_129;
}
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_171 = lean::cnstr_get(x_10, 1);
lean::inc(x_171);
lean::dec(x_10);
x_172 = lean::cnstr_get(x_11, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_11, 1);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_11, 2);
lean::inc(x_174);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_175 = x_11;
} else {
 lean::dec_ref(x_11);
 x_175 = lean::box(0);
}
if (lean::obj_tag(x_172) == 0)
{
obj* x_191; obj* x_192; uint8 x_193; 
x_191 = lean::cnstr_get(x_172, 0);
lean::inc(x_191);
x_192 = lean::cnstr_get(x_191, 1);
lean::inc(x_192);
lean::dec(x_191);
x_193 = lean::string_dec_eq(x_1, x_192);
lean::dec(x_1);
if (x_193 == 0)
{
obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
lean::dec(x_175);
x_194 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_194, 0, x_6);
x_195 = lean::box(0);
x_196 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_192, x_3, x_194, x_195, x_9, x_173, x_171);
lean::dec(x_9);
lean::dec(x_194);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_198 = lean::cnstr_get(x_196, 1);
lean::inc(x_198);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_199 = x_196;
} else {
 lean::dec_ref(x_196);
 x_199 = lean::box(0);
}
x_200 = lean::cnstr_get(x_197, 1);
lean::inc(x_200);
x_201 = lean::cnstr_get(x_197, 2);
lean::inc(x_201);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 lean::cnstr_release(x_197, 1);
 lean::cnstr_release(x_197, 2);
 x_202 = x_197;
} else {
 lean::dec_ref(x_197);
 x_202 = lean::box(0);
}
x_203 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_202)) {
 x_204 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_204 = x_202;
}
lean::cnstr_set(x_204, 0, x_172);
lean::cnstr_set(x_204, 1, x_200);
lean::cnstr_set(x_204, 2, x_203);
x_205 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_201, x_204);
x_206 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_205);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_203, x_206);
x_208 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_207, x_8);
x_209 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_208);
if (lean::is_scalar(x_199)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_199;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_198);
return x_210;
}
else
{
obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_172);
x_211 = lean::cnstr_get(x_196, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_212 = x_196;
} else {
 lean::dec_ref(x_196);
 x_212 = lean::box(0);
}
x_213 = lean::cnstr_get(x_197, 0);
lean::inc(x_213);
x_214 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*1);
if (lean::is_exclusive(x_197)) {
 lean::cnstr_release(x_197, 0);
 x_215 = x_197;
} else {
 lean::dec_ref(x_197);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
lean::cnstr_set_scalar(x_216, sizeof(void*)*1, x_214);
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_216);
x_218 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_219 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_218, x_217);
x_220 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_219, x_8);
x_221 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_220);
if (lean::is_scalar(x_212)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_212;
}
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_211);
return x_222;
}
}
else
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; 
lean::dec(x_192);
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_3);
x_223 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_175)) {
 x_224 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_224 = x_175;
}
lean::cnstr_set(x_224, 0, x_172);
lean::cnstr_set(x_224, 1, x_173);
lean::cnstr_set(x_224, 2, x_223);
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_224);
x_226 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_227 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_226, x_225);
x_228 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_227, x_8);
x_229 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_228);
x_230 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_171);
return x_230;
}
}
else
{
obj* x_231; 
lean::dec(x_175);
lean::dec(x_172);
lean::dec(x_1);
x_231 = lean::box(0);
x_176 = x_231;
goto block_190;
}
block_190:
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
lean::dec(x_176);
x_177 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_177, 0, x_6);
x_178 = lean::box(0);
x_179 = l_String_splitAux___main___closed__1;
x_180 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_179, x_3, x_177, x_178, x_9, x_173, x_171);
lean::dec(x_9);
lean::dec(x_177);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_180, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_183 = x_180;
} else {
 lean::dec_ref(x_180);
 x_183 = lean::box(0);
}
x_184 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_174, x_181);
x_185 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_186 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_185, x_184);
x_187 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_186, x_8);
x_188 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_187);
if (lean::is_scalar(x_183)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_183;
}
lean::cnstr_set(x_189, 0, x_188);
lean::cnstr_set(x_189, 1, x_182);
return x_189;
}
}
}
else
{
uint8 x_232; 
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_232 = !lean::is_exclusive(x_10);
if (x_232 == 0)
{
obj* x_233; uint8 x_234; 
x_233 = lean::cnstr_get(x_10, 0);
lean::dec(x_233);
x_234 = !lean::is_exclusive(x_11);
if (x_234 == 0)
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
x_235 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_236 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_235, x_11);
x_237 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_236, x_8);
x_238 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_237);
lean::cnstr_set(x_10, 0, x_238);
return x_10;
}
else
{
obj* x_239; uint8 x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_239 = lean::cnstr_get(x_11, 0);
x_240 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_239);
lean::dec(x_11);
x_241 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_241, 0, x_239);
lean::cnstr_set_scalar(x_241, sizeof(void*)*1, x_240);
x_242 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_243 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_242, x_241);
x_244 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_243, x_8);
x_245 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_244);
lean::cnstr_set(x_10, 0, x_245);
return x_10;
}
}
else
{
obj* x_246; obj* x_247; uint8 x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_246 = lean::cnstr_get(x_10, 1);
lean::inc(x_246);
lean::dec(x_10);
x_247 = lean::cnstr_get(x_11, 0);
lean::inc(x_247);
x_248 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_249 = x_11;
} else {
 lean::dec_ref(x_11);
 x_249 = lean::box(0);
}
if (lean::is_scalar(x_249)) {
 x_250 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_250 = x_249;
}
lean::cnstr_set(x_250, 0, x_247);
lean::cnstr_set_scalar(x_250, sizeof(void*)*1, x_248);
x_251 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_252 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_251, x_250);
x_253 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_252, x_8);
x_254 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_253);
x_255 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_246);
return x_255;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_String_isEmpty(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::string_length(x_1);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_9);
lean::inc(x_5);
x_11 = l___private_init_lean_parser_parsec_2__strAux___main(x_8, x_10, x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_12 = lean::box(0);
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_2);
lean::cnstr_set(x_14, 3, x_12);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_6);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_5);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_2);
lean::dec(x_1);
x_22 = l_String_splitAux___main___closed__1;
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
return x_25;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_5);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_7, x_1, x_2, x_3, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_9, 2);
x_14 = lean::cnstr_get(x_9, 0);
lean::dec(x_14);
x_15 = 0;
x_16 = lean::box(x_15);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 0, x_16);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_9);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 2);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_17, 1);
lean::dec(x_20);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_17, 2, x_21);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_8, 0, x_17);
return x_8;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set(x_8, 0, x_24);
return x_8;
}
}
else
{
uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_17);
x_25 = 1;
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = lean::box(x_25);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_5);
lean::cnstr_set(x_28, 2, x_26);
lean::cnstr_set(x_8, 0, x_28);
return x_8;
}
}
else
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_9, 1);
x_30 = lean::cnstr_get(x_9, 2);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_9);
x_31 = 0;
x_32 = lean::box(x_31);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_4);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 lean::cnstr_release(x_34, 2);
 x_36 = x_34;
} else {
 lean::dec_ref(x_34);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_5);
lean::cnstr_set(x_38, 2, x_37);
lean::cnstr_set(x_8, 0, x_38);
return x_8;
}
else
{
uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_34);
x_39 = 1;
x_40 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_41 = lean::box(x_39);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_40);
lean::cnstr_set(x_8, 0, x_42);
return x_8;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_43 = lean::cnstr_get(x_8, 1);
lean::inc(x_43);
lean::dec(x_8);
x_44 = lean::cnstr_get(x_9, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_9, 2);
lean::inc(x_45);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_46 = x_9;
} else {
 lean::dec_ref(x_9);
 x_46 = lean::box(0);
}
x_47 = 0;
x_48 = lean::box(x_47);
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_46;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
lean::cnstr_set(x_49, 2, x_4);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 lean::cnstr_release(x_50, 2);
 x_52 = x_50;
} else {
 lean::dec_ref(x_50);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_5);
lean::cnstr_set(x_54, 2, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_43);
return x_55;
}
else
{
uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_50);
x_56 = 1;
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = lean::box(x_56);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_5);
lean::cnstr_set(x_59, 2, x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_43);
return x_60;
}
}
}
else
{
uint8 x_61; 
lean::dec(x_9);
lean::dec(x_4);
x_61 = !lean::is_exclusive(x_8);
if (x_61 == 0)
{
obj* x_62; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_8, 0);
lean::dec(x_62);
x_63 = 1;
x_64 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_65 = lean::box(x_63);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_5);
lean::cnstr_set(x_66, 2, x_64);
lean::cnstr_set(x_8, 0, x_66);
return x_8;
}
else
{
obj* x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_67 = lean::cnstr_get(x_8, 1);
lean::inc(x_67);
lean::dec(x_8);
x_68 = 1;
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = lean::box(x_68);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
lean::cnstr_set(x_71, 2, x_69);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_67);
return x_72;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
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
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
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
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
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
x_27 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_24, x_26, x_25, x_25, x_1, x_2, x_3, x_4);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
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
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_33);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = l_String_OldIterator_next___main(x_3);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_19);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_4);
return x_41;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
lean::inc(x_1);
lean::inc(x_4);
lean::inc(x_3);
x_11 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_12, 1);
x_16 = lean::cnstr_get(x_12, 2);
x_17 = lean::cnstr_get(x_12, 0);
lean::dec(x_17);
lean::inc(x_15);
x_18 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_1, x_10, x_3, x_4, x_15, x_13);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
lean::free_heap_obj(x_12);
lean::dec(x_15);
x_20 = !lean::is_exclusive(x_18);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_18, 0);
lean::dec(x_21);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
lean::cnstr_set(x_18, 0, x_22);
return x_18;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
lean::dec(x_18);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (x_26 == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_18);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_18, 0);
lean::dec(x_28);
x_29 = lean::cnstr_get(x_19, 0);
lean::inc(x_29);
lean::dec(x_19);
x_30 = lean::cnstr_get(x_29, 2);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_mjoin___rarg___closed__1;
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::box(0);
lean::cnstr_set(x_12, 2, x_33);
lean::cnstr_set(x_12, 0, x_34);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_12);
lean::cnstr_set(x_18, 0, x_35);
return x_18;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_18, 1);
lean::inc(x_36);
lean::dec(x_18);
x_37 = lean::cnstr_get(x_19, 0);
lean::inc(x_37);
lean::dec(x_19);
x_38 = lean::cnstr_get(x_37, 2);
lean::inc(x_38);
lean::dec(x_37);
x_39 = l_mjoin___rarg___closed__1;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_40, 0, x_38);
lean::closure_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::box(0);
lean::cnstr_set(x_12, 2, x_41);
lean::cnstr_set(x_12, 0, x_42);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_12);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_36);
return x_44;
}
}
else
{
uint8 x_45; 
lean::free_heap_obj(x_12);
lean::dec(x_15);
x_45 = !lean::is_exclusive(x_18);
if (x_45 == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_18, 0);
lean::dec(x_46);
x_47 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
lean::cnstr_set(x_18, 0, x_47);
return x_18;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_18, 1);
lean::inc(x_48);
lean::dec(x_18);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_12, 1);
x_52 = lean::cnstr_get(x_12, 2);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_12);
lean::inc(x_51);
x_53 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_1, x_10, x_3, x_4, x_51, x_13);
lean::dec(x_10);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_51);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_56 = x_53;
} else {
 lean::dec_ref(x_53);
 x_56 = lean::box(0);
}
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_54);
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_55);
return x_58;
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_60 = lean::cnstr_get(x_53, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_61 = x_53;
} else {
 lean::dec_ref(x_53);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_54, 0);
lean::inc(x_62);
lean::dec(x_54);
x_63 = lean::cnstr_get(x_62, 2);
lean::inc(x_63);
lean::dec(x_62);
x_64 = l_mjoin___rarg___closed__1;
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_51);
lean::cnstr_set(x_68, 2, x_66);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_68);
if (lean::is_scalar(x_61)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_61;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_60);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_51);
x_71 = lean::cnstr_get(x_53, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_72 = x_53;
} else {
 lean::dec_ref(x_53);
 x_72 = lean::box(0);
}
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_54);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_71);
return x_74;
}
}
}
}
else
{
uint8 x_75; 
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_75 = !lean::is_exclusive(x_11);
if (x_75 == 0)
{
obj* x_76; uint8 x_77; 
x_76 = lean::cnstr_get(x_11, 0);
lean::dec(x_76);
x_77 = !lean::is_exclusive(x_12);
if (x_77 == 0)
{
return x_11;
}
else
{
obj* x_78; uint8 x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_12, 0);
x_79 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
lean::inc(x_78);
lean::dec(x_12);
x_80 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_79);
lean::cnstr_set(x_11, 0, x_80);
return x_11;
}
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_11, 1);
lean::inc(x_81);
lean::dec(x_11);
x_82 = lean::cnstr_get(x_12, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_84 = x_12;
} else {
 lean::dec_ref(x_12);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_81);
return x_86;
}
}
}
else
{
obj* x_87; obj* x_88; 
x_87 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
uint8 x_89; 
x_89 = !lean::is_exclusive(x_87);
if (x_89 == 0)
{
obj* x_90; uint8 x_91; 
x_90 = lean::cnstr_get(x_87, 0);
lean::dec(x_90);
x_91 = !lean::is_exclusive(x_88);
if (x_91 == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_88, 2);
x_93 = lean::cnstr_get(x_88, 0);
lean::dec(x_93);
x_94 = lean::box(0);
x_95 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_88, 2, x_95);
lean::cnstr_set(x_88, 0, x_94);
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_92, x_88);
lean::cnstr_set(x_87, 0, x_96);
return x_87;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_88, 1);
x_98 = lean::cnstr_get(x_88, 2);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_88);
x_99 = lean::box(0);
x_100 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_97);
lean::cnstr_set(x_101, 2, x_100);
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_101);
lean::cnstr_set(x_87, 0, x_102);
return x_87;
}
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_103 = lean::cnstr_get(x_87, 1);
lean::inc(x_103);
lean::dec(x_87);
x_104 = lean::cnstr_get(x_88, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_88, 2);
lean::inc(x_105);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 lean::cnstr_release(x_88, 2);
 x_106 = x_88;
} else {
 lean::dec_ref(x_88);
 x_106 = lean::box(0);
}
x_107 = lean::box(0);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_106)) {
 x_109 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_109 = x_106;
}
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_104);
lean::cnstr_set(x_109, 2, x_108);
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_109);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_103);
return x_111;
}
}
else
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_87);
if (x_112 == 0)
{
obj* x_113; uint8 x_114; 
x_113 = lean::cnstr_get(x_87, 0);
lean::dec(x_113);
x_114 = !lean::is_exclusive(x_88);
if (x_114 == 0)
{
return x_87;
}
else
{
obj* x_115; uint8 x_116; obj* x_117; 
x_115 = lean::cnstr_get(x_88, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
lean::inc(x_115);
lean::dec(x_88);
x_117 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_116);
lean::cnstr_set(x_87, 0, x_117);
return x_87;
}
}
else
{
obj* x_118; obj* x_119; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; 
x_118 = lean::cnstr_get(x_87, 1);
lean::inc(x_118);
lean::dec(x_87);
x_119 = lean::cnstr_get(x_88, 0);
lean::inc(x_119);
x_120 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_121 = x_88;
} else {
 lean::dec_ref(x_88);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_118);
return x_123;
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_many_x27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_String_OldIterator_remaining___main(x_4);
lean::inc(x_4);
x_7 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_1, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_6);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_finishCommentBlock___closed__2;
x_11 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_9);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_4);
lean::cnstr_set(x_7, 0, x_11);
return x_7;
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::cnstr_get(x_13, 2);
lean::inc(x_14);
lean::dec(x_13);
x_15 = l_mjoin___rarg___closed__1;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_4);
lean::cnstr_set(x_19, 2, x_17);
lean::cnstr_set(x_7, 0, x_19);
return x_7;
}
else
{
lean::dec(x_4);
lean::cnstr_set(x_7, 0, x_11);
return x_7;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_7, 0);
x_21 = lean::cnstr_get(x_7, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_7);
x_22 = l_Lean_Parser_finishCommentBlock___closed__2;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
lean::dec(x_4);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_21);
return x_24;
}
else
{
uint8 x_25; 
x_25 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_27 = lean::cnstr_get(x_26, 2);
lean::inc(x_27);
lean::dec(x_26);
x_28 = l_mjoin___rarg___closed__1;
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_4);
lean::cnstr_set(x_32, 2, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_21);
return x_33;
}
else
{
obj* x_34; 
lean::dec(x_4);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_23);
lean::cnstr_set(x_34, 1, x_21);
return x_34;
}
}
}
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::apply_5(x_2, x_10, x_3, x_4, x_11, x_9);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_15);
lean::cnstr_set(x_13, 0, x_16);
return x_13;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_13);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = lean::cnstr_get(x_7, 0);
lean::dec(x_22);
x_23 = !lean::is_exclusive(x_8);
if (x_23 == 0)
{
return x_7;
}
else
{
obj* x_24; uint8 x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_8, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_24);
lean::dec(x_8);
x_26 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_25);
lean::cnstr_set(x_7, 0, x_26);
return x_7;
}
}
else
{
obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_7, 1);
lean::inc(x_27);
lean::dec(x_7);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::dec_ref(x_8);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_27);
return x_32;
}
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 0);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::mk_string("/--");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = lean::mk_string("-/");
x_6 = l_Lean_Parser_symbol_tokens___rarg(x_5, x_2);
lean::dec(x_5);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_4);
lean::dec(x_6);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_8);
lean::dec(x_8);
lean::dec(x_3);
x_10 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_5);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_7, x_1, x_2, x_3, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_9, 2);
x_14 = lean::cnstr_get(x_9, 0);
lean::dec(x_14);
x_15 = 0;
x_16 = lean::box(x_15);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 0, x_16);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_9);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 2);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_17, 1);
lean::dec(x_20);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_17, 2, x_21);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_8, 0, x_17);
return x_8;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set(x_8, 0, x_24);
return x_8;
}
}
else
{
uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_17);
x_25 = 1;
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = lean::box(x_25);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_5);
lean::cnstr_set(x_28, 2, x_26);
lean::cnstr_set(x_8, 0, x_28);
return x_8;
}
}
else
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_9, 1);
x_30 = lean::cnstr_get(x_9, 2);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_9);
x_31 = 0;
x_32 = lean::box(x_31);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_4);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 lean::cnstr_release(x_34, 2);
 x_36 = x_34;
} else {
 lean::dec_ref(x_34);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_5);
lean::cnstr_set(x_38, 2, x_37);
lean::cnstr_set(x_8, 0, x_38);
return x_8;
}
else
{
uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_34);
x_39 = 1;
x_40 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_41 = lean::box(x_39);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_40);
lean::cnstr_set(x_8, 0, x_42);
return x_8;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_43 = lean::cnstr_get(x_8, 1);
lean::inc(x_43);
lean::dec(x_8);
x_44 = lean::cnstr_get(x_9, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_9, 2);
lean::inc(x_45);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_46 = x_9;
} else {
 lean::dec_ref(x_9);
 x_46 = lean::box(0);
}
x_47 = 0;
x_48 = lean::box(x_47);
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_46;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
lean::cnstr_set(x_49, 2, x_4);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 lean::cnstr_release(x_50, 2);
 x_52 = x_50;
} else {
 lean::dec_ref(x_50);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_5);
lean::cnstr_set(x_54, 2, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_43);
return x_55;
}
else
{
uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_50);
x_56 = 1;
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = lean::box(x_56);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_5);
lean::cnstr_set(x_59, 2, x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_43);
return x_60;
}
}
}
else
{
uint8 x_61; 
lean::dec(x_9);
lean::dec(x_4);
x_61 = !lean::is_exclusive(x_8);
if (x_61 == 0)
{
obj* x_62; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_8, 0);
lean::dec(x_62);
x_63 = 1;
x_64 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_65 = lean::box(x_63);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_5);
lean::cnstr_set(x_66, 2, x_64);
lean::cnstr_set(x_8, 0, x_66);
return x_8;
}
else
{
obj* x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_67 = lean::cnstr_get(x_8, 1);
lean::inc(x_67);
lean::dec(x_8);
x_68 = 1;
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = lean::box(x_68);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
lean::cnstr_set(x_71, 2, x_69);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_67);
return x_72;
}
}
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_4);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(x_1, x_2, x_3, x_6, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_4);
x_15 = lean::box(0);
x_16 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_16, x_17, x_14, x_15, x_2, x_3, x_12, x_11);
lean::dec(x_14);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::cnstr_get(x_18, 1);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_20);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
lean::free_heap_obj(x_18);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_23, 2);
lean::inc(x_25);
lean::dec(x_23);
x_26 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_24, x_21);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_28);
lean::cnstr_set(x_26, 0, x_29);
return x_26;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_26);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_23);
if (x_34 == 0)
{
lean::cnstr_set(x_18, 0, x_23);
return x_18;
}
else
{
obj* x_35; uint8 x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_23, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
lean::inc(x_35);
lean::dec(x_23);
x_37 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
lean::cnstr_set(x_18, 0, x_37);
return x_18;
}
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_18, 0);
x_39 = lean::cnstr_get(x_18, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_18);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_38);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 2);
lean::inc(x_43);
lean::dec(x_41);
x_44 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_42, x_39);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_45);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
else
{
obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_52 = x_41;
} else {
 lean::dec_ref(x_41);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_51);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_39);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_4);
x_55 = !lean::is_exclusive(x_7);
if (x_55 == 0)
{
obj* x_56; obj* x_57; uint8 x_58; 
x_56 = lean::cnstr_get(x_7, 1);
x_57 = lean::cnstr_get(x_7, 0);
lean::dec(x_57);
x_58 = !lean::is_exclusive(x_8);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_8, 2);
x_60 = lean::cnstr_get(x_8, 0);
lean::dec(x_60);
x_61 = lean::box(0);
lean::cnstr_set(x_8, 2, x_6);
lean::cnstr_set(x_8, 0, x_61);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_8);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; uint8 x_67; 
lean::free_heap_obj(x_7);
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 2);
lean::inc(x_65);
lean::dec(x_63);
x_66 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_64, x_56);
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_66, 0);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_68);
lean::cnstr_set(x_66, 0, x_69);
return x_66;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_66, 0);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_66);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_70);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8 x_74; 
x_74 = !lean::is_exclusive(x_63);
if (x_74 == 0)
{
lean::cnstr_set(x_7, 0, x_63);
return x_7;
}
else
{
obj* x_75; uint8 x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_63, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
lean::inc(x_75);
lean::dec(x_63);
x_77 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_76);
lean::cnstr_set(x_7, 0, x_77);
return x_7;
}
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_8, 1);
x_79 = lean::cnstr_get(x_8, 2);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_8);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_78);
lean::cnstr_set(x_81, 2, x_6);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::free_heap_obj(x_7);
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_83, 2);
lean::inc(x_85);
lean::dec(x_83);
x_86 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_84, x_56);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_87);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
return x_91;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; obj* x_95; 
x_92 = lean::cnstr_get(x_83, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_94 = x_83;
} else {
 lean::dec_ref(x_83);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
lean::cnstr_set(x_7, 0, x_95);
return x_7;
}
}
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_96 = lean::cnstr_get(x_7, 1);
lean::inc(x_96);
lean::dec(x_7);
x_97 = lean::cnstr_get(x_8, 1);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_8, 2);
lean::inc(x_98);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_99 = x_8;
} else {
 lean::dec_ref(x_8);
 x_99 = lean::box(0);
}
x_100 = lean::box(0);
if (lean::is_scalar(x_99)) {
 x_101 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_101 = x_99;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
lean::cnstr_set(x_101, 2, x_6);
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_101);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_103, 2);
lean::inc(x_105);
lean::dec(x_103);
x_106 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_104, x_96);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_106, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_109 = x_106;
} else {
 lean::dec_ref(x_106);
 x_109 = lean::box(0);
}
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_107);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_108);
return x_111;
}
else
{
obj* x_112; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; 
x_112 = lean::cnstr_get(x_103, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*1);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_114 = x_103;
} else {
 lean::dec_ref(x_103);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_96);
return x_116;
}
}
}
}
else
{
uint8 x_117; 
lean::dec(x_4);
x_117 = !lean::is_exclusive(x_7);
if (x_117 == 0)
{
obj* x_118; obj* x_119; uint8 x_120; 
x_118 = lean::cnstr_get(x_7, 1);
x_119 = lean::cnstr_get(x_7, 0);
lean::dec(x_119);
x_120 = !lean::is_exclusive(x_8);
if (x_120 == 0)
{
obj* x_121; 
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_8);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; obj* x_123; obj* x_124; uint8 x_125; 
lean::free_heap_obj(x_7);
x_122 = lean::cnstr_get(x_121, 1);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_121, 2);
lean::inc(x_123);
lean::dec(x_121);
x_124 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_122, x_118);
x_125 = !lean::is_exclusive(x_124);
if (x_125 == 0)
{
obj* x_126; obj* x_127; 
x_126 = lean::cnstr_get(x_124, 0);
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_123, x_126);
lean::cnstr_set(x_124, 0, x_127);
return x_124;
}
else
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_124, 0);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_124);
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_123, x_128);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_129);
return x_131;
}
}
else
{
uint8 x_132; 
x_132 = !lean::is_exclusive(x_121);
if (x_132 == 0)
{
lean::cnstr_set(x_7, 0, x_121);
return x_7;
}
else
{
obj* x_133; uint8 x_134; obj* x_135; 
x_133 = lean::cnstr_get(x_121, 0);
x_134 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
lean::inc(x_133);
lean::dec(x_121);
x_135 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_134);
lean::cnstr_set(x_7, 0, x_135);
return x_7;
}
}
}
else
{
obj* x_136; uint8 x_137; obj* x_138; obj* x_139; 
x_136 = lean::cnstr_get(x_8, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_136);
lean::dec(x_8);
x_138 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_138, 0, x_136);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_137);
x_139 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
lean::free_heap_obj(x_7);
x_140 = lean::cnstr_get(x_139, 1);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_139, 2);
lean::inc(x_141);
lean::dec(x_139);
x_142 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_140, x_118);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_143);
if (lean::is_scalar(x_145)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_145;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_144);
return x_147;
}
else
{
obj* x_148; uint8 x_149; obj* x_150; obj* x_151; 
x_148 = lean::cnstr_get(x_139, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get_scalar<uint8>(x_139, sizeof(void*)*1);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 x_150 = x_139;
} else {
 lean::dec_ref(x_139);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*1, x_149);
lean::cnstr_set(x_7, 0, x_151);
return x_7;
}
}
}
else
{
obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; 
x_152 = lean::cnstr_get(x_7, 1);
lean::inc(x_152);
lean::dec(x_7);
x_153 = lean::cnstr_get(x_8, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_155 = x_8;
} else {
 lean::dec_ref(x_8);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_157, 2);
lean::inc(x_159);
lean::dec(x_157);
x_160 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_158, x_152);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_160, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 lean::cnstr_release(x_160, 1);
 x_163 = x_160;
} else {
 lean::dec_ref(x_160);
 x_163 = lean::box(0);
}
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_159, x_161);
if (lean::is_scalar(x_163)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_163;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_162);
return x_165;
}
else
{
obj* x_166; uint8 x_167; obj* x_168; obj* x_169; obj* x_170; 
x_166 = lean::cnstr_get(x_157, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 x_168 = x_157;
} else {
 lean::dec_ref(x_157);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_167);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_152);
return x_170;
}
}
}
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_MonadParsec_many_x27___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__6(x_1, x_3, x_4, x_5, x_6);
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
obj* _init_l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("/--");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::mk_string("-/");
lean::inc(x_10);
x_11 = l_String_quote(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_17, 0, x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 2);
lean::closure_set(x_18, 0, x_16);
lean::closure_set(x_18, 1, x_17);
x_19 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_8);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_18);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_command_docComment;
x_27 = l_Lean_Parser_command_docComment_HasView;
x_28 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_26, x_25, x_27);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_28;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
lean::inc(x_5);
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__2(x_7, x_1, x_2, x_3, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_9, 2);
x_14 = lean::cnstr_get(x_9, 0);
lean::dec(x_14);
x_15 = 0;
x_16 = lean::box(x_15);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 0, x_16);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_9);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 2);
lean::dec(x_19);
x_20 = lean::cnstr_get(x_17, 1);
lean::dec(x_20);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_17, 2, x_21);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_8, 0, x_17);
return x_8;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set(x_8, 0, x_24);
return x_8;
}
}
else
{
uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_17);
x_25 = 1;
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = lean::box(x_25);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_5);
lean::cnstr_set(x_28, 2, x_26);
lean::cnstr_set(x_8, 0, x_28);
return x_8;
}
}
else
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_9, 1);
x_30 = lean::cnstr_get(x_9, 2);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_9);
x_31 = 0;
x_32 = lean::box(x_31);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_4);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 lean::cnstr_release(x_34, 2);
 x_36 = x_34;
} else {
 lean::dec_ref(x_34);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_5);
lean::cnstr_set(x_38, 2, x_37);
lean::cnstr_set(x_8, 0, x_38);
return x_8;
}
else
{
uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_34);
x_39 = 1;
x_40 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_41 = lean::box(x_39);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
lean::cnstr_set(x_42, 2, x_40);
lean::cnstr_set(x_8, 0, x_42);
return x_8;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_43 = lean::cnstr_get(x_8, 1);
lean::inc(x_43);
lean::dec(x_8);
x_44 = lean::cnstr_get(x_9, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_9, 2);
lean::inc(x_45);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_46 = x_9;
} else {
 lean::dec_ref(x_9);
 x_46 = lean::box(0);
}
x_47 = 0;
x_48 = lean::box(x_47);
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_46;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
lean::cnstr_set(x_49, 2, x_4);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 1);
 lean::cnstr_release(x_50, 2);
 x_52 = x_50;
} else {
 lean::dec_ref(x_50);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_5);
lean::cnstr_set(x_54, 2, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_43);
return x_55;
}
else
{
uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_50);
x_56 = 1;
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = lean::box(x_56);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_5);
lean::cnstr_set(x_59, 2, x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_43);
return x_60;
}
}
}
else
{
uint8 x_61; 
lean::dec(x_9);
lean::dec(x_4);
x_61 = !lean::is_exclusive(x_8);
if (x_61 == 0)
{
obj* x_62; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_8, 0);
lean::dec(x_62);
x_63 = 1;
x_64 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_65 = lean::box(x_63);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_5);
lean::cnstr_set(x_66, 2, x_64);
lean::cnstr_set(x_8, 0, x_66);
return x_8;
}
else
{
obj* x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_67 = lean::cnstr_get(x_8, 1);
lean::inc(x_67);
lean::dec(x_8);
x_68 = 1;
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = lean::box(x_68);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_5);
lean::cnstr_set(x_71, 2, x_69);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_67);
return x_72;
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_67; obj* x_68; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_13 = x_3;
} else {
 lean::dec_ref(x_3);
 x_13 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
x_67 = lean::apply_4(x_11, x_4, x_5, x_6, x_7);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
lean::dec(x_67);
x_14 = x_68;
x_15 = x_69;
goto block_66;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_70; 
x_70 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (x_70 == 0)
{
obj* x_71; uint8 x_72; 
x_71 = lean::cnstr_get(x_67, 1);
lean::inc(x_71);
lean::dec(x_67);
x_72 = !lean::is_exclusive(x_68);
if (x_72 == 0)
{
uint8 x_73; 
x_73 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_73);
x_14 = x_68;
x_15 = x_71;
goto block_66;
}
else
{
obj* x_74; uint8 x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_68, 0);
lean::inc(x_74);
lean::dec(x_68);
x_75 = 0;
x_76 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_75);
x_14 = x_76;
x_15 = x_71;
goto block_66;
}
}
else
{
obj* x_77; uint8 x_78; 
x_77 = lean::cnstr_get(x_67, 1);
lean::inc(x_77);
lean::dec(x_67);
x_78 = !lean::is_exclusive(x_68);
if (x_78 == 0)
{
uint8 x_79; 
x_79 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_79);
x_14 = x_68;
x_15 = x_77;
goto block_66;
}
else
{
obj* x_80; uint8 x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_68, 0);
lean::inc(x_80);
lean::dec(x_68);
x_81 = 1;
x_82 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*1, x_81);
x_14 = x_82;
x_15 = x_77;
goto block_66;
}
}
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_68, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_83, 3);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; uint8 x_86; 
x_85 = lean::cnstr_get(x_67, 1);
lean::inc(x_85);
lean::dec(x_67);
x_86 = !lean::is_exclusive(x_68);
if (x_86 == 0)
{
uint8 x_87; obj* x_88; uint8 x_89; 
x_87 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
x_88 = lean::cnstr_get(x_68, 0);
lean::dec(x_88);
x_89 = !lean::is_exclusive(x_83);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_90 = lean::cnstr_get(x_83, 3);
lean::dec(x_90);
x_91 = lean::box(3);
lean::inc(x_2);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_2);
x_93 = l_List_reverse___rarg(x_92);
lean::inc(x_1);
x_94 = l_Lean_Parser_Syntax_mkNode(x_1, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_83, 3, x_95);
if (x_87 == 0)
{
uint8 x_96; 
x_96 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_96);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_97; 
x_97 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_97);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_83, 0);
x_99 = lean::cnstr_get(x_83, 1);
x_100 = lean::cnstr_get(x_83, 2);
lean::inc(x_100);
lean::inc(x_99);
lean::inc(x_98);
lean::dec(x_83);
x_101 = lean::box(3);
lean::inc(x_2);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_2);
x_103 = l_List_reverse___rarg(x_102);
lean::inc(x_1);
x_104 = l_Lean_Parser_Syntax_mkNode(x_1, x_103);
x_105 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
x_106 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_106, 0, x_98);
lean::cnstr_set(x_106, 1, x_99);
lean::cnstr_set(x_106, 2, x_100);
lean::cnstr_set(x_106, 3, x_105);
if (x_87 == 0)
{
uint8 x_107; 
x_107 = 0;
lean::cnstr_set(x_68, 0, x_106);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_107);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_108; 
x_108 = 1;
lean::cnstr_set(x_68, 0, x_106);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_108);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
}
}
else
{
uint8 x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_109 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
lean::dec(x_68);
x_110 = lean::cnstr_get(x_83, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_83, 1);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_83, 2);
lean::inc(x_112);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 lean::cnstr_release(x_83, 2);
 lean::cnstr_release(x_83, 3);
 x_113 = x_83;
} else {
 lean::dec_ref(x_83);
 x_113 = lean::box(0);
}
x_114 = lean::box(3);
lean::inc(x_2);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_2);
x_116 = l_List_reverse___rarg(x_115);
lean::inc(x_1);
x_117 = l_Lean_Parser_Syntax_mkNode(x_1, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
if (lean::is_scalar(x_113)) {
 x_119 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_119 = x_113;
}
lean::cnstr_set(x_119, 0, x_110);
lean::cnstr_set(x_119, 1, x_111);
lean::cnstr_set(x_119, 2, x_112);
lean::cnstr_set(x_119, 3, x_118);
if (x_109 == 0)
{
uint8 x_120; obj* x_121; 
x_120 = 0;
x_121 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_120);
x_14 = x_121;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_122; obj* x_123; 
x_122 = 1;
x_123 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_122);
x_14 = x_123;
x_15 = x_85;
goto block_66;
}
}
}
else
{
obj* x_124; uint8 x_125; 
x_124 = lean::cnstr_get(x_67, 1);
lean::inc(x_124);
lean::dec(x_67);
x_125 = !lean::is_exclusive(x_68);
if (x_125 == 0)
{
uint8 x_126; obj* x_127; uint8 x_128; 
x_126 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
x_127 = lean::cnstr_get(x_68, 0);
lean::dec(x_127);
x_128 = !lean::is_exclusive(x_83);
if (x_128 == 0)
{
obj* x_129; uint8 x_130; 
x_129 = lean::cnstr_get(x_83, 3);
lean::dec(x_129);
x_130 = !lean::is_exclusive(x_84);
if (x_130 == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_131 = lean::cnstr_get(x_84, 0);
lean::inc(x_2);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_2);
x_133 = l_List_reverse___rarg(x_132);
lean::inc(x_1);
x_134 = l_Lean_Parser_Syntax_mkNode(x_1, x_133);
lean::cnstr_set(x_84, 0, x_134);
if (x_126 == 0)
{
uint8 x_135; 
x_135 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_135);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_136; 
x_136 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_136);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
else
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_137 = lean::cnstr_get(x_84, 0);
lean::inc(x_137);
lean::dec(x_84);
lean::inc(x_2);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_2);
x_139 = l_List_reverse___rarg(x_138);
lean::inc(x_1);
x_140 = l_Lean_Parser_Syntax_mkNode(x_1, x_139);
x_141 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_83, 3, x_141);
if (x_126 == 0)
{
uint8 x_142; 
x_142 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_142);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_143; 
x_143 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_143);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_144 = lean::cnstr_get(x_83, 0);
x_145 = lean::cnstr_get(x_83, 1);
x_146 = lean::cnstr_get(x_83, 2);
lean::inc(x_146);
lean::inc(x_145);
lean::inc(x_144);
lean::dec(x_83);
x_147 = lean::cnstr_get(x_84, 0);
lean::inc(x_147);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 x_148 = x_84;
} else {
 lean::dec_ref(x_84);
 x_148 = lean::box(0);
}
lean::inc(x_2);
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_147);
lean::cnstr_set(x_149, 1, x_2);
x_150 = l_List_reverse___rarg(x_149);
lean::inc(x_1);
x_151 = l_Lean_Parser_Syntax_mkNode(x_1, x_150);
if (lean::is_scalar(x_148)) {
 x_152 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_152 = x_148;
}
lean::cnstr_set(x_152, 0, x_151);
x_153 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_153, 0, x_144);
lean::cnstr_set(x_153, 1, x_145);
lean::cnstr_set(x_153, 2, x_146);
lean::cnstr_set(x_153, 3, x_152);
if (x_126 == 0)
{
uint8 x_154; 
x_154 = 0;
lean::cnstr_set(x_68, 0, x_153);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_154);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_155; 
x_155 = 1;
lean::cnstr_set(x_68, 0, x_153);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_155);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
}
else
{
uint8 x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_156 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
lean::dec(x_68);
x_157 = lean::cnstr_get(x_83, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_83, 1);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_83, 2);
lean::inc(x_159);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 lean::cnstr_release(x_83, 2);
 lean::cnstr_release(x_83, 3);
 x_160 = x_83;
} else {
 lean::dec_ref(x_83);
 x_160 = lean::box(0);
}
x_161 = lean::cnstr_get(x_84, 0);
lean::inc(x_161);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 x_162 = x_84;
} else {
 lean::dec_ref(x_84);
 x_162 = lean::box(0);
}
lean::inc(x_2);
x_163 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_2);
x_164 = l_List_reverse___rarg(x_163);
lean::inc(x_1);
x_165 = l_Lean_Parser_Syntax_mkNode(x_1, x_164);
if (lean::is_scalar(x_162)) {
 x_166 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_166 = x_162;
}
lean::cnstr_set(x_166, 0, x_165);
if (lean::is_scalar(x_160)) {
 x_167 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_167 = x_160;
}
lean::cnstr_set(x_167, 0, x_157);
lean::cnstr_set(x_167, 1, x_158);
lean::cnstr_set(x_167, 2, x_159);
lean::cnstr_set(x_167, 3, x_166);
if (x_156 == 0)
{
uint8 x_168; obj* x_169; 
x_168 = 0;
x_169 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_168);
x_14 = x_169;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_170; obj* x_171; 
x_170 = 1;
x_171 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_171, 0, x_167);
lean::cnstr_set_scalar(x_171, sizeof(void*)*1, x_170);
x_14 = x_171;
x_15 = x_124;
goto block_66;
}
}
}
}
}
block_66:
{
if (lean::obj_tag(x_14) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_14);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_14, 0);
x_18 = lean::cnstr_get(x_14, 2);
if (lean::is_scalar(x_13)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_13;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_2);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_14, 2, x_20);
lean::cnstr_set(x_14, 0, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_14);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_21, 2);
lean::inc(x_24);
lean::dec(x_21);
x_25 = l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(x_1, x_22, x_12, x_4, x_5, x_23, x_15);
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_27);
lean::cnstr_set(x_25, 0, x_28);
return x_25;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_25, 0);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_25);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_29);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8 x_33; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_33 = !lean::is_exclusive(x_21);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_21);
lean::cnstr_set(x_34, 1, x_15);
return x_34;
}
else
{
obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_21, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
lean::inc(x_35);
lean::dec(x_21);
x_37 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_15);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_14, 0);
x_40 = lean::cnstr_get(x_14, 1);
x_41 = lean::cnstr_get(x_14, 2);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_14);
if (lean::is_scalar(x_13)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_13;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_2);
x_43 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_40);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
lean::dec(x_45);
x_49 = l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(x_1, x_46, x_12, x_4, x_5, x_47, x_15);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_50);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
else
{
obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_55 = lean::cnstr_get(x_45, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_57 = x_45;
} else {
 lean::dec_ref(x_45);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_15);
return x_59;
}
}
}
else
{
uint8 x_60; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_60 = !lean::is_exclusive(x_14);
if (x_60 == 0)
{
obj* x_61; 
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_14);
lean::cnstr_set(x_61, 1, x_15);
return x_61;
}
else
{
obj* x_62; uint8 x_63; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_14, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::inc(x_62);
lean::dec(x_14);
x_64 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_15);
return x_65;
}
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::box(0);
lean::inc(x_1);
x_8 = l_List_mfoldl___main___at_Lean_Parser_command_docComment_Parser___spec__3(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 2);
x_15 = l_List_reverse___rarg(x_13);
x_16 = l_Lean_Parser_Syntax_mkNode(x_1, x_15);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_9, 2, x_17);
lean::cnstr_set(x_9, 0, x_16);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
lean::cnstr_set(x_8, 0, x_18);
return x_8;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_9, 0);
x_20 = lean::cnstr_get(x_9, 1);
x_21 = lean::cnstr_get(x_9, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_9);
x_22 = l_List_reverse___rarg(x_19);
x_23 = l_Lean_Parser_Syntax_mkNode(x_1, x_22);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_20);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_25);
lean::cnstr_set(x_8, 0, x_26);
return x_8;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_27 = lean::cnstr_get(x_8, 1);
lean::inc(x_27);
lean::dec(x_8);
x_28 = lean::cnstr_get(x_9, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_9, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_9, 2);
lean::inc(x_30);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_31 = x_9;
} else {
 lean::dec_ref(x_9);
 x_31 = lean::box(0);
}
x_32 = l_List_reverse___rarg(x_28);
x_33 = l_Lean_Parser_Syntax_mkNode(x_1, x_32);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_29);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_27);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_1);
x_38 = !lean::is_exclusive(x_8);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
x_39 = lean::cnstr_get(x_8, 0);
lean::dec(x_39);
x_40 = !lean::is_exclusive(x_9);
if (x_40 == 0)
{
return x_8;
}
else
{
obj* x_41; uint8 x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_9, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_41);
lean::dec(x_9);
x_43 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_42);
lean::cnstr_set(x_8, 0, x_43);
return x_8;
}
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_8, 1);
lean::inc(x_44);
lean::dec(x_8);
x_45 = lean::cnstr_get(x_9, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_47 = x_9;
} else {
 lean::dec_ref(x_9);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
return x_49;
}
}
}
}
obj* l_Lean_Parser_command_docComment_Parser___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_4);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(x_1, x_2, x_3, x_6, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_4);
x_15 = lean::box(0);
x_16 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_16, x_17, x_14, x_15, x_2, x_3, x_12, x_11);
lean::dec(x_14);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::cnstr_get(x_18, 1);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_20);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
lean::free_heap_obj(x_18);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_23, 2);
lean::inc(x_25);
lean::dec(x_23);
x_26 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_24, x_21);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 0);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_28);
lean::cnstr_set(x_26, 0, x_29);
return x_26;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_26);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_30);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_23);
if (x_34 == 0)
{
lean::cnstr_set(x_18, 0, x_23);
return x_18;
}
else
{
obj* x_35; uint8 x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_23, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
lean::inc(x_35);
lean::dec(x_23);
x_37 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
lean::cnstr_set(x_18, 0, x_37);
return x_18;
}
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_18, 0);
x_39 = lean::cnstr_get(x_18, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_18);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_38);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 2);
lean::inc(x_43);
lean::dec(x_41);
x_44 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_42, x_39);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_45);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
else
{
obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_52 = x_41;
} else {
 lean::dec_ref(x_41);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_51);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_39);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_4);
x_55 = !lean::is_exclusive(x_7);
if (x_55 == 0)
{
obj* x_56; obj* x_57; uint8 x_58; 
x_56 = lean::cnstr_get(x_7, 1);
x_57 = lean::cnstr_get(x_7, 0);
lean::dec(x_57);
x_58 = !lean::is_exclusive(x_8);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_8, 2);
x_60 = lean::cnstr_get(x_8, 0);
lean::dec(x_60);
x_61 = lean::box(0);
lean::cnstr_set(x_8, 2, x_6);
lean::cnstr_set(x_8, 0, x_61);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_8);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; uint8 x_67; 
lean::free_heap_obj(x_7);
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 2);
lean::inc(x_65);
lean::dec(x_63);
x_66 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_64, x_56);
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_66, 0);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_68);
lean::cnstr_set(x_66, 0, x_69);
return x_66;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_66, 0);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_66);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_70);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8 x_74; 
x_74 = !lean::is_exclusive(x_63);
if (x_74 == 0)
{
lean::cnstr_set(x_7, 0, x_63);
return x_7;
}
else
{
obj* x_75; uint8 x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_63, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
lean::inc(x_75);
lean::dec(x_63);
x_77 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_76);
lean::cnstr_set(x_7, 0, x_77);
return x_7;
}
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_8, 1);
x_79 = lean::cnstr_get(x_8, 2);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_8);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_78);
lean::cnstr_set(x_81, 2, x_6);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::free_heap_obj(x_7);
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_83, 2);
lean::inc(x_85);
lean::dec(x_83);
x_86 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_84, x_56);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_87);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
return x_91;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; obj* x_95; 
x_92 = lean::cnstr_get(x_83, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_94 = x_83;
} else {
 lean::dec_ref(x_83);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
lean::cnstr_set(x_7, 0, x_95);
return x_7;
}
}
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_96 = lean::cnstr_get(x_7, 1);
lean::inc(x_96);
lean::dec(x_7);
x_97 = lean::cnstr_get(x_8, 1);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_8, 2);
lean::inc(x_98);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_99 = x_8;
} else {
 lean::dec_ref(x_8);
 x_99 = lean::box(0);
}
x_100 = lean::box(0);
if (lean::is_scalar(x_99)) {
 x_101 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_101 = x_99;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
lean::cnstr_set(x_101, 2, x_6);
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_101);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_103, 2);
lean::inc(x_105);
lean::dec(x_103);
x_106 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_104, x_96);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_106, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_109 = x_106;
} else {
 lean::dec_ref(x_106);
 x_109 = lean::box(0);
}
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_107);
if (lean::is_scalar(x_109)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_109;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_108);
return x_111;
}
else
{
obj* x_112; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; 
x_112 = lean::cnstr_get(x_103, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*1);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_114 = x_103;
} else {
 lean::dec_ref(x_103);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_96);
return x_116;
}
}
}
}
else
{
uint8 x_117; 
lean::dec(x_4);
x_117 = !lean::is_exclusive(x_7);
if (x_117 == 0)
{
obj* x_118; obj* x_119; uint8 x_120; 
x_118 = lean::cnstr_get(x_7, 1);
x_119 = lean::cnstr_get(x_7, 0);
lean::dec(x_119);
x_120 = !lean::is_exclusive(x_8);
if (x_120 == 0)
{
obj* x_121; 
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_8);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; obj* x_123; obj* x_124; uint8 x_125; 
lean::free_heap_obj(x_7);
x_122 = lean::cnstr_get(x_121, 1);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_121, 2);
lean::inc(x_123);
lean::dec(x_121);
x_124 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_122, x_118);
x_125 = !lean::is_exclusive(x_124);
if (x_125 == 0)
{
obj* x_126; obj* x_127; 
x_126 = lean::cnstr_get(x_124, 0);
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_123, x_126);
lean::cnstr_set(x_124, 0, x_127);
return x_124;
}
else
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_124, 0);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_124);
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_123, x_128);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_129);
return x_131;
}
}
else
{
uint8 x_132; 
x_132 = !lean::is_exclusive(x_121);
if (x_132 == 0)
{
lean::cnstr_set(x_7, 0, x_121);
return x_7;
}
else
{
obj* x_133; uint8 x_134; obj* x_135; 
x_133 = lean::cnstr_get(x_121, 0);
x_134 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
lean::inc(x_133);
lean::dec(x_121);
x_135 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_134);
lean::cnstr_set(x_7, 0, x_135);
return x_7;
}
}
}
else
{
obj* x_136; uint8 x_137; obj* x_138; obj* x_139; 
x_136 = lean::cnstr_get(x_8, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_136);
lean::dec(x_8);
x_138 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_138, 0, x_136);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_137);
x_139 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
lean::free_heap_obj(x_7);
x_140 = lean::cnstr_get(x_139, 1);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_139, 2);
lean::inc(x_141);
lean::dec(x_139);
x_142 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_140, x_118);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_143);
if (lean::is_scalar(x_145)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_145;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_144);
return x_147;
}
else
{
obj* x_148; uint8 x_149; obj* x_150; obj* x_151; 
x_148 = lean::cnstr_get(x_139, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get_scalar<uint8>(x_139, sizeof(void*)*1);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 x_150 = x_139;
} else {
 lean::dec_ref(x_139);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*1, x_149);
lean::cnstr_set(x_7, 0, x_151);
return x_7;
}
}
}
else
{
obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; 
x_152 = lean::cnstr_get(x_7, 1);
lean::inc(x_152);
lean::dec(x_7);
x_153 = lean::cnstr_get(x_8, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_155 = x_8;
} else {
 lean::dec_ref(x_8);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_157, 2);
lean::inc(x_159);
lean::dec(x_157);
x_160 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__5(x_2, x_3, x_158, x_152);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_160, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 lean::cnstr_release(x_160, 1);
 x_163 = x_160;
} else {
 lean::dec_ref(x_160);
 x_163 = lean::box(0);
}
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_159, x_161);
if (lean::is_scalar(x_163)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_163;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_162);
return x_165;
}
else
{
obj* x_166; uint8 x_167; obj* x_168; obj* x_169; obj* x_170; 
x_166 = lean::cnstr_get(x_157, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 x_168 = x_157;
} else {
 lean::dec_ref(x_157);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_167);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_152);
return x_170;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_docComment_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = lean::mk_string("/--");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("-/");
lean::inc(x_6);
x_7 = l_String_quote(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser___lambda__1___boxed), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_NotationSpec_symbolQuote_Parser_Lean_Parser_HasTokens___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__8___rarg___boxed), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasView___lambda__2), 6, 1);
lean::closure_set(x_13, 0, x_9);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__9___rarg), 6, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = l_String_trim(x_6);
lean::dec(x_6);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_14);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_5);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l_Lean_Parser_command_docComment_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_docComment;
x_6 = l_Lean_Parser_command_docComment_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_command_docComment_Parser___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_command_docComment_Parser___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_command_docComment_Parser___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_attrInstance() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("attrInstance");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_attrInstance_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
x_5 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_3);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_command_attrInstance;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::mk_string("NOTAnIdent");
lean::inc(x_2);
x_3 = l_Lean_Parser_Substring_ofString(x_2);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
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
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1;
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
x_6 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_5);
x_7 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_35; 
x_35 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; 
x_36 = l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3;
return x_36;
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; 
x_39 = lean::box(3);
x_2 = x_38;
x_3 = x_39;
goto block_34;
}
else
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_2 = x_41;
x_3 = x_40;
goto block_34;
}
}
block_34:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 1)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::box(3);
x_17 = l_Lean_Parser_Syntax_asNode___main(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; 
x_18 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_3, 0);
lean::inc(x_24);
lean::dec(x_3);
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_26 = l_Lean_Parser_Syntax_asNode___main(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; 
x_27 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_24);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; 
lean::dec(x_3);
x_33 = lean::box(0);
x_4 = x_33;
goto block_14;
}
block_14:
{
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2;
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_10);
x_12 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_attrInstance_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_5);
x_6 = l___private_init_lean_parser_token_4__ident_x27(x_5, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_7, 2);
lean::inc(x_11);
lean::dec(x_7);
x_12 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_9, x_5, x_10, x_8);
lean::dec(x_5);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_14);
lean::cnstr_set(x_12, 0, x_15);
return x_12;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_12);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_5);
x_20 = !lean::is_exclusive(x_6);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_6, 0);
lean::dec(x_21);
x_22 = !lean::is_exclusive(x_7);
if (x_22 == 0)
{
return x_6;
}
else
{
obj* x_23; uint8 x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_7, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_23);
lean::dec(x_7);
x_25 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_24);
lean::cnstr_set(x_6, 0, x_25);
return x_6;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_6, 1);
lean::inc(x_26);
lean::dec(x_6);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_29 = x_7;
} else {
 lean::dec_ref(x_7);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_26);
return x_31;
}
}
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_88; obj* x_89; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_3, x_10);
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_4);
x_88 = lean::apply_4(x_1, x_4, x_5, x_6, x_7);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; 
x_90 = lean::cnstr_get(x_88, 1);
lean::inc(x_90);
lean::dec(x_88);
x_12 = x_89;
x_13 = x_90;
goto block_87;
}
else
{
obj* x_91; obj* x_92; 
x_91 = lean::cnstr_get(x_89, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_91, 3);
lean::inc(x_92);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; uint8 x_94; 
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
x_94 = !lean::is_exclusive(x_89);
if (x_94 == 0)
{
uint8 x_95; obj* x_96; uint8 x_97; 
x_95 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
x_96 = lean::cnstr_get(x_89, 0);
lean::dec(x_96);
x_97 = !lean::is_exclusive(x_91);
if (x_97 == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_98 = lean::cnstr_get(x_91, 3);
lean::dec(x_98);
x_99 = lean::box(3);
lean::inc(x_2);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_2);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_100);
x_102 = l_List_reverse___rarg(x_101);
x_103 = l_Lean_Parser_noKind;
x_104 = l_Lean_Parser_Syntax_mkNode(x_103, x_102);
x_105 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_91, 3, x_105);
if (x_95 == 0)
{
uint8 x_106; 
x_106 = 0;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_106);
x_12 = x_89;
x_13 = x_93;
goto block_87;
}
else
{
uint8 x_107; 
x_107 = 1;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_107);
x_12 = x_89;
x_13 = x_93;
goto block_87;
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_108 = lean::cnstr_get(x_91, 0);
x_109 = lean::cnstr_get(x_91, 1);
x_110 = lean::cnstr_get(x_91, 2);
lean::inc(x_110);
lean::inc(x_109);
lean::inc(x_108);
lean::dec(x_91);
x_111 = lean::box(3);
lean::inc(x_2);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_2);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set(x_113, 1, x_112);
x_114 = l_List_reverse___rarg(x_113);
x_115 = l_Lean_Parser_noKind;
x_116 = l_Lean_Parser_Syntax_mkNode(x_115, x_114);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
x_118 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_118, 0, x_108);
lean::cnstr_set(x_118, 1, x_109);
lean::cnstr_set(x_118, 2, x_110);
lean::cnstr_set(x_118, 3, x_117);
if (x_95 == 0)
{
uint8 x_119; 
x_119 = 0;
lean::cnstr_set(x_89, 0, x_118);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_119);
x_12 = x_89;
x_13 = x_93;
goto block_87;
}
else
{
uint8 x_120; 
x_120 = 1;
lean::cnstr_set(x_89, 0, x_118);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_120);
x_12 = x_89;
x_13 = x_93;
goto block_87;
}
}
}
else
{
uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_121 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
lean::dec(x_89);
x_122 = lean::cnstr_get(x_91, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_91, 1);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_91, 2);
lean::inc(x_124);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 lean::cnstr_release(x_91, 2);
 lean::cnstr_release(x_91, 3);
 x_125 = x_91;
} else {
 lean::dec_ref(x_91);
 x_125 = lean::box(0);
}
x_126 = lean::box(3);
lean::inc(x_2);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_2);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_126);
lean::cnstr_set(x_128, 1, x_127);
x_129 = l_List_reverse___rarg(x_128);
x_130 = l_Lean_Parser_noKind;
x_131 = l_Lean_Parser_Syntax_mkNode(x_130, x_129);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
if (lean::is_scalar(x_125)) {
 x_133 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_133 = x_125;
}
lean::cnstr_set(x_133, 0, x_122);
lean::cnstr_set(x_133, 1, x_123);
lean::cnstr_set(x_133, 2, x_124);
lean::cnstr_set(x_133, 3, x_132);
if (x_121 == 0)
{
uint8 x_134; obj* x_135; 
x_134 = 0;
x_135 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_134);
x_12 = x_135;
x_13 = x_93;
goto block_87;
}
else
{
uint8 x_136; obj* x_137; 
x_136 = 1;
x_137 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_137, 0, x_133);
lean::cnstr_set_scalar(x_137, sizeof(void*)*1, x_136);
x_12 = x_137;
x_13 = x_93;
goto block_87;
}
}
}
else
{
obj* x_138; uint8 x_139; 
x_138 = lean::cnstr_get(x_88, 1);
lean::inc(x_138);
lean::dec(x_88);
x_139 = !lean::is_exclusive(x_89);
if (x_139 == 0)
{
uint8 x_140; obj* x_141; uint8 x_142; 
x_140 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
x_141 = lean::cnstr_get(x_89, 0);
lean::dec(x_141);
x_142 = !lean::is_exclusive(x_91);
if (x_142 == 0)
{
obj* x_143; uint8 x_144; 
x_143 = lean::cnstr_get(x_91, 3);
lean::dec(x_143);
x_144 = !lean::is_exclusive(x_92);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_92, 0);
lean::inc(x_2);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_2);
x_147 = lean::box(3);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_146);
x_149 = l_List_reverse___rarg(x_148);
x_150 = l_Lean_Parser_noKind;
x_151 = l_Lean_Parser_Syntax_mkNode(x_150, x_149);
lean::cnstr_set(x_92, 0, x_151);
if (x_140 == 0)
{
uint8 x_152; 
x_152 = 0;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_152);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
else
{
uint8 x_153; 
x_153 = 1;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_153);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
}
else
{
obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_154 = lean::cnstr_get(x_92, 0);
lean::inc(x_154);
lean::dec(x_92);
lean::inc(x_2);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_2);
x_156 = lean::box(3);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_155);
x_158 = l_List_reverse___rarg(x_157);
x_159 = l_Lean_Parser_noKind;
x_160 = l_Lean_Parser_Syntax_mkNode(x_159, x_158);
x_161 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_91, 3, x_161);
if (x_140 == 0)
{
uint8 x_162; 
x_162 = 0;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_162);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
else
{
uint8 x_163; 
x_163 = 1;
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_163);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_164 = lean::cnstr_get(x_91, 0);
x_165 = lean::cnstr_get(x_91, 1);
x_166 = lean::cnstr_get(x_91, 2);
lean::inc(x_166);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_91);
x_167 = lean::cnstr_get(x_92, 0);
lean::inc(x_167);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_168 = x_92;
} else {
 lean::dec_ref(x_92);
 x_168 = lean::box(0);
}
lean::inc(x_2);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set(x_169, 1, x_2);
x_170 = lean::box(3);
x_171 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_169);
x_172 = l_List_reverse___rarg(x_171);
x_173 = l_Lean_Parser_noKind;
x_174 = l_Lean_Parser_Syntax_mkNode(x_173, x_172);
if (lean::is_scalar(x_168)) {
 x_175 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_175 = x_168;
}
lean::cnstr_set(x_175, 0, x_174);
x_176 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_176, 0, x_164);
lean::cnstr_set(x_176, 1, x_165);
lean::cnstr_set(x_176, 2, x_166);
lean::cnstr_set(x_176, 3, x_175);
if (x_140 == 0)
{
uint8 x_177; 
x_177 = 0;
lean::cnstr_set(x_89, 0, x_176);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_177);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
else
{
uint8 x_178; 
x_178 = 1;
lean::cnstr_set(x_89, 0, x_176);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_178);
x_12 = x_89;
x_13 = x_138;
goto block_87;
}
}
}
else
{
uint8 x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_179 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
lean::dec(x_89);
x_180 = lean::cnstr_get(x_91, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_91, 1);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_91, 2);
lean::inc(x_182);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 lean::cnstr_release(x_91, 2);
 lean::cnstr_release(x_91, 3);
 x_183 = x_91;
} else {
 lean::dec_ref(x_91);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_92, 0);
lean::inc(x_184);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_185 = x_92;
} else {
 lean::dec_ref(x_92);
 x_185 = lean::box(0);
}
lean::inc(x_2);
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_184);
lean::cnstr_set(x_186, 1, x_2);
x_187 = lean::box(3);
x_188 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_186);
x_189 = l_List_reverse___rarg(x_188);
x_190 = l_Lean_Parser_noKind;
x_191 = l_Lean_Parser_Syntax_mkNode(x_190, x_189);
if (lean::is_scalar(x_185)) {
 x_192 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_192 = x_185;
}
lean::cnstr_set(x_192, 0, x_191);
if (lean::is_scalar(x_183)) {
 x_193 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_193 = x_183;
}
lean::cnstr_set(x_193, 0, x_180);
lean::cnstr_set(x_193, 1, x_181);
lean::cnstr_set(x_193, 2, x_182);
lean::cnstr_set(x_193, 3, x_192);
if (x_179 == 0)
{
uint8 x_194; obj* x_195; 
x_194 = 0;
x_195 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set_scalar(x_195, sizeof(void*)*1, x_194);
x_12 = x_195;
x_13 = x_138;
goto block_87;
}
else
{
uint8 x_196; obj* x_197; 
x_196 = 1;
x_197 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_197, 0, x_193);
lean::cnstr_set_scalar(x_197, sizeof(void*)*1, x_196);
x_12 = x_197;
x_13 = x_138;
goto block_87;
}
}
}
}
block_87:
{
if (lean::obj_tag(x_12) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
x_17 = lean::cnstr_get(x_12, 2);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_2);
lean::inc(x_18);
x_19 = l_List_reverse___rarg(x_18);
x_20 = l_Lean_Parser_noKind;
x_21 = l_Lean_Parser_Syntax_mkNode(x_20, x_19);
lean::inc(x_16);
x_22 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_1, x_18, x_11, x_4, x_5, x_16, x_13);
lean::dec(x_11);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
lean::dec(x_21);
lean::free_heap_obj(x_12);
lean::dec(x_16);
x_24 = !lean::is_exclusive(x_22);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_22, 0);
lean::dec(x_25);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
lean::cnstr_set(x_22, 0, x_26);
return x_22;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8 x_30; 
x_30 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_30 == 0)
{
uint8 x_31; 
x_31 = !lean::is_exclusive(x_22);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_22, 0);
lean::dec(x_32);
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_33, 2);
lean::inc(x_34);
lean::dec(x_33);
x_35 = l_mjoin___rarg___closed__1;
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_36, 0, x_34);
lean::closure_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_12, 2, x_37);
lean::cnstr_set(x_12, 0, x_21);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_12);
lean::cnstr_set(x_22, 0, x_38);
return x_22;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_22, 1);
lean::inc(x_39);
lean::dec(x_22);
x_40 = lean::cnstr_get(x_23, 0);
lean::inc(x_40);
lean::dec(x_23);
x_41 = lean::cnstr_get(x_40, 2);
lean::inc(x_41);
lean::dec(x_40);
x_42 = l_mjoin___rarg___closed__1;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_12, 2, x_44);
lean::cnstr_set(x_12, 0, x_21);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_12);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_39);
return x_46;
}
}
else
{
uint8 x_47; 
lean::dec(x_21);
lean::free_heap_obj(x_12);
lean::dec(x_16);
x_47 = !lean::is_exclusive(x_22);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_22, 0);
lean::dec(x_48);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
lean::cnstr_set(x_22, 0, x_49);
return x_22;
}
else
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::cnstr_get(x_22, 1);
lean::inc(x_50);
lean::dec(x_22);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_53 = lean::cnstr_get(x_12, 0);
x_54 = lean::cnstr_get(x_12, 1);
x_55 = lean::cnstr_get(x_12, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_12);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_2);
lean::inc(x_56);
x_57 = l_List_reverse___rarg(x_56);
x_58 = l_Lean_Parser_noKind;
x_59 = l_Lean_Parser_Syntax_mkNode(x_58, x_57);
lean::inc(x_54);
x_60 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_1, x_56, x_11, x_4, x_5, x_54, x_13);
lean::dec(x_11);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_59);
lean::dec(x_54);
x_62 = lean::cnstr_get(x_60, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_63 = x_60;
} else {
 lean::dec_ref(x_60);
 x_63 = lean::box(0);
}
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_61);
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_62);
return x_65;
}
else
{
uint8 x_66; 
x_66 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_60, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_68 = x_60;
} else {
 lean::dec_ref(x_60);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
x_70 = lean::cnstr_get(x_69, 2);
lean::inc(x_70);
lean::dec(x_69);
x_71 = l_mjoin___rarg___closed__1;
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_72, 0, x_70);
lean::closure_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_59);
lean::cnstr_set(x_74, 1, x_54);
lean::cnstr_set(x_74, 2, x_73);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_74);
if (lean::is_scalar(x_68)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_68;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_67);
return x_76;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_59);
lean::dec(x_54);
x_77 = lean::cnstr_get(x_60, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_78 = x_60;
} else {
 lean::dec_ref(x_60);
 x_78 = lean::box(0);
}
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_61);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_77);
return x_80;
}
}
}
}
else
{
uint8 x_81; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_81 = !lean::is_exclusive(x_12);
if (x_81 == 0)
{
obj* x_82; 
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_12);
lean::cnstr_set(x_82, 1, x_13);
return x_82;
}
else
{
obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_83 = lean::cnstr_get(x_12, 0);
x_84 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
lean::inc(x_83);
lean::dec(x_12);
x_85 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_13);
return x_86;
}
}
}
}
else
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
lean::dec(x_2);
lean::dec(x_1);
x_198 = lean::box(0);
x_199 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_200 = l_mjoin___rarg___closed__1;
x_201 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_199, x_200, x_198, x_198, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
return x_201;
}
}
}
obj* l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = lean::box(0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_6);
x_10 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_1, x_7, x_9, x_2, x_3, x_4, x_5);
lean::dec(x_9);
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_Parser_finishCommentBlock___closed__2;
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_12);
lean::cnstr_set(x_10, 0, x_14);
return x_10;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_10, 0);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_15);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_16);
return x_19;
}
}
}
obj* l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
x_6 = l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3(x_1, x_2, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_4);
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_6, 0);
lean::dec(x_9);
return x_6;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_6);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_6, 0);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_15, 2);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_mjoin___rarg___closed__1;
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_18, 0, x_16);
lean::closure_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_4);
lean::cnstr_set(x_21, 2, x_19);
lean::cnstr_set(x_6, 0, x_21);
return x_6;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_6, 1);
lean::inc(x_22);
lean::dec(x_6);
x_23 = lean::cnstr_get(x_7, 0);
lean::inc(x_23);
lean::dec(x_7);
x_24 = lean::cnstr_get(x_23, 2);
lean::inc(x_24);
lean::dec(x_23);
x_25 = l_mjoin___rarg___closed__1;
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
lean::cnstr_set(x_29, 2, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_4);
x_31 = !lean::is_exclusive(x_6);
if (x_31 == 0)
{
obj* x_32; 
x_32 = lean::cnstr_get(x_6, 0);
lean::dec(x_32);
return x_6;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_6, 1);
lean::inc(x_33);
lean::dec(x_6);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_maxPrec;
x_3 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_2);
x_4 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_1);
lean::dec(x_5);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___main___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = l_Lean_Parser_maxPrec;
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_attrInstance;
x_14 = l_Lean_Parser_command_attrInstance_HasView;
x_15 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_13, x_12, x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_15;
}
}
obj* _init_l_Lean_Parser_command_attrInstance_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* l_Lean_Parser_command_attrInstance_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_attrInstance;
x_6 = l_Lean_Parser_command_attrInstance_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_declAttributes() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declAttributes");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x27___elambda__1___spec__1(obj* x_1) {
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
x_6 = l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x27___elambda__1___spec__1(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = l_Lean_Parser_command_attrInstance_HasView;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_8);
x_12 = lean::box(0);
lean::cnstr_set(x_1, 1, x_12);
lean::cnstr_set(x_1, 0, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_16 = l_Lean_Parser_command_attrInstance_HasView;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_20; 
x_19 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_6);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_15, 0);
lean::inc(x_21);
lean::dec(x_15);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_1, 1, x_22);
lean::cnstr_set(x_1, 0, x_23);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_18);
lean::cnstr_set(x_24, 1, x_1);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_1, 0);
x_27 = lean::cnstr_get(x_1, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_1);
x_28 = l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x27___elambda__1___spec__1(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
lean::dec(x_26);
x_31 = l_Lean_Parser_command_attrInstance_HasView;
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_33 = lean::apply_1(x_32, x_30);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_28);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = lean::cnstr_get(x_26, 0);
lean::inc(x_37);
lean::dec(x_26);
x_38 = lean::cnstr_get(x_29, 0);
lean::inc(x_38);
lean::dec(x_29);
x_39 = l_Lean_Parser_command_attrInstance_HasView;
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
x_41 = lean::apply_1(x_40, x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_28);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_38, 0);
lean::inc(x_45);
lean::dec(x_38);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_47, 0, x_45);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_41);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_28);
return x_50;
}
}
}
}
}
}
obj* l_Lean_Parser_command_declAttributes_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Parser_command_declAttributes_HasView_x27___elambda__1___spec__1(x_3);
x_6 = l_List_join___main___rarg(x_5);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
x_9 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::box(3);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_Parser_command_declAttributes;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_8);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::box(3);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = l_Lean_Parser_command_declAttributes;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
return x_23;
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
if (lean::obj_tag(x_4) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_8);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_command_declAttributes;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_4, 0);
lean::inc(x_31);
lean::dec(x_4);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_8);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_25);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_declAttributes;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::dec(x_8);
x_9 = l_Lean_Parser_command_attrInstance_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_7);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::box(0);
lean::cnstr_set(x_3, 1, x_14);
lean::cnstr_set(x_3, 0, x_13);
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = l_Lean_Parser_command_attrInstance_HasView;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_15);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
else
{
obj* x_23; uint8 x_24; 
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
lean::dec(x_3);
x_24 = !lean::is_exclusive(x_5);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_5, 0);
x_26 = lean::cnstr_get(x_5, 1);
x_27 = l_Lean_Parser_command_attrInstance_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::apply_1(x_28, x_23);
x_30 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_1, x_2, x_26);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set(x_5, 1, x_30);
lean::cnstr_set(x_5, 0, x_34);
return x_5;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_25);
x_35 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_29);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set(x_5, 1, x_30);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 0);
x_38 = lean::cnstr_get(x_5, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_5);
x_39 = l_Lean_Parser_command_attrInstance_HasView;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::apply_1(x_40, x_23);
x_42 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_1, x_2, x_38);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_43 = lean::cnstr_get(x_37, 0);
lean::inc(x_43);
lean::dec(x_37);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_37);
x_48 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_41);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_42);
return x_50;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_command_attrInstance_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_string(",");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2;
x_9 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_10 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_8, x_9, x_7);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_1);
return x_11;
}
}
}
obj* l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_53; 
x_53 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
x_54 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4;
return x_54;
}
else
{
obj* x_55; obj* x_56; 
x_55 = lean::cnstr_get(x_53, 0);
lean::inc(x_55);
lean::dec(x_53);
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
x_57 = lean::box(3);
x_2 = x_56;
x_3 = x_57;
goto block_52;
}
else
{
obj* x_58; obj* x_59; 
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_2 = x_59;
x_3 = x_58;
goto block_52;
}
}
block_52:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_3, 0);
lean::inc(x_49);
lean::dec(x_3);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_4 = x_50;
goto block_48;
}
else
{
obj* x_51; 
lean::dec(x_3);
x_51 = lean::box(0);
x_4 = x_51;
goto block_48;
}
block_48:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_45; 
x_45 = lean::box(3);
x_5 = x_2;
x_6 = x_45;
goto block_44;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_2, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_2, 1);
lean::inc(x_47);
lean::dec(x_2);
x_5 = x_47;
x_6 = x_46;
goto block_44;
}
block_44:
{
obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_8);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
x_16 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_8);
return x_17;
}
}
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_7);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_21 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2;
x_22 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_23 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_21, x_22, x_20);
if (lean::obj_tag(x_5) == 0)
{
obj* x_24; obj* x_25; 
lean::free_heap_obj(x_7);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_23);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_5, 0);
lean::inc(x_26);
lean::dec(x_5);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
lean::dec(x_26);
lean::cnstr_set(x_7, 0, x_27);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_7);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_26);
lean::free_heap_obj(x_7);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_4);
lean::cnstr_set(x_30, 1, x_23);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_7, 0);
lean::inc(x_31);
lean::dec(x_7);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
lean::dec(x_31);
x_33 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2;
x_34 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_35 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_33, x_34, x_32);
if (lean::obj_tag(x_5) == 0)
{
obj* x_36; obj* x_37; 
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_35);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::cnstr_get(x_5, 0);
lean::inc(x_38);
lean::dec(x_5);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_4);
lean::cnstr_set(x_41, 1, x_35);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; 
lean::dec(x_38);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_4);
lean::cnstr_set(x_43, 1, x_35);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_declAttributes_HasView_x27___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declAttributes_HasView_x27;
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, uint8 x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::nat_dec_eq(x_6, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_265; obj* x_266; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_6, x_13);
if (x_4 == 0)
{
obj* x_373; obj* x_374; 
lean::inc(x_1);
lean::inc(x_8);
lean::inc(x_7);
x_373 = lean::apply_4(x_1, x_7, x_8, x_9, x_10);
x_374 = lean::cnstr_get(x_373, 0);
lean::inc(x_374);
if (lean::obj_tag(x_374) == 0)
{
obj* x_375; uint8 x_376; 
x_375 = lean::cnstr_get(x_373, 1);
lean::inc(x_375);
lean::dec(x_373);
x_376 = !lean::is_exclusive(x_374);
if (x_376 == 0)
{
obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; 
x_377 = lean::cnstr_get(x_374, 0);
x_378 = lean::cnstr_get(x_374, 2);
x_379 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_379, 0, x_377);
x_380 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_374, 2, x_380);
lean::cnstr_set(x_374, 0, x_379);
x_381 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_378, x_374);
x_265 = x_381;
x_266 = x_375;
goto block_372;
}
else
{
obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; 
x_382 = lean::cnstr_get(x_374, 0);
x_383 = lean::cnstr_get(x_374, 1);
x_384 = lean::cnstr_get(x_374, 2);
lean::inc(x_384);
lean::inc(x_383);
lean::inc(x_382);
lean::dec(x_374);
x_385 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_385, 0, x_382);
x_386 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_387 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_387, 0, x_385);
lean::cnstr_set(x_387, 1, x_383);
lean::cnstr_set(x_387, 2, x_386);
x_388 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_384, x_387);
x_265 = x_388;
x_266 = x_375;
goto block_372;
}
}
else
{
obj* x_389; uint8 x_390; 
x_389 = lean::cnstr_get(x_373, 1);
lean::inc(x_389);
lean::dec(x_373);
x_390 = !lean::is_exclusive(x_374);
if (x_390 == 0)
{
x_265 = x_374;
x_266 = x_389;
goto block_372;
}
else
{
obj* x_391; uint8 x_392; obj* x_393; 
x_391 = lean::cnstr_get(x_374, 0);
x_392 = lean::cnstr_get_scalar<uint8>(x_374, sizeof(void*)*1);
lean::inc(x_391);
lean::dec(x_374);
x_393 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_393, 0, x_391);
lean::cnstr_set_scalar(x_393, sizeof(void*)*1, x_392);
x_265 = x_393;
x_266 = x_389;
goto block_372;
}
}
}
else
{
obj* x_394; obj* x_395; obj* x_396; 
x_394 = lean::box(0);
lean::inc(x_1);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
x_395 = lean::apply_4(x_1, x_7, x_8, x_9, x_10);
x_396 = lean::cnstr_get(x_395, 0);
lean::inc(x_396);
if (lean::obj_tag(x_396) == 0)
{
obj* x_397; uint8 x_398; 
x_397 = lean::cnstr_get(x_395, 1);
lean::inc(x_397);
lean::dec(x_395);
x_398 = !lean::is_exclusive(x_396);
if (x_398 == 0)
{
obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; 
x_399 = lean::cnstr_get(x_396, 0);
x_400 = lean::cnstr_get(x_396, 2);
x_401 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_401, 0, x_399);
x_402 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_396, 2, x_402);
lean::cnstr_set(x_396, 0, x_401);
x_403 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_400, x_396);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_9);
x_265 = x_403;
x_266 = x_397;
goto block_372;
}
else
{
uint8 x_404; 
x_404 = lean::cnstr_get_scalar<uint8>(x_403, sizeof(void*)*1);
if (x_404 == 0)
{
obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; 
x_405 = lean::cnstr_get(x_403, 0);
lean::inc(x_405);
lean::dec(x_403);
x_406 = lean::cnstr_get(x_405, 2);
lean::inc(x_406);
lean::dec(x_405);
x_407 = l_mjoin___rarg___closed__1;
x_408 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_408, 0, x_406);
lean::closure_set(x_408, 1, x_407);
x_409 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_409, 0, x_408);
x_410 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_410, 0, x_394);
lean::cnstr_set(x_410, 1, x_9);
lean::cnstr_set(x_410, 2, x_409);
x_265 = x_410;
x_266 = x_397;
goto block_372;
}
else
{
lean::dec(x_9);
x_265 = x_403;
x_266 = x_397;
goto block_372;
}
}
}
else
{
obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; 
x_411 = lean::cnstr_get(x_396, 0);
x_412 = lean::cnstr_get(x_396, 1);
x_413 = lean::cnstr_get(x_396, 2);
lean::inc(x_413);
lean::inc(x_412);
lean::inc(x_411);
lean::dec(x_396);
x_414 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_414, 0, x_411);
x_415 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_416 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_416, 0, x_414);
lean::cnstr_set(x_416, 1, x_412);
lean::cnstr_set(x_416, 2, x_415);
x_417 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_413, x_416);
if (lean::obj_tag(x_417) == 0)
{
lean::dec(x_9);
x_265 = x_417;
x_266 = x_397;
goto block_372;
}
else
{
uint8 x_418; 
x_418 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*1);
if (x_418 == 0)
{
obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
x_419 = lean::cnstr_get(x_417, 0);
lean::inc(x_419);
lean::dec(x_417);
x_420 = lean::cnstr_get(x_419, 2);
lean::inc(x_420);
lean::dec(x_419);
x_421 = l_mjoin___rarg___closed__1;
x_422 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_422, 0, x_420);
lean::closure_set(x_422, 1, x_421);
x_423 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_423, 0, x_422);
x_424 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_424, 0, x_394);
lean::cnstr_set(x_424, 1, x_9);
lean::cnstr_set(x_424, 2, x_423);
x_265 = x_424;
x_266 = x_397;
goto block_372;
}
else
{
lean::dec(x_9);
x_265 = x_417;
x_266 = x_397;
goto block_372;
}
}
}
}
else
{
uint8 x_425; 
x_425 = lean::cnstr_get_scalar<uint8>(x_396, sizeof(void*)*1);
if (x_425 == 0)
{
obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; 
x_426 = lean::cnstr_get(x_395, 1);
lean::inc(x_426);
lean::dec(x_395);
x_427 = lean::cnstr_get(x_396, 0);
lean::inc(x_427);
lean::dec(x_396);
x_428 = lean::cnstr_get(x_427, 2);
lean::inc(x_428);
lean::dec(x_427);
x_429 = l_mjoin___rarg___closed__1;
x_430 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_430, 0, x_428);
lean::closure_set(x_430, 1, x_429);
x_431 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_431, 0, x_430);
x_432 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_432, 0, x_394);
lean::cnstr_set(x_432, 1, x_9);
lean::cnstr_set(x_432, 2, x_431);
x_265 = x_432;
x_266 = x_426;
goto block_372;
}
else
{
obj* x_433; uint8 x_434; 
lean::dec(x_9);
x_433 = lean::cnstr_get(x_395, 1);
lean::inc(x_433);
lean::dec(x_395);
x_434 = !lean::is_exclusive(x_396);
if (x_434 == 0)
{
x_265 = x_396;
x_266 = x_433;
goto block_372;
}
else
{
obj* x_435; obj* x_436; 
x_435 = lean::cnstr_get(x_396, 0);
lean::inc(x_435);
lean::dec(x_396);
x_436 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_436, 0, x_435);
lean::cnstr_set_scalar(x_436, sizeof(void*)*1, x_425);
x_265 = x_436;
x_266 = x_433;
goto block_372;
}
}
}
}
block_264:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_15, 2);
x_20 = lean::cnstr_get(x_15, 0);
lean::dec(x_20);
x_21 = l_List_reverse___rarg(x_5);
x_22 = l_Lean_Parser_noKind;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_15, 2, x_24);
lean::cnstr_set(x_15, 0, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_15);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_16);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_15, 1);
x_28 = lean::cnstr_get(x_15, 2);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_15);
x_29 = l_List_reverse___rarg(x_5);
x_30 = l_Lean_Parser_noKind;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_27);
lean::cnstr_set(x_33, 2, x_32);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_16);
return x_35;
}
}
else
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_15);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; uint8 x_40; 
x_37 = lean::cnstr_get(x_15, 1);
x_38 = lean::cnstr_get(x_15, 2);
x_39 = lean::cnstr_get(x_15, 0);
lean::dec(x_39);
x_40 = !lean::is_exclusive(x_17);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_41 = lean::cnstr_get(x_17, 0);
x_91 = lean::box(0);
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_8);
lean::inc(x_7);
x_92 = lean::apply_4(x_2, x_7, x_8, x_37, x_16);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
lean::dec(x_92);
x_95 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_93);
if (lean::obj_tag(x_95) == 0)
{
uint8 x_96; 
x_96 = !lean::is_exclusive(x_95);
if (x_96 == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_97 = lean::cnstr_get(x_95, 0);
x_98 = lean::cnstr_get(x_95, 2);
lean::cnstr_set(x_17, 0, x_97);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_95, 2, x_99);
lean::cnstr_set(x_95, 0, x_17);
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_95);
if (lean::obj_tag(x_100) == 0)
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_42 = x_100;
x_43 = x_94;
goto block_90;
}
else
{
uint8 x_101; 
x_101 = lean::cnstr_get_scalar<uint8>(x_100, sizeof(void*)*1);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
lean::dec(x_100);
x_103 = lean::cnstr_get(x_102, 2);
lean::inc(x_103);
lean::dec(x_102);
x_104 = l_mjoin___rarg___closed__1;
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_105, 0, x_103);
lean::closure_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_15, 2, x_106);
lean::cnstr_set(x_15, 0, x_91);
x_42 = x_15;
x_43 = x_94;
goto block_90;
}
else
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_42 = x_100;
x_43 = x_94;
goto block_90;
}
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_107 = lean::cnstr_get(x_95, 0);
x_108 = lean::cnstr_get(x_95, 1);
x_109 = lean::cnstr_get(x_95, 2);
lean::inc(x_109);
lean::inc(x_108);
lean::inc(x_107);
lean::dec(x_95);
lean::cnstr_set(x_17, 0, x_107);
x_110 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_111 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_111, 0, x_17);
lean::cnstr_set(x_111, 1, x_108);
lean::cnstr_set(x_111, 2, x_110);
x_112 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_109, x_111);
if (lean::obj_tag(x_112) == 0)
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_42 = x_112;
x_43 = x_94;
goto block_90;
}
else
{
uint8 x_113; 
x_113 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (x_113 == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_114 = lean::cnstr_get(x_112, 0);
lean::inc(x_114);
lean::dec(x_112);
x_115 = lean::cnstr_get(x_114, 2);
lean::inc(x_115);
lean::dec(x_114);
x_116 = l_mjoin___rarg___closed__1;
x_117 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_117, 0, x_115);
lean::closure_set(x_117, 1, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_15, 2, x_118);
lean::cnstr_set(x_15, 0, x_91);
x_42 = x_15;
x_43 = x_94;
goto block_90;
}
else
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_42 = x_112;
x_43 = x_94;
goto block_90;
}
}
}
}
else
{
uint8 x_119; 
x_119 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
if (x_119 == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_120 = lean::cnstr_get(x_95, 0);
lean::inc(x_120);
lean::dec(x_95);
x_121 = lean::cnstr_get(x_120, 2);
lean::inc(x_121);
lean::dec(x_120);
x_122 = l_mjoin___rarg___closed__1;
x_123 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_123, 0, x_121);
lean::closure_set(x_123, 1, x_122);
lean::cnstr_set(x_17, 0, x_123);
lean::cnstr_set(x_15, 2, x_17);
lean::cnstr_set(x_15, 0, x_91);
x_42 = x_15;
x_43 = x_94;
goto block_90;
}
else
{
uint8 x_124; 
lean::free_heap_obj(x_17);
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_124 = !lean::is_exclusive(x_95);
if (x_124 == 0)
{
x_42 = x_95;
x_43 = x_94;
goto block_90;
}
else
{
obj* x_125; obj* x_126; 
x_125 = lean::cnstr_get(x_95, 0);
lean::inc(x_125);
lean::dec(x_95);
x_126 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set_scalar(x_126, sizeof(void*)*1, x_119);
x_42 = x_126;
x_43 = x_94;
goto block_90;
}
}
}
block_90:
{
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; 
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
uint8 x_45; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_45 = !lean::is_exclusive(x_42);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_46 = lean::cnstr_get(x_42, 2);
x_47 = lean::cnstr_get(x_42, 0);
lean::dec(x_47);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_41);
lean::cnstr_set(x_48, 1, x_5);
x_49 = l_List_reverse___rarg(x_48);
x_50 = l_Lean_Parser_noKind;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_42, 2, x_52);
lean::cnstr_set(x_42, 0, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_42);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_43);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_42, 1);
x_57 = lean::cnstr_get(x_42, 2);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_42);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_41);
lean::cnstr_set(x_58, 1, x_5);
x_59 = l_List_reverse___rarg(x_58);
x_60 = l_Lean_Parser_noKind;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
x_62 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_56);
lean::cnstr_set(x_63, 2, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_63);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_43);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; 
x_67 = lean::cnstr_get(x_42, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_42, 2);
lean::inc(x_68);
lean::dec(x_42);
x_69 = lean::cnstr_get(x_44, 0);
lean::inc(x_69);
lean::dec(x_44);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_41);
lean::cnstr_set(x_70, 1, x_5);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_3, x_71, x_14, x_7, x_8, x_67, x_43);
lean::dec(x_14);
x_73 = !lean::is_exclusive(x_72);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_72, 0);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_74);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_75);
lean::cnstr_set(x_72, 0, x_76);
return x_72;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::cnstr_get(x_72, 0);
x_78 = lean::cnstr_get(x_72, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_72);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_77);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_79);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_78);
return x_81;
}
}
}
else
{
uint8 x_82; 
lean::dec(x_41);
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_82 = !lean::is_exclusive(x_42);
if (x_82 == 0)
{
obj* x_83; obj* x_84; 
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_42);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_43);
return x_84;
}
else
{
obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_42, 0);
x_86 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
lean::inc(x_85);
lean::dec(x_42);
x_87 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_43);
return x_89;
}
}
}
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_127 = lean::cnstr_get(x_17, 0);
lean::inc(x_127);
lean::dec(x_17);
x_162 = lean::box(0);
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_8);
lean::inc(x_7);
x_163 = lean::apply_4(x_2, x_7, x_8, x_37, x_16);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
lean::dec(x_163);
x_166 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_164);
if (lean::obj_tag(x_166) == 0)
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
x_167 = lean::cnstr_get(x_166, 0);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_166, 1);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_166, 2);
lean::inc(x_169);
if (lean::is_exclusive(x_166)) {
 lean::cnstr_release(x_166, 0);
 lean::cnstr_release(x_166, 1);
 lean::cnstr_release(x_166, 2);
 x_170 = x_166;
} else {
 lean::dec_ref(x_166);
 x_170 = lean::box(0);
}
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_167);
x_172 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_170)) {
 x_173 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_173 = x_170;
}
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_168);
lean::cnstr_set(x_173, 2, x_172);
x_174 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_169, x_173);
if (lean::obj_tag(x_174) == 0)
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_128 = x_174;
x_129 = x_165;
goto block_161;
}
else
{
uint8 x_175; 
x_175 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
if (x_175 == 0)
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
x_176 = lean::cnstr_get(x_174, 0);
lean::inc(x_176);
lean::dec(x_174);
x_177 = lean::cnstr_get(x_176, 2);
lean::inc(x_177);
lean::dec(x_176);
x_178 = l_mjoin___rarg___closed__1;
x_179 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_179, 0, x_177);
lean::closure_set(x_179, 1, x_178);
x_180 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_15, 2, x_180);
lean::cnstr_set(x_15, 0, x_162);
x_128 = x_15;
x_129 = x_165;
goto block_161;
}
else
{
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_128 = x_174;
x_129 = x_165;
goto block_161;
}
}
}
else
{
uint8 x_181; 
x_181 = lean::cnstr_get_scalar<uint8>(x_166, sizeof(void*)*1);
if (x_181 == 0)
{
obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
x_182 = lean::cnstr_get(x_166, 0);
lean::inc(x_182);
lean::dec(x_166);
x_183 = lean::cnstr_get(x_182, 2);
lean::inc(x_183);
lean::dec(x_182);
x_184 = l_mjoin___rarg___closed__1;
x_185 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_185, 0, x_183);
lean::closure_set(x_185, 1, x_184);
x_186 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_15, 2, x_186);
lean::cnstr_set(x_15, 0, x_162);
x_128 = x_15;
x_129 = x_165;
goto block_161;
}
else
{
obj* x_187; obj* x_188; obj* x_189; 
lean::free_heap_obj(x_15);
lean::dec(x_37);
x_187 = lean::cnstr_get(x_166, 0);
lean::inc(x_187);
if (lean::is_exclusive(x_166)) {
 lean::cnstr_release(x_166, 0);
 x_188 = x_166;
} else {
 lean::dec_ref(x_166);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set_scalar(x_189, sizeof(void*)*1, x_181);
x_128 = x_189;
x_129 = x_165;
goto block_161;
}
}
block_161:
{
if (lean::obj_tag(x_128) == 0)
{
obj* x_130; 
x_130 = lean::cnstr_get(x_128, 0);
lean::inc(x_130);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_128, 2);
lean::inc(x_132);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 lean::cnstr_release(x_128, 2);
 x_133 = x_128;
} else {
 lean::dec_ref(x_128);
 x_133 = lean::box(0);
}
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_127);
lean::cnstr_set(x_134, 1, x_5);
x_135 = l_List_reverse___rarg(x_134);
x_136 = l_Lean_Parser_noKind;
x_137 = l_Lean_Parser_Syntax_mkNode(x_136, x_135);
x_138 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_133)) {
 x_139 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_139 = x_133;
}
lean::cnstr_set(x_139, 0, x_137);
lean::cnstr_set(x_139, 1, x_131);
lean::cnstr_set(x_139, 2, x_138);
x_140 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_132, x_139);
x_141 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_140);
x_142 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_129);
return x_142;
}
else
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_143 = lean::cnstr_get(x_128, 1);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_128, 2);
lean::inc(x_144);
lean::dec(x_128);
x_145 = lean::cnstr_get(x_130, 0);
lean::inc(x_145);
lean::dec(x_130);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_127);
lean::cnstr_set(x_146, 1, x_5);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_146);
x_148 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_3, x_147, x_14, x_7, x_8, x_143, x_129);
lean::dec(x_14);
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_148, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 lean::cnstr_release(x_148, 1);
 x_151 = x_148;
} else {
 lean::dec_ref(x_148);
 x_151 = lean::box(0);
}
x_152 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_144, x_149);
x_153 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_152);
if (lean::is_scalar(x_151)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_151;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_150);
return x_154;
}
}
else
{
obj* x_155; uint8 x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_127);
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_155 = lean::cnstr_get(x_128, 0);
lean::inc(x_155);
x_156 = lean::cnstr_get_scalar<uint8>(x_128, sizeof(void*)*1);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 x_157 = x_128;
} else {
 lean::dec_ref(x_128);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
lean::cnstr_set_scalar(x_158, sizeof(void*)*1, x_156);
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_158);
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_129);
return x_160;
}
}
}
}
else
{
obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
x_190 = lean::cnstr_get(x_15, 1);
x_191 = lean::cnstr_get(x_15, 2);
lean::inc(x_191);
lean::inc(x_190);
lean::dec(x_15);
x_192 = lean::cnstr_get(x_17, 0);
lean::inc(x_192);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_193 = x_17;
} else {
 lean::dec_ref(x_17);
 x_193 = lean::box(0);
}
x_228 = lean::box(0);
lean::inc(x_2);
lean::inc(x_190);
lean::inc(x_8);
lean::inc(x_7);
x_229 = lean::apply_4(x_2, x_7, x_8, x_190, x_16);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
x_231 = lean::cnstr_get(x_229, 1);
lean::inc(x_231);
lean::dec(x_229);
x_232 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_230);
if (lean::obj_tag(x_232) == 0)
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
x_233 = lean::cnstr_get(x_232, 0);
lean::inc(x_233);
x_234 = lean::cnstr_get(x_232, 1);
lean::inc(x_234);
x_235 = lean::cnstr_get(x_232, 2);
lean::inc(x_235);
if (lean::is_exclusive(x_232)) {
 lean::cnstr_release(x_232, 0);
 lean::cnstr_release(x_232, 1);
 lean::cnstr_release(x_232, 2);
 x_236 = x_232;
} else {
 lean::dec_ref(x_232);
 x_236 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_237 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_237 = x_193;
}
lean::cnstr_set(x_237, 0, x_233);
x_238 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_236)) {
 x_239 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_239 = x_236;
}
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set(x_239, 1, x_234);
lean::cnstr_set(x_239, 2, x_238);
x_240 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_235, x_239);
if (lean::obj_tag(x_240) == 0)
{
lean::dec(x_190);
x_194 = x_240;
x_195 = x_231;
goto block_227;
}
else
{
uint8 x_241; 
x_241 = lean::cnstr_get_scalar<uint8>(x_240, sizeof(void*)*1);
if (x_241 == 0)
{
obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; 
x_242 = lean::cnstr_get(x_240, 0);
lean::inc(x_242);
lean::dec(x_240);
x_243 = lean::cnstr_get(x_242, 2);
lean::inc(x_243);
lean::dec(x_242);
x_244 = l_mjoin___rarg___closed__1;
x_245 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_245, 0, x_243);
lean::closure_set(x_245, 1, x_244);
x_246 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_246, 0, x_245);
x_247 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_247, 0, x_228);
lean::cnstr_set(x_247, 1, x_190);
lean::cnstr_set(x_247, 2, x_246);
x_194 = x_247;
x_195 = x_231;
goto block_227;
}
else
{
lean::dec(x_190);
x_194 = x_240;
x_195 = x_231;
goto block_227;
}
}
}
else
{
uint8 x_248; 
x_248 = lean::cnstr_get_scalar<uint8>(x_232, sizeof(void*)*1);
if (x_248 == 0)
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_249 = lean::cnstr_get(x_232, 0);
lean::inc(x_249);
lean::dec(x_232);
x_250 = lean::cnstr_get(x_249, 2);
lean::inc(x_250);
lean::dec(x_249);
x_251 = l_mjoin___rarg___closed__1;
x_252 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_252, 0, x_250);
lean::closure_set(x_252, 1, x_251);
if (lean::is_scalar(x_193)) {
 x_253 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_253 = x_193;
}
lean::cnstr_set(x_253, 0, x_252);
x_254 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_254, 0, x_228);
lean::cnstr_set(x_254, 1, x_190);
lean::cnstr_set(x_254, 2, x_253);
x_194 = x_254;
x_195 = x_231;
goto block_227;
}
else
{
obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_193);
lean::dec(x_190);
x_255 = lean::cnstr_get(x_232, 0);
lean::inc(x_255);
if (lean::is_exclusive(x_232)) {
 lean::cnstr_release(x_232, 0);
 x_256 = x_232;
} else {
 lean::dec_ref(x_232);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_255);
lean::cnstr_set_scalar(x_257, sizeof(void*)*1, x_248);
x_194 = x_257;
x_195 = x_231;
goto block_227;
}
}
block_227:
{
if (lean::obj_tag(x_194) == 0)
{
obj* x_196; 
x_196 = lean::cnstr_get(x_194, 0);
lean::inc(x_196);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
x_198 = lean::cnstr_get(x_194, 2);
lean::inc(x_198);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 lean::cnstr_release(x_194, 1);
 lean::cnstr_release(x_194, 2);
 x_199 = x_194;
} else {
 lean::dec_ref(x_194);
 x_199 = lean::box(0);
}
x_200 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_5);
x_201 = l_List_reverse___rarg(x_200);
x_202 = l_Lean_Parser_noKind;
x_203 = l_Lean_Parser_Syntax_mkNode(x_202, x_201);
x_204 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_199)) {
 x_205 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_205 = x_199;
}
lean::cnstr_set(x_205, 0, x_203);
lean::cnstr_set(x_205, 1, x_197);
lean::cnstr_set(x_205, 2, x_204);
x_206 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_198, x_205);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_191, x_206);
x_208 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_195);
return x_208;
}
else
{
obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_209 = lean::cnstr_get(x_194, 1);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_194, 2);
lean::inc(x_210);
lean::dec(x_194);
x_211 = lean::cnstr_get(x_196, 0);
lean::inc(x_211);
lean::dec(x_196);
x_212 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_212, 0, x_192);
lean::cnstr_set(x_212, 1, x_5);
x_213 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_213, 0, x_211);
lean::cnstr_set(x_213, 1, x_212);
x_214 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_3, x_213, x_14, x_7, x_8, x_209, x_195);
lean::dec(x_14);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_216 = lean::cnstr_get(x_214, 1);
lean::inc(x_216);
if (lean::is_exclusive(x_214)) {
 lean::cnstr_release(x_214, 0);
 lean::cnstr_release(x_214, 1);
 x_217 = x_214;
} else {
 lean::dec_ref(x_214);
 x_217 = lean::box(0);
}
x_218 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_210, x_215);
x_219 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_191, x_218);
if (lean::is_scalar(x_217)) {
 x_220 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_220 = x_217;
}
lean::cnstr_set(x_220, 0, x_219);
lean::cnstr_set(x_220, 1, x_216);
return x_220;
}
}
else
{
obj* x_221; uint8 x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_192);
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_221 = lean::cnstr_get(x_194, 0);
lean::inc(x_221);
x_222 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 x_223 = x_194;
} else {
 lean::dec_ref(x_194);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_222);
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_191, x_224);
x_226 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_195);
return x_226;
}
}
}
}
}
else
{
uint8 x_258; 
lean::dec(x_14);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_258 = !lean::is_exclusive(x_15);
if (x_258 == 0)
{
obj* x_259; 
x_259 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_259, 0, x_15);
lean::cnstr_set(x_259, 1, x_16);
return x_259;
}
else
{
obj* x_260; uint8 x_261; obj* x_262; obj* x_263; 
x_260 = lean::cnstr_get(x_15, 0);
x_261 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
lean::inc(x_260);
lean::dec(x_15);
x_262 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_262, 0, x_260);
lean::cnstr_set_scalar(x_262, sizeof(void*)*1, x_261);
x_263 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_16);
return x_263;
}
}
}
block_372:
{
if (lean::obj_tag(x_265) == 0)
{
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
obj* x_267; obj* x_268; 
x_267 = lean::cnstr_get(x_265, 0);
lean::inc(x_267);
x_268 = lean::cnstr_get(x_267, 3);
lean::inc(x_268);
if (lean::obj_tag(x_268) == 0)
{
uint8 x_269; 
x_269 = !lean::is_exclusive(x_265);
if (x_269 == 0)
{
uint8 x_270; obj* x_271; uint8 x_272; 
x_270 = lean::cnstr_get_scalar<uint8>(x_265, sizeof(void*)*1);
x_271 = lean::cnstr_get(x_265, 0);
lean::dec(x_271);
x_272 = !lean::is_exclusive(x_267);
if (x_272 == 0)
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
x_273 = lean::cnstr_get(x_267, 3);
lean::dec(x_273);
x_274 = lean::box(3);
lean::inc(x_5);
x_275 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_5);
x_276 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_276, 0, x_274);
lean::cnstr_set(x_276, 1, x_275);
x_277 = l_List_reverse___rarg(x_276);
x_278 = l_Lean_Parser_noKind;
x_279 = l_Lean_Parser_Syntax_mkNode(x_278, x_277);
x_280 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_267, 3, x_280);
if (x_270 == 0)
{
uint8 x_281; 
x_281 = 0;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_281);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_282; 
x_282 = 1;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_282);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_267, 0);
x_284 = lean::cnstr_get(x_267, 1);
x_285 = lean::cnstr_get(x_267, 2);
lean::inc(x_285);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_267);
x_286 = lean::box(3);
lean::inc(x_5);
x_287 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_5);
x_288 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_288, 0, x_286);
lean::cnstr_set(x_288, 1, x_287);
x_289 = l_List_reverse___rarg(x_288);
x_290 = l_Lean_Parser_noKind;
x_291 = l_Lean_Parser_Syntax_mkNode(x_290, x_289);
x_292 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_292, 0, x_291);
x_293 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_293, 0, x_283);
lean::cnstr_set(x_293, 1, x_284);
lean::cnstr_set(x_293, 2, x_285);
lean::cnstr_set(x_293, 3, x_292);
if (x_270 == 0)
{
uint8 x_294; 
x_294 = 0;
lean::cnstr_set(x_265, 0, x_293);
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_294);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_295; 
x_295 = 1;
lean::cnstr_set(x_265, 0, x_293);
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_295);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
}
}
else
{
uint8 x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; 
x_296 = lean::cnstr_get_scalar<uint8>(x_265, sizeof(void*)*1);
lean::dec(x_265);
x_297 = lean::cnstr_get(x_267, 0);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_267, 1);
lean::inc(x_298);
x_299 = lean::cnstr_get(x_267, 2);
lean::inc(x_299);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 lean::cnstr_release(x_267, 2);
 lean::cnstr_release(x_267, 3);
 x_300 = x_267;
} else {
 lean::dec_ref(x_267);
 x_300 = lean::box(0);
}
x_301 = lean::box(3);
lean::inc(x_5);
x_302 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_302, 0, x_301);
lean::cnstr_set(x_302, 1, x_5);
x_303 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_303, 0, x_301);
lean::cnstr_set(x_303, 1, x_302);
x_304 = l_List_reverse___rarg(x_303);
x_305 = l_Lean_Parser_noKind;
x_306 = l_Lean_Parser_Syntax_mkNode(x_305, x_304);
x_307 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_307, 0, x_306);
if (lean::is_scalar(x_300)) {
 x_308 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_308 = x_300;
}
lean::cnstr_set(x_308, 0, x_297);
lean::cnstr_set(x_308, 1, x_298);
lean::cnstr_set(x_308, 2, x_299);
lean::cnstr_set(x_308, 3, x_307);
if (x_296 == 0)
{
uint8 x_309; obj* x_310; 
x_309 = 0;
x_310 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_310, 0, x_308);
lean::cnstr_set_scalar(x_310, sizeof(void*)*1, x_309);
x_15 = x_310;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_311; obj* x_312; 
x_311 = 1;
x_312 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_312, 0, x_308);
lean::cnstr_set_scalar(x_312, sizeof(void*)*1, x_311);
x_15 = x_312;
x_16 = x_266;
goto block_264;
}
}
}
else
{
uint8 x_313; 
x_313 = !lean::is_exclusive(x_265);
if (x_313 == 0)
{
uint8 x_314; obj* x_315; uint8 x_316; 
x_314 = lean::cnstr_get_scalar<uint8>(x_265, sizeof(void*)*1);
x_315 = lean::cnstr_get(x_265, 0);
lean::dec(x_315);
x_316 = !lean::is_exclusive(x_267);
if (x_316 == 0)
{
obj* x_317; uint8 x_318; 
x_317 = lean::cnstr_get(x_267, 3);
lean::dec(x_317);
x_318 = !lean::is_exclusive(x_268);
if (x_318 == 0)
{
obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; 
x_319 = lean::cnstr_get(x_268, 0);
lean::inc(x_5);
x_320 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_320, 0, x_319);
lean::cnstr_set(x_320, 1, x_5);
x_321 = lean::box(3);
x_322 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_322, 0, x_321);
lean::cnstr_set(x_322, 1, x_320);
x_323 = l_List_reverse___rarg(x_322);
x_324 = l_Lean_Parser_noKind;
x_325 = l_Lean_Parser_Syntax_mkNode(x_324, x_323);
lean::cnstr_set(x_268, 0, x_325);
if (x_314 == 0)
{
uint8 x_326; 
x_326 = 0;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_326);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_327; 
x_327 = 1;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_327);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
}
else
{
obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_328 = lean::cnstr_get(x_268, 0);
lean::inc(x_328);
lean::dec(x_268);
lean::inc(x_5);
x_329 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_5);
x_330 = lean::box(3);
x_331 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_329);
x_332 = l_List_reverse___rarg(x_331);
x_333 = l_Lean_Parser_noKind;
x_334 = l_Lean_Parser_Syntax_mkNode(x_333, x_332);
x_335 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_335, 0, x_334);
lean::cnstr_set(x_267, 3, x_335);
if (x_314 == 0)
{
uint8 x_336; 
x_336 = 0;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_336);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_337; 
x_337 = 1;
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_337);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
}
}
else
{
obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
x_338 = lean::cnstr_get(x_267, 0);
x_339 = lean::cnstr_get(x_267, 1);
x_340 = lean::cnstr_get(x_267, 2);
lean::inc(x_340);
lean::inc(x_339);
lean::inc(x_338);
lean::dec(x_267);
x_341 = lean::cnstr_get(x_268, 0);
lean::inc(x_341);
if (lean::is_exclusive(x_268)) {
 lean::cnstr_release(x_268, 0);
 x_342 = x_268;
} else {
 lean::dec_ref(x_268);
 x_342 = lean::box(0);
}
lean::inc(x_5);
x_343 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_343, 0, x_341);
lean::cnstr_set(x_343, 1, x_5);
x_344 = lean::box(3);
x_345 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_345, 0, x_344);
lean::cnstr_set(x_345, 1, x_343);
x_346 = l_List_reverse___rarg(x_345);
x_347 = l_Lean_Parser_noKind;
x_348 = l_Lean_Parser_Syntax_mkNode(x_347, x_346);
if (lean::is_scalar(x_342)) {
 x_349 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_349 = x_342;
}
lean::cnstr_set(x_349, 0, x_348);
x_350 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_350, 0, x_338);
lean::cnstr_set(x_350, 1, x_339);
lean::cnstr_set(x_350, 2, x_340);
lean::cnstr_set(x_350, 3, x_349);
if (x_314 == 0)
{
uint8 x_351; 
x_351 = 0;
lean::cnstr_set(x_265, 0, x_350);
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_351);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_352; 
x_352 = 1;
lean::cnstr_set(x_265, 0, x_350);
lean::cnstr_set_scalar(x_265, sizeof(void*)*1, x_352);
x_15 = x_265;
x_16 = x_266;
goto block_264;
}
}
}
else
{
uint8 x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
x_353 = lean::cnstr_get_scalar<uint8>(x_265, sizeof(void*)*1);
lean::dec(x_265);
x_354 = lean::cnstr_get(x_267, 0);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_267, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_267, 2);
lean::inc(x_356);
if (lean::is_exclusive(x_267)) {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 lean::cnstr_release(x_267, 2);
 lean::cnstr_release(x_267, 3);
 x_357 = x_267;
} else {
 lean::dec_ref(x_267);
 x_357 = lean::box(0);
}
x_358 = lean::cnstr_get(x_268, 0);
lean::inc(x_358);
if (lean::is_exclusive(x_268)) {
 lean::cnstr_release(x_268, 0);
 x_359 = x_268;
} else {
 lean::dec_ref(x_268);
 x_359 = lean::box(0);
}
lean::inc(x_5);
x_360 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_5);
x_361 = lean::box(3);
x_362 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_360);
x_363 = l_List_reverse___rarg(x_362);
x_364 = l_Lean_Parser_noKind;
x_365 = l_Lean_Parser_Syntax_mkNode(x_364, x_363);
if (lean::is_scalar(x_359)) {
 x_366 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_366 = x_359;
}
lean::cnstr_set(x_366, 0, x_365);
if (lean::is_scalar(x_357)) {
 x_367 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_367 = x_357;
}
lean::cnstr_set(x_367, 0, x_354);
lean::cnstr_set(x_367, 1, x_355);
lean::cnstr_set(x_367, 2, x_356);
lean::cnstr_set(x_367, 3, x_366);
if (x_353 == 0)
{
uint8 x_368; obj* x_369; 
x_368 = 0;
x_369 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_369, 0, x_367);
lean::cnstr_set_scalar(x_369, sizeof(void*)*1, x_368);
x_15 = x_369;
x_16 = x_266;
goto block_264;
}
else
{
uint8 x_370; obj* x_371; 
x_370 = 1;
x_371 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_371, 0, x_367);
lean::cnstr_set_scalar(x_371, sizeof(void*)*1, x_370);
x_15 = x_371;
x_16 = x_266;
goto block_264;
}
}
}
}
}
}
else
{
obj* x_437; obj* x_438; obj* x_439; obj* x_440; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_437 = lean::box(0);
x_438 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_439 = l_mjoin___rarg___closed__1;
x_440 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_438, x_439, x_437, x_437, x_7, x_8, x_9, x_10);
lean::dec(x_8);
lean::dec(x_7);
return x_440;
}
}
}
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; uint8 x_14; 
x_8 = l_String_OldIterator_remaining___main(x_6);
x_9 = lean::box(0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_8, x_10);
lean::dec(x_8);
x_12 = 0;
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_12, x_9, x_11, x_4, x_5, x_6, x_7);
lean::dec(x_11);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = l_Lean_Parser_finishCommentBlock___closed__2;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_15);
lean::cnstr_set(x_13, 0, x_17);
return x_13;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_13, 0);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_13);
x_20 = l_Lean_Parser_finishCommentBlock___closed__2;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::mk_string("@[");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::mk_string(",");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_2);
lean::dec(x_4);
x_6 = l_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens;
x_7 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_6, x_5);
lean::dec(x_5);
x_8 = lean::mk_string("]");
x_9 = l_Lean_Parser_symbol_tokens___rarg(x_8, x_2);
lean::dec(x_8);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_10);
lean::dec(x_9);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_11);
lean::dec(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_12);
lean::dec(x_12);
lean::dec(x_3);
x_14 = l_Lean_Parser_tokens___rarg(x_13);
lean::dec(x_13);
return x_14;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; uint8 x_12; obj* x_13; 
x_11 = lean::unbox(x_3);
lean::dec(x_3);
x_12 = lean::unbox(x_4);
lean::dec(x_4);
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean::dec(x_6);
return x_13;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_3);
lean::dec(x_3);
x_9 = l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("@[");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::mk_string(",");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
x_15 = 1;
x_16 = lean::box(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_14);
lean::closure_set(x_17, 1, x_13);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::mk_string("]");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_8);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_command_declAttributes;
x_27 = l_Lean_Parser_command_declAttributes_HasView;
x_28 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_26, x_25, x_27);
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_28;
}
}
obj* _init_l_Lean_Parser_command_declAttributes_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_1 = lean::mk_string("@[");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string(",");
x_7 = l_String_trim(x_6);
lean::dec(x_6);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_4);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_attrInstance_Parser), 4, 0);
x_11 = 1;
x_12 = lean::box(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_9);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::mk_string("]");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_5);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
obj* l_Lean_Parser_command_declAttributes_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declAttributes;
x_6 = l_Lean_Parser_command_declAttributes_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_visibility() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("visibility");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_visibility;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_visibility;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_visibility;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_visibility;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("visibility");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_visibility_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
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
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
lean::dec(x_22);
if (x_30 == 0)
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_31);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_13);
return x_32;
}
else
{
obj* x_33; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_33 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1;
return x_33;
}
}
else
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_34);
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_13);
return x_35;
}
else
{
obj* x_36; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_36 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2;
return x_36;
}
}
}
else
{
obj* x_37; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_37 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_37;
}
}
}
}
}
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_13, 0);
lean::inc(x_38);
lean::dec(x_13);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
switch (lean::obj_tag(x_39)) {
case 0:
{
obj* x_40; 
lean::dec(x_38);
x_40 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_40;
}
case 1:
{
obj* x_41; 
lean::dec(x_39);
lean::dec(x_38);
x_41 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_41;
}
default: 
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_42 = lean::cnstr_get(x_38, 1);
lean::inc(x_42);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_45 = lean::box(0);
x_46 = lean_name_dec_eq(x_43, x_45);
lean::dec(x_43);
if (x_46 == 0)
{
obj* x_47; 
lean::dec(x_44);
lean::dec(x_42);
x_47 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_47;
}
else
{
if (lean::obj_tag(x_42) == 0)
{
obj* x_48; 
lean::dec(x_44);
x_48 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_48;
}
else
{
obj* x_49; 
x_49 = lean::cnstr_get(x_42, 1);
lean::inc(x_49);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::nat_dec_eq(x_44, x_51);
lean::dec(x_44);
if (x_52 == 0)
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
lean::dec(x_50);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
else
{
obj* x_56; 
lean::dec(x_50);
x_56 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1;
return x_56;
}
}
else
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
else
{
obj* x_60; 
lean::dec(x_50);
x_60 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2;
return x_60;
}
}
}
else
{
obj* x_61; 
lean::dec(x_49);
lean::dec(x_44);
lean::dec(x_42);
x_61 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_61;
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
obj* x_62; 
lean::dec(x_11);
lean::dec(x_6);
x_62 = l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3;
return x_62;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_visibility_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_visibility_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_visibility_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_visibility_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_visibility_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_visibility_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declModifiers() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declModifiers");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_noKind;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_noKind;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
x_6 = l_Lean_Parser_Syntax_mkNode(x_4, x_1);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_1);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_82; 
x_82 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_8 = x_82;
goto block_81;
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_83 = lean::cnstr_get(x_2, 0);
lean::inc(x_83);
lean::dec(x_2);
x_84 = l_Lean_Parser_command_docComment_HasView;
x_85 = lean::cnstr_get(x_84, 1);
lean::inc(x_85);
x_86 = lean::apply_1(x_85, x_83);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_7);
x_88 = l_Lean_Parser_noKind;
x_89 = l_Lean_Parser_Syntax_mkNode(x_88, x_87);
x_8 = x_89;
goto block_81;
}
block_81:
{
obj* x_9; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_73; 
x_73 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_9 = x_73;
goto block_72;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_74 = lean::cnstr_get(x_3, 0);
lean::inc(x_74);
lean::dec(x_3);
x_75 = l_Lean_Parser_command_declAttributes_HasView;
x_76 = lean::cnstr_get(x_75, 1);
lean::inc(x_76);
x_77 = lean::apply_1(x_76, x_74);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_7);
x_79 = l_Lean_Parser_noKind;
x_80 = l_Lean_Parser_Syntax_mkNode(x_79, x_78);
x_9 = x_80;
goto block_72;
}
block_72:
{
obj* x_10; 
if (lean::obj_tag(x_4) == 0)
{
obj* x_64; 
x_64 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_10 = x_64;
goto block_63;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_4, 0);
lean::inc(x_65);
lean::dec(x_4);
x_66 = l_Lean_Parser_command_visibility_HasView;
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_68 = lean::apply_1(x_67, x_65);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_7);
x_70 = l_Lean_Parser_noKind;
x_71 = l_Lean_Parser_Syntax_mkNode(x_70, x_69);
x_10 = x_71;
goto block_63;
}
block_63:
{
obj* x_11; obj* x_12; 
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = l_Lean_Parser_Term_binderContent_HasView_x27___elambda__1___closed__2;
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_10);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_9);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_8);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_declModifiers;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_6, 0);
lean::inc(x_39);
lean::dec(x_6);
x_40 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_11 = x_40;
x_12 = x_39;
goto block_32;
}
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_5, 0);
lean::inc(x_41);
lean::dec(x_5);
if (lean::obj_tag(x_41) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2;
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_10);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_9);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_8);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_declModifiers;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_6, 0);
lean::inc(x_48);
lean::dec(x_6);
x_49 = l_Lean_Parser_command_notation_HasView_x27___elambda__1___closed__1;
x_11 = x_49;
x_12 = x_48;
goto block_32;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_7);
x_53 = l_Lean_Parser_noKind;
x_54 = l_Lean_Parser_Syntax_mkNode(x_53, x_52);
if (lean::obj_tag(x_6) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_55 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_10);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_9);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_8);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_Lean_Parser_command_declModifiers;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
return x_61;
}
else
{
obj* x_62; 
x_62 = lean::cnstr_get(x_6, 0);
lean::inc(x_62);
lean::dec(x_6);
x_11 = x_54;
x_12 = x_62;
goto block_32;
}
}
}
block_32:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_command_declModifiers;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
x_23 = l_Lean_Parser_noKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_7);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_10);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_9);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_command_declModifiers;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
return x_31;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_visibility_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_declAttributes_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_docComment_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_110; obj* x_111; 
x_110 = lean::box(3);
x_111 = l_Lean_Parser_Syntax_asNode___main(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; 
x_112 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_1 = x_112;
goto block_109;
}
else
{
uint8 x_113; 
x_113 = !lean::is_exclusive(x_111);
if (x_113 == 0)
{
obj* x_114; obj* x_115; 
x_114 = lean::cnstr_get(x_111, 0);
x_115 = lean::cnstr_get(x_114, 1);
lean::inc(x_115);
lean::dec(x_114);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; 
lean::free_heap_obj(x_111);
x_116 = lean::box(0);
x_1 = x_116;
goto block_109;
}
else
{
obj* x_117; 
x_117 = lean::cnstr_get(x_115, 1);
lean::inc(x_117);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
lean::dec(x_115);
x_119 = l_Lean_Parser_command_docComment_HasView;
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_121 = lean::apply_1(x_120, x_118);
lean::cnstr_set(x_111, 0, x_121);
x_1 = x_111;
goto block_109;
}
else
{
obj* x_122; 
lean::dec(x_117);
lean::dec(x_115);
lean::free_heap_obj(x_111);
x_122 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_1 = x_122;
goto block_109;
}
}
}
else
{
obj* x_123; obj* x_124; 
x_123 = lean::cnstr_get(x_111, 0);
lean::inc(x_123);
lean::dec(x_111);
x_124 = lean::cnstr_get(x_123, 1);
lean::inc(x_124);
lean::dec(x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; 
x_125 = lean::box(0);
x_1 = x_125;
goto block_109;
}
else
{
obj* x_126; 
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
if (lean::obj_tag(x_126) == 0)
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
lean::dec(x_124);
x_128 = l_Lean_Parser_command_docComment_HasView;
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_130 = lean::apply_1(x_129, x_127);
x_131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
x_1 = x_131;
goto block_109;
}
else
{
obj* x_132; 
lean::dec(x_126);
lean::dec(x_124);
x_132 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_1 = x_132;
goto block_109;
}
}
}
}
block_109:
{
obj* x_2; obj* x_86; obj* x_87; 
x_86 = lean::box(3);
x_87 = l_Lean_Parser_Syntax_asNode___main(x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; 
x_88 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_2 = x_88;
goto block_85;
}
else
{
uint8 x_89; 
x_89 = !lean::is_exclusive(x_87);
if (x_89 == 0)
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_87, 0);
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; 
lean::free_heap_obj(x_87);
x_92 = lean::box(0);
x_2 = x_92;
goto block_85;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
lean::dec(x_91);
x_95 = l_Lean_Parser_command_declAttributes_HasView;
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::apply_1(x_96, x_94);
lean::cnstr_set(x_87, 0, x_97);
x_2 = x_87;
goto block_85;
}
else
{
obj* x_98; 
lean::dec(x_93);
lean::dec(x_91);
lean::free_heap_obj(x_87);
x_98 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_2 = x_98;
goto block_85;
}
}
}
else
{
obj* x_99; obj* x_100; 
x_99 = lean::cnstr_get(x_87, 0);
lean::inc(x_99);
lean::dec(x_87);
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
lean::dec(x_99);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; 
x_101 = lean::box(0);
x_2 = x_101;
goto block_85;
}
else
{
obj* x_102; 
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
if (lean::obj_tag(x_102) == 0)
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
lean::dec(x_100);
x_104 = l_Lean_Parser_command_declAttributes_HasView;
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_106 = lean::apply_1(x_105, x_103);
x_107 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_107, 0, x_106);
x_2 = x_107;
goto block_85;
}
else
{
obj* x_108; 
lean::dec(x_102);
lean::dec(x_100);
x_108 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_2 = x_108;
goto block_85;
}
}
}
}
block_85:
{
obj* x_3; obj* x_62; obj* x_63; 
x_62 = lean::box(3);
x_63 = l_Lean_Parser_Syntax_asNode___main(x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; 
x_64 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_3 = x_64;
goto block_61;
}
else
{
uint8 x_65; 
x_65 = !lean::is_exclusive(x_63);
if (x_65 == 0)
{
obj* x_66; obj* x_67; 
x_66 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
lean::dec(x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; 
lean::free_heap_obj(x_63);
x_68 = lean::box(0);
x_3 = x_68;
goto block_61;
}
else
{
obj* x_69; 
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
lean::dec(x_67);
x_71 = l_Lean_Parser_command_visibility_HasView;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_73 = lean::apply_1(x_72, x_70);
lean::cnstr_set(x_63, 0, x_73);
x_3 = x_63;
goto block_61;
}
else
{
obj* x_74; 
lean::dec(x_69);
lean::dec(x_67);
lean::free_heap_obj(x_63);
x_74 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_3 = x_74;
goto block_61;
}
}
}
else
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_63, 0);
lean::inc(x_75);
lean::dec(x_63);
x_76 = lean::cnstr_get(x_75, 1);
lean::inc(x_76);
lean::dec(x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; 
x_77 = lean::box(0);
x_3 = x_77;
goto block_61;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_76, 1);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
lean::dec(x_76);
x_80 = l_Lean_Parser_command_visibility_HasView;
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_82 = lean::apply_1(x_81, x_79);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_3 = x_83;
goto block_61;
}
else
{
obj* x_84; 
lean::dec(x_78);
lean::dec(x_76);
x_84 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_3 = x_84;
goto block_61;
}
}
}
}
block_61:
{
obj* x_4; obj* x_38; obj* x_39; 
x_38 = lean::box(3);
x_39 = l_Lean_Parser_Syntax_asNode___main(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; 
x_40 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_40;
goto block_37;
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_39);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_39, 0);
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; 
lean::free_heap_obj(x_39);
x_44 = lean::box(0);
x_4 = x_44;
goto block_37;
}
else
{
obj* x_45; 
x_45 = lean::cnstr_get(x_43, 1);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
lean::dec(x_46);
lean::cnstr_set(x_39, 0, x_47);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_39);
x_4 = x_48;
goto block_37;
}
else
{
obj* x_49; 
lean::dec(x_46);
lean::free_heap_obj(x_39);
x_49 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_49;
goto block_37;
}
}
else
{
obj* x_50; 
lean::dec(x_45);
lean::dec(x_43);
lean::free_heap_obj(x_39);
x_50 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_50;
goto block_37;
}
}
}
else
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_39, 0);
lean::inc(x_51);
lean::dec(x_39);
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
lean::dec(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; 
x_53 = lean::box(0);
x_4 = x_53;
goto block_37;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; 
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
lean::dec(x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_4 = x_58;
goto block_37;
}
else
{
obj* x_59; 
lean::dec(x_55);
x_59 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_59;
goto block_37;
}
}
else
{
obj* x_60; 
lean::dec(x_54);
lean::dec(x_52);
x_60 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_60;
goto block_37;
}
}
}
}
block_37:
{
obj* x_5; obj* x_6; 
x_5 = lean::box(3);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 4, x_7);
return x_8;
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::free_heap_obj(x_6);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_2);
lean::cnstr_set(x_13, 2, x_3);
lean::cnstr_set(x_13, 3, x_4);
lean::cnstr_set(x_13, 4, x_12);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
lean::cnstr_set(x_6, 0, x_16);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_6);
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_2);
lean::cnstr_set(x_18, 2, x_3);
lean::cnstr_set(x_18, 3, x_4);
lean::cnstr_set(x_18, 4, x_17);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_15);
lean::free_heap_obj(x_6);
x_19 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_20 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set(x_20, 2, x_3);
lean::cnstr_set(x_20, 3, x_4);
lean::cnstr_set(x_20, 4, x_19);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_14);
lean::dec(x_11);
lean::free_heap_obj(x_6);
x_21 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_4);
lean::cnstr_set(x_22, 4, x_21);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_6, 0);
lean::inc(x_23);
lean::dec(x_6);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_2);
lean::cnstr_set(x_26, 2, x_3);
lean::cnstr_set(x_26, 3, x_4);
lean::cnstr_set(x_26, 4, x_25);
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_24, 0);
lean::inc(x_28);
lean::dec(x_24);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
lean::dec(x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_2);
lean::cnstr_set(x_32, 2, x_3);
lean::cnstr_set(x_32, 3, x_4);
lean::cnstr_set(x_32, 4, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_28);
x_33 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_34 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_2);
lean::cnstr_set(x_34, 2, x_3);
lean::cnstr_set(x_34, 3, x_4);
lean::cnstr_set(x_34, 4, x_33);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_2);
lean::cnstr_set(x_36, 2, x_3);
lean::cnstr_set(x_36, 3, x_4);
lean::cnstr_set(x_36, 4, x_35);
return x_36;
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
obj* l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_154; 
x_154 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_154) == 0)
{
obj* x_155; 
x_155 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4;
return x_155;
}
else
{
obj* x_156; obj* x_157; 
x_156 = lean::cnstr_get(x_154, 0);
lean::inc(x_156);
lean::dec(x_154);
x_157 = lean::cnstr_get(x_156, 1);
lean::inc(x_157);
lean::dec(x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; 
x_158 = lean::box(3);
x_2 = x_157;
x_3 = x_158;
goto block_153;
}
else
{
obj* x_159; obj* x_160; 
x_159 = lean::cnstr_get(x_157, 0);
lean::inc(x_159);
x_160 = lean::cnstr_get(x_157, 1);
lean::inc(x_160);
lean::dec(x_157);
x_2 = x_160;
x_3 = x_159;
goto block_153;
}
}
block_153:
{
obj* x_4; obj* x_131; 
x_131 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; 
x_132 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_4 = x_132;
goto block_130;
}
else
{
uint8 x_133; 
x_133 = !lean::is_exclusive(x_131);
if (x_133 == 0)
{
obj* x_134; obj* x_135; 
x_134 = lean::cnstr_get(x_131, 0);
x_135 = lean::cnstr_get(x_134, 1);
lean::inc(x_135);
lean::dec(x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; 
lean::free_heap_obj(x_131);
x_136 = lean::box(0);
x_4 = x_136;
goto block_130;
}
else
{
obj* x_137; 
x_137 = lean::cnstr_get(x_135, 1);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_138 = lean::cnstr_get(x_135, 0);
lean::inc(x_138);
lean::dec(x_135);
x_139 = l_Lean_Parser_command_docComment_HasView;
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_141 = lean::apply_1(x_140, x_138);
lean::cnstr_set(x_131, 0, x_141);
x_4 = x_131;
goto block_130;
}
else
{
obj* x_142; 
lean::dec(x_137);
lean::dec(x_135);
lean::free_heap_obj(x_131);
x_142 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_4 = x_142;
goto block_130;
}
}
}
else
{
obj* x_143; obj* x_144; 
x_143 = lean::cnstr_get(x_131, 0);
lean::inc(x_143);
lean::dec(x_131);
x_144 = lean::cnstr_get(x_143, 1);
lean::inc(x_144);
lean::dec(x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_145; 
x_145 = lean::box(0);
x_4 = x_145;
goto block_130;
}
else
{
obj* x_146; 
x_146 = lean::cnstr_get(x_144, 1);
lean::inc(x_146);
if (lean::obj_tag(x_146) == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_147 = lean::cnstr_get(x_144, 0);
lean::inc(x_147);
lean::dec(x_144);
x_148 = l_Lean_Parser_command_docComment_HasView;
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_150 = lean::apply_1(x_149, x_147);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
x_4 = x_151;
goto block_130;
}
else
{
obj* x_152; 
lean::dec(x_146);
lean::dec(x_144);
x_152 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3;
x_4 = x_152;
goto block_130;
}
}
}
}
block_130:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_127; 
x_127 = lean::box(3);
x_5 = x_2;
x_6 = x_127;
goto block_126;
}
else
{
obj* x_128; obj* x_129; 
x_128 = lean::cnstr_get(x_2, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_2, 1);
lean::inc(x_129);
lean::dec(x_2);
x_5 = x_129;
x_6 = x_128;
goto block_126;
}
block_126:
{
obj* x_7; obj* x_104; 
x_104 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; 
x_105 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_7 = x_105;
goto block_103;
}
else
{
uint8 x_106; 
x_106 = !lean::is_exclusive(x_104);
if (x_106 == 0)
{
obj* x_107; obj* x_108; 
x_107 = lean::cnstr_get(x_104, 0);
x_108 = lean::cnstr_get(x_107, 1);
lean::inc(x_108);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; 
lean::free_heap_obj(x_104);
x_109 = lean::box(0);
x_7 = x_109;
goto block_103;
}
else
{
obj* x_110; 
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_111 = lean::cnstr_get(x_108, 0);
lean::inc(x_111);
lean::dec(x_108);
x_112 = l_Lean_Parser_command_declAttributes_HasView;
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_114 = lean::apply_1(x_113, x_111);
lean::cnstr_set(x_104, 0, x_114);
x_7 = x_104;
goto block_103;
}
else
{
obj* x_115; 
lean::dec(x_110);
lean::dec(x_108);
lean::free_heap_obj(x_104);
x_115 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_7 = x_115;
goto block_103;
}
}
}
else
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_104, 0);
lean::inc(x_116);
lean::dec(x_104);
x_117 = lean::cnstr_get(x_116, 1);
lean::inc(x_117);
lean::dec(x_116);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; 
x_118 = lean::box(0);
x_7 = x_118;
goto block_103;
}
else
{
obj* x_119; 
x_119 = lean::cnstr_get(x_117, 1);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
lean::dec(x_117);
x_121 = l_Lean_Parser_command_declAttributes_HasView;
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_123 = lean::apply_1(x_122, x_120);
x_124 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_124, 0, x_123);
x_7 = x_124;
goto block_103;
}
else
{
obj* x_125; 
lean::dec(x_119);
lean::dec(x_117);
x_125 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2;
x_7 = x_125;
goto block_103;
}
}
}
}
block_103:
{
obj* x_8; obj* x_9; 
if (lean::obj_tag(x_5) == 0)
{
obj* x_100; 
x_100 = lean::box(3);
x_8 = x_5;
x_9 = x_100;
goto block_99;
}
else
{
obj* x_101; obj* x_102; 
x_101 = lean::cnstr_get(x_5, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_5, 1);
lean::inc(x_102);
lean::dec(x_5);
x_8 = x_102;
x_9 = x_101;
goto block_99;
}
block_99:
{
obj* x_10; obj* x_77; 
x_77 = l_Lean_Parser_Syntax_asNode___main(x_9);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; 
x_78 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_10 = x_78;
goto block_76;
}
else
{
uint8 x_79; 
x_79 = !lean::is_exclusive(x_77);
if (x_79 == 0)
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_77, 0);
x_81 = lean::cnstr_get(x_80, 1);
lean::inc(x_81);
lean::dec(x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; 
lean::free_heap_obj(x_77);
x_82 = lean::box(0);
x_10 = x_82;
goto block_76;
}
else
{
obj* x_83; 
x_83 = lean::cnstr_get(x_81, 1);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
lean::dec(x_81);
x_85 = l_Lean_Parser_command_visibility_HasView;
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_87 = lean::apply_1(x_86, x_84);
lean::cnstr_set(x_77, 0, x_87);
x_10 = x_77;
goto block_76;
}
else
{
obj* x_88; 
lean::dec(x_83);
lean::dec(x_81);
lean::free_heap_obj(x_77);
x_88 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_10 = x_88;
goto block_76;
}
}
}
else
{
obj* x_89; obj* x_90; 
x_89 = lean::cnstr_get(x_77, 0);
lean::inc(x_89);
lean::dec(x_77);
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; 
x_91 = lean::box(0);
x_10 = x_91;
goto block_76;
}
else
{
obj* x_92; 
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_90, 0);
lean::inc(x_93);
lean::dec(x_90);
x_94 = l_Lean_Parser_command_visibility_HasView;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_96 = lean::apply_1(x_95, x_93);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
x_10 = x_97;
goto block_76;
}
else
{
obj* x_98; 
lean::dec(x_92);
lean::dec(x_90);
x_98 = l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1;
x_10 = x_98;
goto block_76;
}
}
}
}
block_76:
{
obj* x_11; obj* x_12; 
if (lean::obj_tag(x_8) == 0)
{
obj* x_73; 
x_73 = lean::box(3);
x_11 = x_8;
x_12 = x_73;
goto block_72;
}
else
{
obj* x_74; obj* x_75; 
x_74 = lean::cnstr_get(x_8, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_8, 1);
lean::inc(x_75);
lean::dec(x_8);
x_11 = x_75;
x_12 = x_74;
goto block_72;
}
block_72:
{
obj* x_13; obj* x_50; 
x_50 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; 
x_51 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_13 = x_51;
goto block_49;
}
else
{
uint8 x_52; 
x_52 = !lean::is_exclusive(x_50);
if (x_52 == 0)
{
obj* x_53; obj* x_54; 
x_53 = lean::cnstr_get(x_50, 0);
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; 
lean::free_heap_obj(x_50);
x_55 = lean::box(0);
x_13 = x_55;
goto block_49;
}
else
{
obj* x_56; 
x_56 = lean::cnstr_get(x_54, 1);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
x_57 = lean::cnstr_get(x_54, 0);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
lean::dec(x_57);
lean::cnstr_set(x_50, 0, x_58);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_50);
x_13 = x_59;
goto block_49;
}
else
{
obj* x_60; 
lean::dec(x_57);
lean::free_heap_obj(x_50);
x_60 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_13 = x_60;
goto block_49;
}
}
else
{
obj* x_61; 
lean::dec(x_56);
lean::dec(x_54);
lean::free_heap_obj(x_50);
x_61 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_13 = x_61;
goto block_49;
}
}
}
else
{
obj* x_62; obj* x_63; 
x_62 = lean::cnstr_get(x_50, 0);
lean::inc(x_62);
lean::dec(x_50);
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
lean::dec(x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; 
x_64 = lean::box(0);
x_13 = x_64;
goto block_49;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; 
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
lean::dec(x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
lean::dec(x_66);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_13 = x_69;
goto block_49;
}
else
{
obj* x_70; 
lean::dec(x_66);
x_70 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_13 = x_70;
goto block_49;
}
}
else
{
obj* x_71; 
lean::dec(x_65);
lean::dec(x_63);
x_71 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_13 = x_71;
goto block_49;
}
}
}
}
block_49:
{
obj* x_14; 
if (lean::obj_tag(x_11) == 0)
{
obj* x_47; 
x_47 = lean::box(3);
x_14 = x_47;
goto block_46;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_11, 0);
lean::inc(x_48);
lean::dec(x_11);
x_14 = x_48;
goto block_46;
}
block_46:
{
obj* x_15; 
x_15 = l_Lean_Parser_Syntax_asNode___main(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_7);
lean::cnstr_set(x_17, 2, x_10);
lean::cnstr_set(x_17, 3, x_13);
lean::cnstr_set(x_17, 4, x_16);
return x_17;
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; 
lean::free_heap_obj(x_15);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_4);
lean::cnstr_set(x_22, 1, x_7);
lean::cnstr_set(x_22, 2, x_10);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set(x_22, 4, x_21);
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
lean::cnstr_set(x_15, 0, x_25);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_15);
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_7);
lean::cnstr_set(x_27, 2, x_10);
lean::cnstr_set(x_27, 3, x_13);
lean::cnstr_set(x_27, 4, x_26);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_24);
lean::free_heap_obj(x_15);
x_28 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_29, 0, x_4);
lean::cnstr_set(x_29, 1, x_7);
lean::cnstr_set(x_29, 2, x_10);
lean::cnstr_set(x_29, 3, x_13);
lean::cnstr_set(x_29, 4, x_28);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_23);
lean::dec(x_20);
lean::free_heap_obj(x_15);
x_30 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_31 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_7);
lean::cnstr_set(x_31, 2, x_10);
lean::cnstr_set(x_31, 3, x_13);
lean::cnstr_set(x_31, 4, x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_15, 0);
lean::inc(x_32);
lean::dec(x_15);
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_35, 0, x_4);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_10);
lean::cnstr_set(x_35, 3, x_13);
lean::cnstr_set(x_35, 4, x_34);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
lean::dec(x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_41, 0, x_4);
lean::cnstr_set(x_41, 1, x_7);
lean::cnstr_set(x_41, 2, x_10);
lean::cnstr_set(x_41, 3, x_13);
lean::cnstr_set(x_41, 4, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; 
lean::dec(x_37);
x_42 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_43 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_43, 0, x_4);
lean::cnstr_set(x_43, 1, x_7);
lean::cnstr_set(x_43, 2, x_10);
lean::cnstr_set(x_43, 3, x_13);
lean::cnstr_set(x_43, 4, x_42);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_36);
lean::dec(x_33);
x_44 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_45 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_45, 0, x_4);
lean::cnstr_set(x_45, 1, x_7);
lean::cnstr_set(x_45, 2, x_10);
lean::cnstr_set(x_45, 3, x_13);
lean::cnstr_set(x_45, 4, x_44);
return x_45;
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
obj* _init_l_Lean_Parser_command_declModifiers_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declModifiers_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
if (x_2 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_94; obj* x_95; 
x_53 = lean::box(0);
lean::inc(x_5);
x_94 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; 
x_96 = lean::cnstr_get(x_94, 1);
lean::inc(x_96);
lean::dec(x_94);
x_54 = x_95;
x_55 = x_96;
goto block_93;
}
else
{
obj* x_97; obj* x_98; 
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_97, 3);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; uint8 x_100; 
x_99 = lean::cnstr_get(x_94, 1);
lean::inc(x_99);
lean::dec(x_94);
x_100 = !lean::is_exclusive(x_95);
if (x_100 == 0)
{
uint8 x_101; obj* x_102; uint8 x_103; 
x_101 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
x_102 = lean::cnstr_get(x_95, 0);
lean::dec(x_102);
x_103 = !lean::is_exclusive(x_97);
if (x_103 == 0)
{
obj* x_104; obj* x_105; 
x_104 = lean::cnstr_get(x_97, 3);
lean::dec(x_104);
x_105 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
lean::cnstr_set(x_97, 3, x_105);
if (x_101 == 0)
{
uint8 x_106; 
x_106 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_106);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_107; 
x_107 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_107);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_108 = lean::cnstr_get(x_97, 0);
x_109 = lean::cnstr_get(x_97, 1);
x_110 = lean::cnstr_get(x_97, 2);
lean::inc(x_110);
lean::inc(x_109);
lean::inc(x_108);
lean::dec(x_97);
x_111 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
x_112 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_112, 0, x_108);
lean::cnstr_set(x_112, 1, x_109);
lean::cnstr_set(x_112, 2, x_110);
lean::cnstr_set(x_112, 3, x_111);
if (x_101 == 0)
{
uint8 x_113; 
x_113 = 0;
lean::cnstr_set(x_95, 0, x_112);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_113);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_114; 
x_114 = 1;
lean::cnstr_set(x_95, 0, x_112);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_114);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
}
}
else
{
uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_115 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
lean::dec(x_95);
x_116 = lean::cnstr_get(x_97, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_97, 1);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_97, 2);
lean::inc(x_118);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 lean::cnstr_release(x_97, 2);
 lean::cnstr_release(x_97, 3);
 x_119 = x_97;
} else {
 lean::dec_ref(x_97);
 x_119 = lean::box(0);
}
x_120 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_119)) {
 x_121 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_121 = x_119;
}
lean::cnstr_set(x_121, 0, x_116);
lean::cnstr_set(x_121, 1, x_117);
lean::cnstr_set(x_121, 2, x_118);
lean::cnstr_set(x_121, 3, x_120);
if (x_115 == 0)
{
uint8 x_122; obj* x_123; 
x_122 = 0;
x_123 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_122);
x_54 = x_123;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_124; obj* x_125; 
x_124 = 1;
x_125 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_124);
x_54 = x_125;
x_55 = x_99;
goto block_93;
}
}
}
else
{
obj* x_126; uint8 x_127; 
x_126 = lean::cnstr_get(x_94, 1);
lean::inc(x_126);
lean::dec(x_94);
x_127 = !lean::is_exclusive(x_95);
if (x_127 == 0)
{
uint8 x_128; obj* x_129; uint8 x_130; 
x_128 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
x_129 = lean::cnstr_get(x_95, 0);
lean::dec(x_129);
x_130 = !lean::is_exclusive(x_97);
if (x_130 == 0)
{
obj* x_131; uint8 x_132; 
x_131 = lean::cnstr_get(x_97, 3);
lean::dec(x_131);
x_132 = !lean::is_exclusive(x_98);
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_133 = lean::cnstr_get(x_98, 0);
x_134 = lean::box(0);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
x_136 = l_Lean_Parser_noKind;
x_137 = l_Lean_Parser_Syntax_mkNode(x_136, x_135);
lean::cnstr_set(x_98, 0, x_137);
if (x_128 == 0)
{
uint8 x_138; 
x_138 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_138);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_139; 
x_139 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_139);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_140 = lean::cnstr_get(x_98, 0);
lean::inc(x_140);
lean::dec(x_98);
x_141 = lean::box(0);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_140);
lean::cnstr_set(x_142, 1, x_141);
x_143 = l_Lean_Parser_noKind;
x_144 = l_Lean_Parser_Syntax_mkNode(x_143, x_142);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_97, 3, x_145);
if (x_128 == 0)
{
uint8 x_146; 
x_146 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_146);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_147; 
x_147 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_147);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_148 = lean::cnstr_get(x_97, 0);
x_149 = lean::cnstr_get(x_97, 1);
x_150 = lean::cnstr_get(x_97, 2);
lean::inc(x_150);
lean::inc(x_149);
lean::inc(x_148);
lean::dec(x_97);
x_151 = lean::cnstr_get(x_98, 0);
lean::inc(x_151);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_152 = x_98;
} else {
 lean::dec_ref(x_98);
 x_152 = lean::box(0);
}
x_153 = lean::box(0);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_151);
lean::cnstr_set(x_154, 1, x_153);
x_155 = l_Lean_Parser_noKind;
x_156 = l_Lean_Parser_Syntax_mkNode(x_155, x_154);
if (lean::is_scalar(x_152)) {
 x_157 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_157 = x_152;
}
lean::cnstr_set(x_157, 0, x_156);
x_158 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_158, 0, x_148);
lean::cnstr_set(x_158, 1, x_149);
lean::cnstr_set(x_158, 2, x_150);
lean::cnstr_set(x_158, 3, x_157);
if (x_128 == 0)
{
uint8 x_159; 
x_159 = 0;
lean::cnstr_set(x_95, 0, x_158);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_159);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_160; 
x_160 = 1;
lean::cnstr_set(x_95, 0, x_158);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_160);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
}
else
{
uint8 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_161 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
lean::dec(x_95);
x_162 = lean::cnstr_get(x_97, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_97, 1);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_97, 2);
lean::inc(x_164);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 lean::cnstr_release(x_97, 2);
 lean::cnstr_release(x_97, 3);
 x_165 = x_97;
} else {
 lean::dec_ref(x_97);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_98, 0);
lean::inc(x_166);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_167 = x_98;
} else {
 lean::dec_ref(x_98);
 x_167 = lean::box(0);
}
x_168 = lean::box(0);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_168);
x_170 = l_Lean_Parser_noKind;
x_171 = l_Lean_Parser_Syntax_mkNode(x_170, x_169);
if (lean::is_scalar(x_167)) {
 x_172 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_172 = x_167;
}
lean::cnstr_set(x_172, 0, x_171);
if (lean::is_scalar(x_165)) {
 x_173 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_173 = x_165;
}
lean::cnstr_set(x_173, 0, x_162);
lean::cnstr_set(x_173, 1, x_163);
lean::cnstr_set(x_173, 2, x_164);
lean::cnstr_set(x_173, 3, x_172);
if (x_161 == 0)
{
uint8 x_174; obj* x_175; 
x_174 = 0;
x_175 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_174);
x_54 = x_175;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_176; obj* x_177; 
x_176 = 1;
x_177 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_176);
x_54 = x_177;
x_55 = x_126;
goto block_93;
}
}
}
}
block_93:
{
if (lean::obj_tag(x_54) == 0)
{
uint8 x_56; 
x_56 = !lean::is_exclusive(x_54);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_54, 0);
x_58 = lean::cnstr_get(x_54, 2);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_57);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_54, 2, x_60);
lean::cnstr_set(x_54, 0, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_54);
if (lean::obj_tag(x_61) == 0)
{
lean::dec(x_5);
x_7 = x_61;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_62; 
x_62 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
lean::dec(x_61);
x_64 = lean::cnstr_get(x_63, 2);
lean::inc(x_64);
lean::dec(x_63);
x_65 = l_mjoin___rarg___closed__1;
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_66, 0, x_64);
lean::closure_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_53);
lean::cnstr_set(x_68, 1, x_5);
lean::cnstr_set(x_68, 2, x_67);
x_7 = x_68;
x_8 = x_55;
goto block_52;
}
else
{
lean::dec(x_5);
x_7 = x_61;
x_8 = x_55;
goto block_52;
}
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_54, 0);
x_70 = lean::cnstr_get(x_54, 1);
x_71 = lean::cnstr_get(x_54, 2);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::dec(x_54);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_69);
x_73 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_70);
lean::cnstr_set(x_74, 2, x_73);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_74);
if (lean::obj_tag(x_75) == 0)
{
lean::dec(x_5);
x_7 = x_75;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_76; 
x_76 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_77 = lean::cnstr_get(x_75, 0);
lean::inc(x_77);
lean::dec(x_75);
x_78 = lean::cnstr_get(x_77, 2);
lean::inc(x_78);
lean::dec(x_77);
x_79 = l_mjoin___rarg___closed__1;
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_80, 0, x_78);
lean::closure_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_53);
lean::cnstr_set(x_82, 1, x_5);
lean::cnstr_set(x_82, 2, x_81);
x_7 = x_82;
x_8 = x_55;
goto block_52;
}
else
{
lean::dec(x_5);
x_7 = x_75;
x_8 = x_55;
goto block_52;
}
}
}
}
else
{
uint8 x_83; 
x_83 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (x_83 == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_84 = lean::cnstr_get(x_54, 0);
lean::inc(x_84);
lean::dec(x_54);
x_85 = lean::cnstr_get(x_84, 2);
lean::inc(x_85);
lean::dec(x_84);
x_86 = l_mjoin___rarg___closed__1;
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_87, 0, x_85);
lean::closure_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_53);
lean::cnstr_set(x_89, 1, x_5);
lean::cnstr_set(x_89, 2, x_88);
x_7 = x_89;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_90; 
lean::dec(x_5);
x_90 = !lean::is_exclusive(x_54);
if (x_90 == 0)
{
x_7 = x_54;
x_8 = x_55;
goto block_52;
}
else
{
obj* x_91; obj* x_92; 
x_91 = lean::cnstr_get(x_54, 0);
lean::inc(x_91);
lean::dec(x_54);
x_92 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_83);
x_7 = x_92;
x_8 = x_55;
goto block_52;
}
}
}
}
}
else
{
obj* x_178; 
x_178 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
return x_178;
}
block_52:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_7, 2);
x_12 = lean::cnstr_get(x_7, 0);
lean::dec(x_12);
x_13 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_14);
lean::cnstr_set(x_7, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_7);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_7, 1);
x_18 = lean::cnstr_get(x_7, 2);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_7);
x_19 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_8);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_7);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_7, 2);
x_26 = lean::cnstr_get(x_7, 0);
lean::dec(x_26);
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
lean::dec(x_9);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_noKind;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_32);
lean::cnstr_set(x_7, 0, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_7);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_7, 1);
x_36 = lean::cnstr_get(x_7, 2);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_7);
x_37 = lean::cnstr_get(x_9, 0);
lean::inc(x_37);
lean::dec(x_9);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_noKind;
x_41 = l_Lean_Parser_Syntax_mkNode(x_40, x_39);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_35);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_8);
return x_45;
}
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_7);
if (x_46 == 0)
{
obj* x_47; 
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_7);
lean::cnstr_set(x_47, 1, x_8);
return x_47;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_7, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_48);
lean::dec(x_7);
x_50 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_8);
return x_51;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_8, x_9, x_7, x_7, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_1);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_2, x_14);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_16 = lean::apply_4(x_12, x_3, x_4, x_5, x_6);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_16);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_16, 1);
x_20 = lean::cnstr_get(x_16, 0);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_17);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 2);
x_24 = lean::box(0);
x_25 = lean_name_mk_numeral(x_24, x_2);
x_26 = lean::box(0);
lean::cnstr_set(x_1, 1, x_26);
lean::cnstr_set(x_1, 0, x_22);
x_27 = l_Lean_Parser_Syntax_mkNode(x_25, x_1);
x_28 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_17, 2, x_28);
lean::cnstr_set(x_17, 0, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_17);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_29);
return x_16;
}
else
{
uint8 x_30; 
x_30 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (x_30 == 0)
{
obj* x_31; obj* x_32; uint8 x_33; 
lean::free_heap_obj(x_16);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
lean::dec(x_29);
x_32 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_13, x_15, x_3, x_4, x_5, x_19);
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
x_35 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_34);
lean::cnstr_set(x_32, 0, x_35);
return x_32;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_32, 0);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_32);
x_38 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_29);
return x_16;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_40 = lean::cnstr_get(x_17, 0);
x_41 = lean::cnstr_get(x_17, 1);
x_42 = lean::cnstr_get(x_17, 2);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_17);
x_43 = lean::box(0);
x_44 = lean_name_mk_numeral(x_43, x_2);
x_45 = lean::box(0);
lean::cnstr_set(x_1, 1, x_45);
lean::cnstr_set(x_1, 0, x_40);
x_46 = l_Lean_Parser_Syntax_mkNode(x_44, x_1);
x_47 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_41);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_48);
if (lean::obj_tag(x_49) == 0)
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_49);
return x_16;
}
else
{
uint8 x_50; 
x_50 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::free_heap_obj(x_16);
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
lean::dec(x_49);
x_52 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_13, x_15, x_3, x_4, x_5, x_19);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_55 = x_52;
} else {
 lean::dec_ref(x_52);
 x_55 = lean::box(0);
}
x_56 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_51, x_53);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_54);
return x_57;
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_16, 0, x_49);
return x_16;
}
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_58 = lean::cnstr_get(x_16, 1);
lean::inc(x_58);
lean::dec(x_16);
x_59 = lean::cnstr_get(x_17, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_17, 1);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_17, 2);
lean::inc(x_61);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 lean::cnstr_release(x_17, 2);
 x_62 = x_17;
} else {
 lean::dec_ref(x_17);
 x_62 = lean::box(0);
}
x_63 = lean::box(0);
x_64 = lean_name_mk_numeral(x_63, x_2);
x_65 = lean::box(0);
lean::cnstr_set(x_1, 1, x_65);
lean::cnstr_set(x_1, 0, x_59);
x_66 = l_Lean_Parser_Syntax_mkNode(x_64, x_1);
x_67 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_62)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_62;
}
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_60);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_61, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_58);
return x_70;
}
else
{
uint8 x_71; 
x_71 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
lean::dec(x_69);
x_73 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_13, x_15, x_3, x_4, x_5, x_58);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_73, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_76 = x_73;
} else {
 lean::dec_ref(x_73);
 x_76 = lean::box(0);
}
x_77 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_72, x_74);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_75);
return x_78;
}
else
{
obj* x_79; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_69);
lean::cnstr_set(x_79, 1, x_58);
return x_79;
}
}
}
}
else
{
uint8 x_80; 
lean::free_heap_obj(x_1);
lean::dec(x_2);
x_80 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; uint8 x_84; 
x_81 = lean::cnstr_get(x_16, 1);
lean::inc(x_81);
lean::dec(x_16);
x_82 = lean::cnstr_get(x_17, 0);
lean::inc(x_82);
lean::dec(x_17);
x_83 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_13, x_15, x_3, x_4, x_5, x_81);
x_84 = !lean::is_exclusive(x_83);
if (x_84 == 0)
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_83, 0);
x_86 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_82, x_85);
lean::cnstr_set(x_83, 0, x_86);
return x_83;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_87 = lean::cnstr_get(x_83, 0);
x_88 = lean::cnstr_get(x_83, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_83);
x_89 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_82, x_87);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8 x_91; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_91 = !lean::is_exclusive(x_16);
if (x_91 == 0)
{
obj* x_92; uint8 x_93; 
x_92 = lean::cnstr_get(x_16, 0);
lean::dec(x_92);
x_93 = !lean::is_exclusive(x_17);
if (x_93 == 0)
{
return x_16;
}
else
{
obj* x_94; obj* x_95; 
x_94 = lean::cnstr_get(x_17, 0);
lean::inc(x_94);
lean::dec(x_17);
x_95 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_80);
lean::cnstr_set(x_16, 0, x_95);
return x_16;
}
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_96 = lean::cnstr_get(x_16, 1);
lean::inc(x_96);
lean::dec(x_16);
x_97 = lean::cnstr_get(x_17, 0);
lean::inc(x_97);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_98 = x_17;
} else {
 lean::dec_ref(x_17);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_80);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
return x_100;
}
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_1, 0);
x_102 = lean::cnstr_get(x_1, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_1);
x_103 = lean::mk_nat_obj(1u);
x_104 = lean::nat_add(x_2, x_103);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_105 = lean::apply_4(x_101, x_3, x_4, x_5, x_6);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_107 = lean::cnstr_get(x_105, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_108 = x_105;
} else {
 lean::dec_ref(x_105);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_106, 1);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_106, 2);
lean::inc(x_111);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 lean::cnstr_release(x_106, 2);
 x_112 = x_106;
} else {
 lean::dec_ref(x_106);
 x_112 = lean::box(0);
}
x_113 = lean::box(0);
x_114 = lean_name_mk_numeral(x_113, x_2);
x_115 = lean::box(0);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_109);
lean::cnstr_set(x_116, 1, x_115);
x_117 = l_Lean_Parser_Syntax_mkNode(x_114, x_116);
x_118 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_112)) {
 x_119 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_119 = x_112;
}
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_110);
lean::cnstr_set(x_119, 2, x_118);
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_111, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_107);
return x_121;
}
else
{
uint8 x_122; 
x_122 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (x_122 == 0)
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_108);
x_123 = lean::cnstr_get(x_120, 0);
lean::inc(x_123);
lean::dec(x_120);
x_124 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_102, x_104, x_3, x_4, x_5, x_107);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_124)) {
 lean::cnstr_release(x_124, 0);
 lean::cnstr_release(x_124, 1);
 x_127 = x_124;
} else {
 lean::dec_ref(x_124);
 x_127 = lean::box(0);
}
x_128 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_123, x_125);
if (lean::is_scalar(x_127)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_127;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_126);
return x_129;
}
else
{
obj* x_130; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_108)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_108;
}
lean::cnstr_set(x_130, 0, x_120);
lean::cnstr_set(x_130, 1, x_107);
return x_130;
}
}
}
else
{
uint8 x_131; 
lean::dec(x_2);
x_131 = lean::cnstr_get_scalar<uint8>(x_106, sizeof(void*)*1);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_132 = lean::cnstr_get(x_105, 1);
lean::inc(x_132);
lean::dec(x_105);
x_133 = lean::cnstr_get(x_106, 0);
lean::inc(x_133);
lean::dec(x_106);
x_134 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2(x_102, x_104, x_3, x_4, x_5, x_132);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_134, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_137 = x_134;
} else {
 lean::dec_ref(x_134);
 x_137 = lean::box(0);
}
x_138 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_133, x_135);
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_136);
return x_139;
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_104);
lean::dec(x_102);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_140 = lean::cnstr_get(x_105, 1);
lean::inc(x_140);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_141 = x_105;
} else {
 lean::dec_ref(x_105);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_106, 0);
lean::inc(x_142);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_143 = x_106;
} else {
 lean::dec_ref(x_106);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_142);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_131);
if (lean::is_scalar(x_141)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_141;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_140);
return x_145;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = l_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_tokens___rarg(x_3);
x_5 = lean::mk_string("private");
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = lean::mk_string("protected");
x_9 = l_Lean_Parser_symbol_tokens___rarg(x_8, x_6);
lean::dec(x_8);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_10);
lean::dec(x_9);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_11);
lean::dec(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_13, x_10);
lean::dec(x_13);
x_15 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
x_16 = l_Lean_Parser_tokens___rarg(x_15);
lean::dec(x_15);
x_17 = lean::mk_string("noncomputable");
x_18 = l_Lean_Parser_symbol_tokens___rarg(x_17, x_6);
lean::dec(x_17);
x_19 = l_Lean_Parser_tokens___rarg(x_18);
lean::dec(x_18);
x_20 = lean::mk_string("unsafe");
x_21 = l_Lean_Parser_symbol_tokens___rarg(x_20, x_6);
lean::dec(x_20);
x_22 = l_Lean_Parser_tokens___rarg(x_21);
lean::dec(x_21);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_10);
lean::dec(x_22);
x_24 = l_Lean_Parser_List_cons_tokens___rarg(x_19, x_23);
lean::dec(x_23);
lean::dec(x_19);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_16, x_24);
lean::dec(x_24);
lean::dec(x_16);
x_26 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_25);
lean::dec(x_25);
lean::dec(x_4);
x_27 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_26);
lean::dec(x_26);
lean::dec(x_2);
x_28 = l_Lean_Parser_tokens___rarg(x_27);
lean::dec(x_27);
return x_28;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser), 4, 0);
x_6 = 0;
x_7 = lean::box(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_Parser), 4, 0);
x_10 = lean::box(x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::mk_string("private");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::mk_nat_obj(0u);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
lean::closure_set(x_16, 2, x_14);
x_17 = lean::mk_string("protected");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_15);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_15);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
x_26 = l_Lean_Parser_command_visibility;
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_25);
x_28 = lean::box(x_6);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::mk_string("noncomputable");
x_31 = l_String_trim(x_30);
lean::dec(x_30);
lean::inc(x_31);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_15);
lean::closure_set(x_33, 2, x_32);
x_34 = lean::box(x_6);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_35, 0, x_33);
lean::closure_set(x_35, 1, x_34);
x_36 = lean::mk_string("unsafe");
x_37 = l_String_trim(x_36);
lean::dec(x_36);
lean::inc(x_37);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_38, 0, x_37);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_15);
lean::closure_set(x_39, 2, x_38);
x_40 = lean::box(x_6);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_41, 0, x_39);
lean::closure_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_21);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_35);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_29);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_11);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_8);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_Lean_Parser_command_declModifiers;
x_48 = l_Lean_Parser_command_declModifiers_HasView;
x_49 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_47, x_46, x_48);
lean::dec(x_46);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_49;
}
}
obj* _init_l_Lean_Parser_command_declModifiers_Parser___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_docComment_Parser), 4, 0);
x_2 = 0;
x_3 = lean::box(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declAttributes_Parser), 4, 0);
x_6 = lean::box(x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::mk_string("private");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_11);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::mk_string("protected");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_11);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_11);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_17);
x_22 = l_Lean_Parser_command_visibility;
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::box(x_2);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::mk_string("noncomputable");
x_27 = l_String_trim(x_26);
lean::dec(x_26);
lean::inc(x_27);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_11);
lean::closure_set(x_29, 2, x_28);
x_30 = lean::box(x_2);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_31, 0, x_29);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::mk_string("unsafe");
x_33 = l_String_trim(x_32);
lean::dec(x_32);
lean::inc(x_33);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_34, 0, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_35, 0, x_33);
lean::closure_set(x_35, 1, x_11);
lean::closure_set(x_35, 2, x_34);
x_36 = lean::box(x_2);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_17);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_31);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_25);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_7);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_4);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
obj* l_Lean_Parser_command_declModifiers_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declModifiers;
x_6 = l_Lean_Parser_command_declModifiers_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_declSig() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declSig");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_2);
x_7 = l_Lean_Parser_Term_typeSpec_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::apply_1(x_8, x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_command_declSig;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_Term_typeSpec_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Term_typeSpec_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_command_declSig_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_13; 
x_12 = l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_15 = l_Lean_Parser_Term_typeSpec_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declSig_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declSig_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_Term_typeSpec_Parser_Lean_Parser_HasTokens;
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
obj* _init_l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec_Parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_command_declSig;
x_13 = l_Lean_Parser_command_declSig_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_12, x_11, x_13);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_declSig_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_typeSpec_Parser), 5, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_command_declSig_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declSig;
x_6 = l_Lean_Parser_command_declSig_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("optDeclSig");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_optDeclSig_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_command_optDeclSig;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_Term_typeSpec_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_11);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
x_17 = l_Lean_Parser_noKind;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_command_optDeclSig;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::free_heap_obj(x_5);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_15 = l_Lean_Parser_Term_typeSpec_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
lean::cnstr_set(x_5, 0, x_17);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_5);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_13);
lean::dec(x_10);
lean::free_heap_obj(x_5);
x_19 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_4);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_27 = l_Lean_Parser_Term_typeSpec_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::apply_1(x_28, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_25);
lean::dec(x_22);
x_32 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
obj* l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_68; 
x_68 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
x_69 = l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1;
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
x_2 = x_71;
x_3 = x_72;
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
x_2 = x_74;
x_3 = x_73;
goto block_67;
}
}
block_67:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_Term_bracketedBinders_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(3);
x_8 = l_Lean_Parser_Syntax_asNode___main(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; 
lean::free_heap_obj(x_8);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_18 = l_Lean_Parser_Term_typeSpec_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::apply_1(x_19, x_17);
lean::cnstr_set(x_8, 0, x_20);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_8);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_16);
lean::dec(x_13);
lean::free_heap_obj(x_8);
x_22 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_8, 0);
lean::inc(x_24);
lean::dec(x_8);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_25, 0);
lean::inc(x_29);
lean::dec(x_25);
x_30 = l_Lean_Parser_Term_typeSpec_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::apply_1(x_31, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_6);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_28);
lean::dec(x_25);
x_35 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_2, 0);
lean::inc(x_37);
lean::dec(x_2);
x_38 = l_Lean_Parser_Syntax_asNode___main(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; 
x_39 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_6);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_38);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; 
lean::free_heap_obj(x_38);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_6);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_48 = l_Lean_Parser_Term_typeSpec_HasView;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::apply_1(x_49, x_47);
lean::cnstr_set(x_38, 0, x_50);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_6);
lean::cnstr_set(x_51, 1, x_38);
return x_51;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_46);
lean::dec(x_43);
lean::free_heap_obj(x_38);
x_52 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_6);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_38, 0);
lean::inc(x_54);
lean::dec(x_38);
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; 
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_6);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_55, 0);
lean::inc(x_59);
lean::dec(x_55);
x_60 = l_Lean_Parser_Term_typeSpec_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_62 = lean::apply_1(x_61, x_59);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_6);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_58);
lean::dec(x_55);
x_65 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__2;
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_6);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_optDeclSig_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_Term_bracketedBinders_Parser_Lean_Parser_HasTokens;
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_Term_optType_Parser_Lean_Parser_HasTokens;
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
obj* _init_l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType_Parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_Lean_Parser_command_optDeclSig;
x_13 = l_Lean_Parser_command_optDeclSig_HasView;
x_14 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_12, x_11, x_13);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_optDeclSig_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_bracketedBinders_Parser), 5, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_optType_Parser), 5, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_command_optDeclSig_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_optDeclSig;
x_6 = l_Lean_Parser_command_optDeclSig_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_equation() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("equation");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_equation_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_3);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_command_equation;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_10);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(3);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_Lean_Parser_command_equation;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
if (lean::obj_tag(x_4) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_equation;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_4, 0);
lean::inc(x_33);
lean::dec(x_4);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_10);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_8);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_26);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_command_equation;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
return x_39;
}
}
}
}
obj* _init_l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_1);
lean::cnstr_set(x_5, 3, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_7);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_2);
return x_9;
}
}
}
obj* l_Lean_Parser_command_equation_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_79; 
x_79 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; 
x_80 = l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1;
return x_80;
}
else
{
obj* x_81; obj* x_82; 
x_81 = lean::cnstr_get(x_79, 0);
lean::inc(x_81);
lean::dec(x_79);
x_82 = lean::cnstr_get(x_81, 1);
lean::inc(x_82);
lean::dec(x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; 
x_83 = lean::box(3);
x_2 = x_82;
x_3 = x_83;
goto block_78;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_2 = x_85;
x_3 = x_84;
goto block_78;
}
}
block_78:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_3, 0);
lean::inc(x_75);
lean::dec(x_3);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_4 = x_76;
goto block_74;
}
else
{
obj* x_77; 
lean::dec(x_3);
x_77 = lean::box(0);
x_4 = x_77;
goto block_74;
}
block_74:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_71; 
x_71 = lean::box(3);
x_5 = x_2;
x_6 = x_71;
goto block_70;
}
else
{
obj* x_72; obj* x_73; 
x_72 = lean::cnstr_get(x_2, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_2, 1);
lean::inc(x_73);
lean::dec(x_2);
x_5 = x_73;
x_6 = x_72;
goto block_70;
}
block_70:
{
obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_10);
return x_11;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_17 = lean::box(3);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_17);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_20 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_19);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::box(0);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_4);
lean::cnstr_set(x_26, 1, x_24);
lean::cnstr_set(x_26, 2, x_23);
lean::cnstr_set(x_26, 3, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
lean::dec(x_22);
x_28 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_4);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_23);
lean::cnstr_set(x_29, 3, x_27);
return x_29;
}
}
}
}
else
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_7);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_7, 0);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
lean::dec(x_31);
x_33 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_32);
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
lean::free_heap_obj(x_7);
x_34 = lean::box(0);
x_35 = lean::box(3);
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_4);
lean::cnstr_set(x_36, 1, x_33);
lean::cnstr_set(x_36, 2, x_34);
lean::cnstr_set(x_36, 3, x_35);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_5, 1);
lean::inc(x_38);
lean::dec(x_5);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
lean::dec(x_37);
lean::cnstr_set(x_7, 0, x_39);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::box(3);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_4);
lean::cnstr_set(x_41, 1, x_33);
lean::cnstr_set(x_41, 2, x_7);
lean::cnstr_set(x_41, 3, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
lean::dec(x_38);
x_43 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_43, 0, x_4);
lean::cnstr_set(x_43, 1, x_33);
lean::cnstr_set(x_43, 2, x_7);
lean::cnstr_set(x_43, 3, x_42);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_37);
lean::free_heap_obj(x_7);
x_44 = lean::cnstr_get(x_5, 1);
lean::inc(x_44);
lean::dec(x_5);
x_45 = lean::box(0);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::box(3);
x_47 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_47, 0, x_4);
lean::cnstr_set(x_47, 1, x_33);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
lean::dec(x_44);
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_33);
lean::cnstr_set(x_49, 2, x_45);
lean::cnstr_set(x_49, 3, x_48);
return x_49;
}
}
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::cnstr_get(x_7, 0);
lean::inc(x_50);
lean::dec(x_7);
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
x_52 = l_List_map___main___at_Lean_Parser_identUnivSpec_HasView_x27___elambda__1___spec__1(x_51);
if (lean::obj_tag(x_5) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::box(0);
x_54 = lean::box(3);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_4);
lean::cnstr_set(x_55, 1, x_52);
lean::cnstr_set(x_55, 2, x_53);
lean::cnstr_set(x_55, 3, x_54);
return x_55;
}
else
{
obj* x_56; 
x_56 = lean::cnstr_get(x_5, 0);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::dec(x_5);
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
lean::dec(x_56);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_61; 
x_60 = lean::box(3);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_4);
lean::cnstr_set(x_61, 1, x_52);
lean::cnstr_set(x_61, 2, x_59);
lean::cnstr_set(x_61, 3, x_60);
return x_61;
}
else
{
obj* x_62; obj* x_63; 
x_62 = lean::cnstr_get(x_57, 0);
lean::inc(x_62);
lean::dec(x_57);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_4);
lean::cnstr_set(x_63, 1, x_52);
lean::cnstr_set(x_63, 2, x_59);
lean::cnstr_set(x_63, 3, x_62);
return x_63;
}
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_56);
x_64 = lean::cnstr_get(x_5, 1);
lean::inc(x_64);
lean::dec(x_5);
x_65 = lean::box(0);
if (lean::obj_tag(x_64) == 0)
{
obj* x_66; obj* x_67; 
x_66 = lean::box(3);
x_67 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_67, 0, x_4);
lean::cnstr_set(x_67, 1, x_52);
lean::cnstr_set(x_67, 2, x_65);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
lean::dec(x_64);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_4);
lean::cnstr_set(x_69, 1, x_52);
lean::cnstr_set(x_69, 2, x_65);
lean::cnstr_set(x_69, 3, x_68);
return x_69;
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
obj* _init_l_Lean_Parser_command_equation_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_equation_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_equation_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::mk_string("|");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_4);
x_6 = l_Lean_Parser_tokens___rarg(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
x_8 = lean::mk_string(":=");
x_9 = l_Lean_Parser_symbol_tokens___rarg(x_8, x_2);
lean::dec(x_8);
x_10 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_2);
x_11 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_12);
lean::dec(x_11);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_13);
lean::dec(x_13);
lean::dec(x_9);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_15);
lean::dec(x_15);
lean::dec(x_3);
x_17 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
return x_17;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("|");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = l_Lean_Parser_maxPrec;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::mk_string(":=");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_8);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_18, 0, x_8);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_13);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_9);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_command_equation;
x_26 = l_Lean_Parser_command_equation_HasView;
x_27 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_25, x_24, x_26);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_27;
}
}
obj* _init_l_Lean_Parser_command_equation_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_1 = lean::mk_string("|");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = l_Lean_Parser_maxPrec;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::mk_string(":=");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_14, 0, x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_Lean_Parser_command_equation_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_equation;
x_6 = l_Lean_Parser_command_equation_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("simpleDeclVal");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::box(3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_command_simpleDeclVal;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
x_13 = l_Lean_Parser_command_simpleDeclVal;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
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
x_7 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
lean::cnstr_set(x_2, 0, x_10);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_8);
lean::free_heap_obj(x_2);
x_15 = lean::cnstr_get(x_6, 1);
lean::inc(x_15);
lean::dec(x_6);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
x_22 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
lean::dec(x_23);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
else
{
obj* x_31; 
lean::dec(x_23);
x_31 = lean::cnstr_get(x_21, 1);
lean::inc(x_31);
lean::dec(x_21);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
return x_35;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_simpleDeclVal_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_simpleDeclVal_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declVal() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declVal");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_declVal;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_equation_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_command_declVal_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_declVal;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
case 1:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_declVal;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
default: 
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_24 = l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2;
x_25 = l_List_map___main___rarg(x_24, x_23);
x_26 = l_Lean_Parser_noKind;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_2);
x_29 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_2);
x_32 = l_Lean_Parser_command_declVal;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
}
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_Parser_command_equation_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_equation_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declVal");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_declVal_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
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
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_dec_eq(x_22, x_31);
lean::dec(x_22);
if (x_32 == 0)
{
obj* x_33; 
lean::free_heap_obj(x_13);
x_33 = l_Lean_Parser_Syntax_asNode___main(x_28);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
lean::dec(x_33);
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
lean::dec(x_35);
x_37 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2;
x_38 = l_List_map___main___rarg(x_37, x_36);
x_39 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_28, 0);
lean::inc(x_40);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_40);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_13);
return x_41;
}
else
{
obj* x_42; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_42 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3;
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_43 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_45 = lean::apply_1(x_44, x_28);
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
else
{
obj* x_47; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_47 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_47;
}
}
}
}
}
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_13, 0);
lean::inc(x_48);
lean::dec(x_13);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
switch (lean::obj_tag(x_49)) {
case 0:
{
obj* x_50; 
lean::dec(x_48);
x_50 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_50;
}
case 1:
{
obj* x_51; 
lean::dec(x_49);
lean::dec(x_48);
x_51 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_51;
}
default: 
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_48, 1);
lean::inc(x_52);
lean::dec(x_48);
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_55 = lean::box(0);
x_56 = lean_name_dec_eq(x_53, x_55);
lean::dec(x_53);
if (x_56 == 0)
{
obj* x_57; 
lean::dec(x_54);
lean::dec(x_52);
x_57 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_57;
}
else
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_58; 
lean::dec(x_54);
x_58 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_58;
}
else
{
obj* x_59; 
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; uint8 x_62; 
x_60 = lean::cnstr_get(x_52, 0);
lean::inc(x_60);
lean::dec(x_52);
x_61 = lean::mk_nat_obj(0u);
x_62 = lean::nat_dec_eq(x_54, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(1u);
x_64 = lean::nat_dec_eq(x_54, x_63);
lean::dec(x_54);
if (x_64 == 0)
{
obj* x_65; 
x_65 = l_Lean_Parser_Syntax_asNode___main(x_60);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; 
x_66 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
lean::dec(x_65);
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
lean::dec(x_67);
x_69 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2;
x_70 = l_List_map___main___rarg(x_69, x_68);
x_71 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
}
else
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_60, 0);
lean::inc(x_72);
lean::dec(x_60);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
else
{
obj* x_75; 
lean::dec(x_60);
x_75 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3;
return x_75;
}
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_54);
x_76 = l_Lean_Parser_command_simpleDeclVal_HasView;
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_78 = lean::apply_1(x_77, x_60);
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
}
else
{
obj* x_80; 
lean::dec(x_59);
lean::dec(x_54);
lean::dec(x_52);
x_80 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_80;
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
obj* x_81; 
lean::dec(x_11);
lean::dec(x_6);
x_81 = l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4;
return x_81;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declVal_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declVal_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_1 = lean::mk_string(":=");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_2);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_7);
lean::dec(x_7);
lean::dec(x_3);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
x_10 = lean::mk_string(".");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_2);
lean::dec(x_10);
x_12 = l_Lean_Parser_command_equation_Parser_Lean_Parser_HasTokens;
x_13 = l_Lean_Parser_tokens___rarg(x_12);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_13, x_6);
lean::dec(x_13);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_15);
lean::dec(x_15);
lean::dec(x_9);
x_17 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
x_18 = l_Lean_Parser_List_cons_tokens___rarg(x_17, x_6);
lean::dec(x_17);
x_19 = l_Lean_Parser_tokens___rarg(x_18);
lean::dec(x_18);
return x_19;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string(":=");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_command_simpleDeclVal;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::mk_string(".");
x_18 = l_String_trim(x_17);
lean::dec(x_17);
lean::inc(x_18);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_8);
lean::closure_set(x_20, 2, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_Parser), 4, 0);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_12);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_16);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_26, 0, x_25);
lean::closure_set(x_26, 1, x_8);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_12);
x_28 = l_Lean_Parser_command_declVal;
x_29 = l_Lean_Parser_command_declVal_HasView;
x_30 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_28, x_27, x_29);
lean::dec(x_27);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_30;
}
}
obj* _init_l_Lean_Parser_command_declVal_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = lean::mk_string(":=");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_command_simpleDeclVal;
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::mk_string(".");
x_14 = l_String_trim(x_13);
lean::dec(x_13);
lean::inc(x_14);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_4);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_equation_Parser), 4, 0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_8);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_4);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_8);
return x_23;
}
}
obj* l_Lean_Parser_command_declVal_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declVal;
x_6 = l_Lean_Parser_command_declVal_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("relaxedInferModifier");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_command_relaxedInferModifier;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::box(3);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Parser_command_relaxedInferModifier;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_command_relaxedInferModifier;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_4);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_relaxedInferModifier;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_10; obj* x_11; obj* x_21; 
x_21 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
x_22 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2;
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
lean::dec(x_21);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_10 = x_24;
x_11 = x_25;
goto block_20;
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_10 = x_27;
x_11 = x_26;
goto block_20;
}
}
block_9:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
block_20:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_2 = x_13;
x_3 = x_16;
goto block_9;
}
}
else
{
lean::dec(x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; 
x_17 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1;
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
lean::dec(x_10);
x_19 = lean::box(0);
x_2 = x_19;
x_3 = x_18;
goto block_9;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_relaxedInferModifier_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_relaxedInferModifier_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("strictInferModifier");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_command_strictInferModifier;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::box(3);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_Lean_Parser_command_strictInferModifier;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_command_strictInferModifier;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_4);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_strictInferModifier;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
return x_24;
}
}
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_10; obj* x_11; obj* x_21; 
x_21 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
x_22 = l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2;
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
lean::dec(x_21);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_10 = x_24;
x_11 = x_25;
goto block_20;
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_10 = x_27;
x_11 = x_26;
goto block_20;
}
}
block_9:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
block_20:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_2 = x_13;
x_3 = x_16;
goto block_9;
}
}
else
{
lean::dec(x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; 
x_17 = l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1;
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
lean::dec(x_10);
x_19 = lean::box(0);
x_2 = x_19;
x_3 = x_18;
goto block_9;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_strictInferModifier_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_strictInferModifier_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_inferModifier() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("inferModifier");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_inferModifier_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_inferModifier;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Lean_Parser_command_strictInferModifier_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_inferModifier;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("inferModifier");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_17; 
lean::dec(x_15);
x_17 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_17;
}
case 1:
{
obj* x_18; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_18;
}
default: 
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_20, x_22);
lean::dec(x_20);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_21);
lean::dec(x_19);
x_24 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::nat_dec_eq(x_21, x_28);
lean::dec(x_21);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = l_Lean_Parser_command_strictInferModifier_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::apply_1(x_31, x_27);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = l_Lean_Parser_command_relaxedInferModifier_HasView;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_27);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
else
{
obj* x_38; 
lean::dec(x_26);
lean::dec(x_21);
lean::dec(x_19);
x_38 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_38;
}
}
}
}
}
}
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_6);
x_39 = l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1;
return x_39;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_inferModifier_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = lean::mk_string("{");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::mk_string("}");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_2);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_7);
lean::dec(x_7);
lean::dec(x_3);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
x_11 = lean::mk_string("(");
x_12 = l_Lean_Parser_symbol_tokens___rarg(x_11, x_2);
lean::dec(x_11);
x_13 = lean::mk_string(")");
x_14 = l_Lean_Parser_symbol_tokens___rarg(x_13, x_2);
lean::dec(x_13);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_6);
lean::dec(x_14);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_15);
lean::dec(x_15);
lean::dec(x_12);
x_17 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
x_18 = l_Lean_Parser_tokens___rarg(x_17);
lean::dec(x_17);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_6);
lean::dec(x_18);
x_20 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_19);
lean::dec(x_19);
lean::dec(x_10);
x_21 = l_Lean_Parser_tokens___rarg(x_20);
lean::dec(x_20);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_21, x_6);
lean::dec(x_21);
x_23 = l_Lean_Parser_tokens___rarg(x_22);
lean::dec(x_22);
return x_23;
}
}
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_Lean_Parser_command_relaxedInferModifier;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_6, x_1, x_2, x_3, x_4, x_5);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_9);
lean::cnstr_set(x_7, 0, x_10);
return x_7;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
}
obj* l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_Lean_Parser_command_strictInferModifier;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_6, x_1, x_2, x_3, x_4, x_5);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_9);
lean::cnstr_set(x_7, 0, x_10);
return x_7;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("{");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::mk_string("}");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::mk_string("(");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_8);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::mk_string(")");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_8);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_14);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2), 5, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_14);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_17);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_31, 0, x_30);
lean::closure_set(x_31, 1, x_8);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_14);
x_33 = l_Lean_Parser_command_inferModifier;
x_34 = l_Lean_Parser_command_inferModifier_HasView;
x_35 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_33, x_32, x_34);
lean::dec(x_32);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_35;
}
}
obj* _init_l_Lean_Parser_command_inferModifier_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_1 = lean::mk_string("{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("}");
x_7 = l_String_trim(x_6);
lean::dec(x_6);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_4);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::mk_string("(");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::mk_string(")");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasView___lambda__2), 5, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_13);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_4);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
return x_28;
}
}
obj* l_Lean_Parser_command_inferModifier_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_inferModifier;
x_6 = l_Lean_Parser_command_inferModifier_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_introRule() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("introRule");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_introRule_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_3);
x_7 = l_Lean_Parser_command_optDeclSig_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::apply_1(x_8, x_5);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_command_introRule;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_19 = lean::cnstr_get(x_4, 0);
lean::inc(x_19);
lean::dec(x_4);
x_20 = l_Lean_Parser_command_inferModifier_HasView;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_22 = lean::apply_1(x_21, x_19);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_10);
x_24 = l_Lean_Parser_noKind;
x_25 = l_Lean_Parser_Syntax_mkNode(x_24, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::box(3);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = l_Lean_Parser_command_introRule;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_2, 0);
lean::inc(x_32);
lean::dec(x_2);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::obj_tag(x_4) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_11);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_command_introRule;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_40 = lean::cnstr_get(x_4, 0);
lean::inc(x_40);
lean::dec(x_4);
x_41 = l_Lean_Parser_command_inferModifier_HasView;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
x_43 = lean::apply_1(x_42, x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_10);
x_45 = l_Lean_Parser_noKind;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_11);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_6);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_33);
lean::cnstr_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_command_introRule;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
}
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_inferModifier_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_optDeclSig_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_5 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_6 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
lean::free_heap_obj(x_3);
x_11 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_12 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_1);
lean::cnstr_set(x_13, 3, x_12);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_16 = l_Lean_Parser_command_inferModifier_HasView;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_15);
lean::cnstr_set(x_3, 0, x_18);
x_19 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_20 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set(x_21, 2, x_3);
lean::cnstr_set(x_21, 3, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::dec(x_10);
lean::free_heap_obj(x_3);
x_22 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_23 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_24 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_3, 0);
lean::inc(x_26);
lean::dec(x_3);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_29 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_1);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_27, 0);
lean::inc(x_32);
lean::dec(x_27);
x_33 = l_Lean_Parser_command_inferModifier_HasView;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::apply_1(x_34, x_32);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_38 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_1);
lean::cnstr_set(x_39, 1, x_37);
lean::cnstr_set(x_39, 2, x_36);
lean::cnstr_set(x_39, 3, x_38);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_27);
x_40 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_41 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_42 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_43 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_43, 0, x_1);
lean::cnstr_set(x_43, 1, x_40);
lean::cnstr_set(x_43, 2, x_41);
lean::cnstr_set(x_43, 3, x_42);
return x_43;
}
}
}
}
}
}
obj* l_Lean_Parser_command_introRule_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_100; 
x_100 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; 
x_101 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3;
return x_101;
}
else
{
obj* x_102; obj* x_103; 
x_102 = lean::cnstr_get(x_100, 0);
lean::inc(x_102);
lean::dec(x_100);
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
lean::dec(x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; 
x_104 = lean::box(3);
x_2 = x_103;
x_3 = x_104;
goto block_99;
}
else
{
obj* x_105; obj* x_106; 
x_105 = lean::cnstr_get(x_103, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
lean::dec(x_103);
x_2 = x_106;
x_3 = x_105;
goto block_99;
}
}
block_99:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_96; obj* x_97; 
x_96 = lean::cnstr_get(x_3, 0);
lean::inc(x_96);
lean::dec(x_3);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
x_4 = x_97;
goto block_95;
}
else
{
obj* x_98; 
lean::dec(x_3);
x_98 = lean::box(0);
x_4 = x_98;
goto block_95;
}
block_95:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_92; 
x_92 = lean::box(3);
x_5 = x_2;
x_6 = x_92;
goto block_91;
}
else
{
obj* x_93; obj* x_94; 
x_93 = lean::cnstr_get(x_2, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_2, 1);
lean::inc(x_94);
lean::dec(x_2);
x_5 = x_94;
x_6 = x_93;
goto block_91;
}
block_91:
{
obj* x_7; 
if (lean::obj_tag(x_6) == 1)
{
obj* x_89; 
x_89 = lean::cnstr_get(x_6, 0);
lean::inc(x_89);
lean::dec(x_6);
x_7 = x_89;
goto block_88;
}
else
{
obj* x_90; 
lean::dec(x_6);
x_90 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_7 = x_90;
goto block_88;
}
block_88:
{
obj* x_8; obj* x_9; 
if (lean::obj_tag(x_5) == 0)
{
obj* x_85; 
x_85 = lean::box(3);
x_8 = x_5;
x_9 = x_85;
goto block_84;
}
else
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_5, 0);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_5, 1);
lean::inc(x_87);
lean::dec(x_5);
x_8 = x_87;
x_9 = x_86;
goto block_84;
}
block_84:
{
obj* x_10; 
x_10 = l_Lean_Parser_Syntax_asNode___main(x_9);
if (lean::obj_tag(x_10) == 0)
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_12 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_7);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_15 = l_Lean_Parser_command_optDeclSig_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
x_18 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_4);
lean::cnstr_set(x_19, 1, x_7);
lean::cnstr_set(x_19, 2, x_18);
lean::cnstr_set(x_19, 3, x_17);
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_10);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_10, 0);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
lean::free_heap_obj(x_10);
x_23 = lean::box(0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_24; obj* x_25; 
x_24 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_7);
lean::cnstr_set(x_25, 2, x_23);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
lean::dec(x_8);
x_27 = l_Lean_Parser_command_optDeclSig_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::apply_1(x_28, x_26);
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_4);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_23);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
lean::dec(x_22);
x_33 = l_Lean_Parser_command_inferModifier_HasView;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::apply_1(x_34, x_32);
lean::cnstr_set(x_10, 0, x_35);
if (lean::obj_tag(x_8) == 0)
{
obj* x_36; obj* x_37; 
x_36 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_7);
lean::cnstr_set(x_37, 2, x_10);
lean::cnstr_set(x_37, 3, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_8, 0);
lean::inc(x_38);
lean::dec(x_8);
x_39 = l_Lean_Parser_command_optDeclSig_HasView;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::apply_1(x_40, x_38);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_4);
lean::cnstr_set(x_42, 1, x_7);
lean::cnstr_set(x_42, 2, x_10);
lean::cnstr_set(x_42, 3, x_41);
return x_42;
}
}
else
{
lean::dec(x_31);
lean::dec(x_22);
lean::free_heap_obj(x_10);
if (lean::obj_tag(x_8) == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_44 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_4);
lean::cnstr_set(x_45, 1, x_7);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_8, 0);
lean::inc(x_46);
lean::dec(x_8);
x_47 = l_Lean_Parser_command_optDeclSig_HasView;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::apply_1(x_48, x_46);
x_50 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_4);
lean::cnstr_set(x_51, 1, x_7);
lean::cnstr_set(x_51, 2, x_50);
lean::cnstr_set(x_51, 3, x_49);
return x_51;
}
}
}
}
else
{
obj* x_52; obj* x_53; 
x_52 = lean::cnstr_get(x_10, 0);
lean::inc(x_52);
lean::dec(x_10);
x_53 = lean::cnstr_get(x_52, 1);
lean::inc(x_53);
lean::dec(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; 
x_54 = lean::box(0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_55; obj* x_56; 
x_55 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_4);
lean::cnstr_set(x_56, 1, x_7);
lean::cnstr_set(x_56, 2, x_54);
lean::cnstr_set(x_56, 3, x_55);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_8, 0);
lean::inc(x_57);
lean::dec(x_8);
x_58 = l_Lean_Parser_command_optDeclSig_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::apply_1(x_59, x_57);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_4);
lean::cnstr_set(x_61, 1, x_7);
lean::cnstr_set(x_61, 2, x_54);
lean::cnstr_set(x_61, 3, x_60);
return x_61;
}
}
else
{
obj* x_62; 
x_62 = lean::cnstr_get(x_53, 1);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_53, 0);
lean::inc(x_63);
lean::dec(x_53);
x_64 = l_Lean_Parser_command_inferModifier_HasView;
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_66 = lean::apply_1(x_65, x_63);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
if (lean::obj_tag(x_8) == 0)
{
obj* x_68; obj* x_69; 
x_68 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_4);
lean::cnstr_set(x_69, 1, x_7);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_68);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::cnstr_get(x_8, 0);
lean::inc(x_70);
lean::dec(x_8);
x_71 = l_Lean_Parser_command_optDeclSig_HasView;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_73 = lean::apply_1(x_72, x_70);
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_4);
lean::cnstr_set(x_74, 1, x_7);
lean::cnstr_set(x_74, 2, x_67);
lean::cnstr_set(x_74, 3, x_73);
return x_74;
}
}
else
{
lean::dec(x_62);
lean::dec(x_53);
if (lean::obj_tag(x_8) == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_76 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_4);
lean::cnstr_set(x_77, 1, x_7);
lean::cnstr_set(x_77, 2, x_75);
lean::cnstr_set(x_77, 3, x_76);
return x_77;
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_8, 0);
lean::inc(x_78);
lean::dec(x_8);
x_79 = l_Lean_Parser_command_optDeclSig_HasView;
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_81 = lean::apply_1(x_80, x_78);
x_82 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_83 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_83, 0, x_4);
lean::cnstr_set(x_83, 1, x_7);
lean::cnstr_set(x_83, 2, x_82);
lean::cnstr_set(x_83, 3, x_81);
return x_83;
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
obj* _init_l_Lean_Parser_command_introRule_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_introRule_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_introRule_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_5);
x_6 = l_Lean_Parser_token(x_5, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_6, 1);
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_7);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_7, 0);
x_13 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
if (lean::obj_tag(x_12) == 1)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
lean::dec(x_3);
x_37 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_37);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_7);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_38);
x_40 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_41 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_39, x_40);
x_42 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_41);
lean::cnstr_set(x_6, 0, x_42);
return x_6;
}
else
{
obj* x_43; 
lean::free_heap_obj(x_7);
lean::dec(x_12);
lean::free_heap_obj(x_6);
x_43 = lean::box(0);
x_15 = x_43;
goto block_36;
}
block_36:
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
lean::dec(x_15);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_3);
x_17 = lean::box(0);
x_18 = l_String_splitAux___main___closed__1;
x_19 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_20 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_18, x_19, x_16, x_17, x_5, x_13, x_9);
lean::dec(x_5);
lean::dec(x_16);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_22);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_23);
x_26 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_25, x_19);
x_27 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_26);
lean::cnstr_set(x_20, 0, x_27);
return x_20;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_20, 0);
x_29 = lean::cnstr_get(x_20, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_20);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_28);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
x_33 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_32, x_19);
x_34 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_29);
return x_35;
}
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::cnstr_get(x_7, 0);
x_45 = lean::cnstr_get(x_7, 1);
x_46 = lean::cnstr_get(x_7, 2);
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_7);
if (lean::obj_tag(x_44) == 1)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_5);
lean::dec(x_3);
x_63 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_44);
lean::cnstr_set(x_64, 1, x_45);
lean::cnstr_set(x_64, 2, x_63);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_64);
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_65);
x_67 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_68 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_66, x_67);
x_69 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_68);
lean::cnstr_set(x_6, 0, x_69);
return x_6;
}
else
{
obj* x_70; 
lean::dec(x_44);
lean::free_heap_obj(x_6);
x_70 = lean::box(0);
x_47 = x_70;
goto block_62;
}
block_62:
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_47);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_3);
x_49 = lean::box(0);
x_50 = l_String_splitAux___main___closed__1;
x_51 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_52 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_50, x_51, x_48, x_49, x_5, x_45, x_9);
lean::dec(x_5);
lean::dec(x_48);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_55 = x_52;
} else {
 lean::dec_ref(x_52);
 x_55 = lean::box(0);
}
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_53);
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_56);
x_59 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_58, x_51);
x_60 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_59);
if (lean::is_scalar(x_55)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_55;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_54);
return x_61;
}
}
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_6, 1);
lean::inc(x_71);
lean::dec(x_6);
x_72 = lean::cnstr_get(x_7, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_7, 1);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_7, 2);
lean::inc(x_74);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_75 = x_7;
} else {
 lean::dec_ref(x_7);
 x_75 = lean::box(0);
}
if (lean::obj_tag(x_72) == 1)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_5);
lean::dec(x_3);
x_92 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_75;
}
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_73);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_93);
x_95 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_92, x_94);
x_96 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_97 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_95, x_96);
x_98 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_97);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_71);
return x_99;
}
else
{
obj* x_100; 
lean::dec(x_75);
lean::dec(x_72);
x_100 = lean::box(0);
x_76 = x_100;
goto block_91;
}
block_91:
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_76);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_3);
x_78 = lean::box(0);
x_79 = l_String_splitAux___main___closed__1;
x_80 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_81 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_79, x_80, x_77, x_78, x_5, x_73, x_71);
lean::dec(x_5);
lean::dec(x_77);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_81, 1);
lean::inc(x_83);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_84 = x_81;
} else {
 lean::dec_ref(x_81);
 x_84 = lean::box(0);
}
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_82);
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_85);
x_88 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_87, x_80);
x_89 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_88);
if (lean::is_scalar(x_84)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_84;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
return x_90;
}
}
}
else
{
uint8 x_101; 
lean::dec(x_5);
lean::dec(x_3);
x_101 = !lean::is_exclusive(x_6);
if (x_101 == 0)
{
obj* x_102; uint8 x_103; 
x_102 = lean::cnstr_get(x_6, 0);
lean::dec(x_102);
x_103 = !lean::is_exclusive(x_7);
if (x_103 == 0)
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_104 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_7);
x_106 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_107 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_105, x_106);
x_108 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_107);
lean::cnstr_set(x_6, 0, x_108);
return x_6;
}
else
{
obj* x_109; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_109 = lean::cnstr_get(x_7, 0);
x_110 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_109);
lean::dec(x_7);
x_111 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_111, 0, x_109);
lean::cnstr_set_scalar(x_111, sizeof(void*)*1, x_110);
x_112 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_111);
x_114 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_115 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_113, x_114);
x_116 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_115);
lean::cnstr_set(x_6, 0, x_116);
return x_6;
}
}
else
{
obj* x_117; obj* x_118; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_117 = lean::cnstr_get(x_6, 1);
lean::inc(x_117);
lean::dec(x_6);
x_118 = lean::cnstr_get(x_7, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_120 = x_7;
} else {
 lean::dec_ref(x_7);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_122, x_121);
x_124 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_NotationSpec_foldAction_Parser_Lean_Parser_HasTokens___spec__4___rarg___closed__1;
x_125 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_123, x_124);
x_126 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_125);
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_117);
return x_127;
}
}
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::mk_string("|");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_tokens___rarg(x_5);
x_7 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_4);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_8);
lean::dec(x_8);
lean::dec(x_6);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_10);
lean::dec(x_10);
lean::dec(x_3);
x_12 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
return x_12;
}
}
obj* l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("|");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_command_introRule;
x_22 = l_Lean_Parser_command_introRule_HasView;
x_23 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_21, x_20, x_22);
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_23;
}
}
obj* _init_l_Lean_Parser_command_introRule_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::mk_string("|");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_Lean_Parser_command_introRule_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_introRule;
x_6 = l_Lean_Parser_command_introRule_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structBinderContent");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(obj* x_1) {
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
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(x_5);
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
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(x_2);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
x_9 = l_Lean_Parser_command_optDeclSig_HasView;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_4);
x_12 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_command_structBinderContent;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_21 = l_Lean_Parser_Term_binderDefault_HasView;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_23 = lean::apply_1(x_22, x_20);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_12);
x_25 = l_Lean_Parser_Syntax_mkNode(x_7, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_11);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_command_structBinderContent;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_3, 0);
lean::inc(x_33);
lean::dec(x_3);
x_34 = l_Lean_Parser_command_inferModifier_HasView;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_33);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_12);
x_38 = l_Lean_Parser_Syntax_mkNode(x_7, x_37);
if (lean::obj_tag(x_5) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_11);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_8);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_command_structBinderContent;
x_44 = l_Lean_Parser_Syntax_mkNode(x_43, x_42);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
lean::dec(x_5);
x_46 = l_Lean_Parser_Term_binderDefault_HasView;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_12);
x_50 = l_Lean_Parser_Syntax_mkNode(x_7, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_12);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_11);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_38);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_8);
lean::cnstr_set(x_54, 1, x_53);
x_55 = l_Lean_Parser_command_structBinderContent;
x_56 = l_Lean_Parser_Syntax_mkNode(x_55, x_54);
return x_56;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(obj* x_1) {
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_5);
if (lean::obj_tag(x_4) == 1)
{
obj* x_7; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_7);
return x_1;
}
else
{
obj* x_8; 
lean::dec(x_4);
x_8 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
lean::cnstr_set(x_1, 1, x_6);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_1);
x_11 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_10);
if (lean::obj_tag(x_9) == 1)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_9);
x_14 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_11);
return x_15;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::mk_string("NOTAnIdent");
lean::inc(x_2);
x_3 = l_Lean_Parser_Substring_ofString(x_2);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
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
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_61; obj* x_62; 
x_61 = lean::box(3);
x_62 = l_Lean_Parser_Syntax_asNode___main(x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; 
x_63 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_1 = x_63;
goto block_60;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
lean::dec(x_62);
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
lean::dec(x_64);
x_66 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_65);
x_1 = x_66;
goto block_60;
}
block_60:
{
obj* x_2; obj* x_37; obj* x_38; 
x_37 = lean::box(3);
x_38 = l_Lean_Parser_Syntax_asNode___main(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; 
x_39 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_2 = x_39;
goto block_36;
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_38);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_38, 0);
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; 
lean::free_heap_obj(x_38);
x_43 = lean::box(0);
x_2 = x_43;
goto block_36;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
lean::dec(x_42);
x_46 = l_Lean_Parser_command_inferModifier_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_45);
lean::cnstr_set(x_38, 0, x_48);
x_2 = x_38;
goto block_36;
}
else
{
obj* x_49; 
lean::dec(x_44);
lean::dec(x_42);
lean::free_heap_obj(x_38);
x_49 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_2 = x_49;
goto block_36;
}
}
}
else
{
obj* x_50; obj* x_51; 
x_50 = lean::cnstr_get(x_38, 0);
lean::inc(x_50);
lean::dec(x_38);
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; 
x_52 = lean::box(0);
x_2 = x_52;
goto block_36;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
lean::dec(x_51);
x_55 = l_Lean_Parser_command_inferModifier_HasView;
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_57 = lean::apply_1(x_56, x_54);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_2 = x_58;
goto block_36;
}
else
{
obj* x_59; 
lean::dec(x_53);
lean::dec(x_51);
x_59 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_2 = x_59;
goto block_36;
}
}
}
}
block_36:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Lean_Parser_command_optDeclSig_HasView;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_4, x_5);
x_7 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_8);
return x_9;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; 
lean::free_heap_obj(x_7);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_13);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_17 = l_Lean_Parser_Term_binderDefault_HasView;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::apply_1(x_18, x_16);
lean::cnstr_set(x_7, 0, x_19);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set(x_20, 2, x_6);
lean::cnstr_set(x_20, 3, x_7);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_15);
lean::dec(x_12);
lean::free_heap_obj(x_7);
x_21 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_6);
lean::cnstr_set(x_22, 3, x_21);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_7, 0);
lean::inc(x_23);
lean::dec(x_7);
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_2);
lean::cnstr_set(x_26, 2, x_6);
lean::cnstr_set(x_26, 3, x_25);
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_28 = lean::cnstr_get(x_24, 0);
lean::inc(x_28);
lean::dec(x_24);
x_29 = l_Lean_Parser_Term_binderDefault_HasView;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_31 = lean::apply_1(x_30, x_28);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_6);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; 
lean::dec(x_27);
lean::dec(x_24);
x_34 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_35 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_2);
lean::cnstr_set(x_35, 2, x_6);
lean::cnstr_set(x_35, 3, x_34);
return x_35;
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_111; 
x_111 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_111) == 0)
{
obj* x_112; 
x_112 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2;
return x_112;
}
else
{
obj* x_113; obj* x_114; 
x_113 = lean::cnstr_get(x_111, 0);
lean::inc(x_113);
lean::dec(x_111);
x_114 = lean::cnstr_get(x_113, 1);
lean::inc(x_114);
lean::dec(x_113);
if (lean::obj_tag(x_114) == 0)
{
obj* x_115; 
x_115 = lean::box(3);
x_2 = x_114;
x_3 = x_115;
goto block_110;
}
else
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_2 = x_117;
x_3 = x_116;
goto block_110;
}
}
block_110:
{
obj* x_4; obj* x_105; 
x_105 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; 
x_106 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_4 = x_106;
goto block_104;
}
else
{
obj* x_107; obj* x_108; obj* x_109; 
x_107 = lean::cnstr_get(x_105, 0);
lean::inc(x_107);
lean::dec(x_105);
x_108 = lean::cnstr_get(x_107, 1);
lean::inc(x_108);
lean::dec(x_107);
x_109 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_108);
x_4 = x_109;
goto block_104;
}
block_104:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_101; 
x_101 = lean::box(3);
x_5 = x_2;
x_6 = x_101;
goto block_100;
}
else
{
obj* x_102; obj* x_103; 
x_102 = lean::cnstr_get(x_2, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_2, 1);
lean::inc(x_103);
lean::dec(x_2);
x_5 = x_103;
x_6 = x_102;
goto block_100;
}
block_100:
{
obj* x_7; obj* x_78; 
x_78 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; 
x_79 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_7 = x_79;
goto block_77;
}
else
{
uint8 x_80; 
x_80 = !lean::is_exclusive(x_78);
if (x_80 == 0)
{
obj* x_81; obj* x_82; 
x_81 = lean::cnstr_get(x_78, 0);
x_82 = lean::cnstr_get(x_81, 1);
lean::inc(x_82);
lean::dec(x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; 
lean::free_heap_obj(x_78);
x_83 = lean::box(0);
x_7 = x_83;
goto block_77;
}
else
{
obj* x_84; 
x_84 = lean::cnstr_get(x_82, 1);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
lean::dec(x_82);
x_86 = l_Lean_Parser_command_inferModifier_HasView;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::apply_1(x_87, x_85);
lean::cnstr_set(x_78, 0, x_88);
x_7 = x_78;
goto block_77;
}
else
{
obj* x_89; 
lean::dec(x_84);
lean::dec(x_82);
lean::free_heap_obj(x_78);
x_89 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_7 = x_89;
goto block_77;
}
}
}
else
{
obj* x_90; obj* x_91; 
x_90 = lean::cnstr_get(x_78, 0);
lean::inc(x_90);
lean::dec(x_78);
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; 
x_92 = lean::box(0);
x_7 = x_92;
goto block_77;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_91, 0);
lean::inc(x_94);
lean::dec(x_91);
x_95 = l_Lean_Parser_command_inferModifier_HasView;
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::apply_1(x_96, x_94);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
x_7 = x_98;
goto block_77;
}
else
{
obj* x_99; 
lean::dec(x_93);
lean::dec(x_91);
x_99 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_7 = x_99;
goto block_77;
}
}
}
}
block_77:
{
obj* x_8; obj* x_9; 
if (lean::obj_tag(x_5) == 0)
{
obj* x_74; 
x_74 = lean::box(3);
x_8 = x_5;
x_9 = x_74;
goto block_73;
}
else
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_5, 1);
lean::inc(x_76);
lean::dec(x_5);
x_8 = x_76;
x_9 = x_75;
goto block_73;
}
block_73:
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = l_Lean_Parser_command_optDeclSig_HasView;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_9);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::box(3);
x_14 = l_Lean_Parser_Syntax_asNode___main(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
x_15 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_7);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_15);
return x_16;
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_14, 0);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
lean::free_heap_obj(x_14);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_7);
lean::cnstr_set(x_21, 2, x_12);
lean::cnstr_set(x_21, 3, x_20);
return x_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_19, 0);
lean::inc(x_23);
lean::dec(x_19);
x_24 = l_Lean_Parser_Term_binderDefault_HasView;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::apply_1(x_25, x_23);
lean::cnstr_set(x_14, 0, x_26);
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_7);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_14);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_19);
lean::free_heap_obj(x_14);
x_28 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_29, 0, x_4);
lean::cnstr_set(x_29, 1, x_7);
lean::cnstr_set(x_29, 2, x_12);
lean::cnstr_set(x_29, 3, x_28);
return x_29;
}
}
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_14, 0);
lean::inc(x_30);
lean::dec(x_14);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_7);
lean::cnstr_set(x_33, 2, x_12);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_36 = l_Lean_Parser_Term_binderDefault_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::apply_1(x_37, x_35);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_40, 0, x_4);
lean::cnstr_set(x_40, 1, x_7);
lean::cnstr_set(x_40, 2, x_12);
lean::cnstr_set(x_40, 3, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_42; 
lean::dec(x_34);
lean::dec(x_31);
x_41 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_4);
lean::cnstr_set(x_42, 1, x_7);
lean::cnstr_set(x_42, 2, x_12);
lean::cnstr_set(x_42, 3, x_41);
return x_42;
}
}
}
}
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_8, 0);
lean::inc(x_43);
lean::dec(x_8);
x_44 = l_Lean_Parser_Syntax_asNode___main(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; 
x_45 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_4);
lean::cnstr_set(x_46, 1, x_7);
lean::cnstr_set(x_46, 2, x_12);
lean::cnstr_set(x_46, 3, x_45);
return x_46;
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_44);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_44, 0);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; 
lean::free_heap_obj(x_44);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_4);
lean::cnstr_set(x_51, 1, x_7);
lean::cnstr_set(x_51, 2, x_12);
lean::cnstr_set(x_51, 3, x_50);
return x_51;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
lean::dec(x_49);
x_54 = l_Lean_Parser_Term_binderDefault_HasView;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_56 = lean::apply_1(x_55, x_53);
lean::cnstr_set(x_44, 0, x_56);
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_4);
lean::cnstr_set(x_57, 1, x_7);
lean::cnstr_set(x_57, 2, x_12);
lean::cnstr_set(x_57, 3, x_44);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_52);
lean::dec(x_49);
lean::free_heap_obj(x_44);
x_58 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_4);
lean::cnstr_set(x_59, 1, x_7);
lean::cnstr_set(x_59, 2, x_12);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_61; 
x_60 = lean::cnstr_get(x_44, 0);
lean::inc(x_60);
lean::dec(x_44);
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; 
x_62 = lean::box(0);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_4);
lean::cnstr_set(x_63, 1, x_7);
lean::cnstr_set(x_63, 2, x_12);
lean::cnstr_set(x_63, 3, x_62);
return x_63;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_61, 0);
lean::inc(x_65);
lean::dec(x_61);
x_66 = l_Lean_Parser_Term_binderDefault_HasView;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::apply_1(x_67, x_65);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_70, 0, x_4);
lean::cnstr_set(x_70, 1, x_7);
lean::cnstr_set(x_70, 2, x_12);
lean::cnstr_set(x_70, 3, x_69);
return x_70;
}
else
{
obj* x_71; obj* x_72; 
lean::dec(x_64);
lean::dec(x_61);
x_71 = l_Lean_Parser_Term_binderContent_HasView_x27___lambda__1___closed__1;
x_72 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_72, 0, x_4);
lean::cnstr_set(x_72, 1, x_7);
lean::cnstr_set(x_72, 2, x_12);
lean::cnstr_set(x_72, 3, x_71);
return x_72;
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
obj* _init_l_Lean_Parser_command_structBinderContent_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structBinderContent_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_tokens___rarg(x_1);
x_3 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_4 = l_Lean_Parser_tokens___rarg(x_3);
x_5 = l_Lean_Parser_Term_binderDefault_Parser_Lean_Parser_HasTokens;
x_6 = l_Lean_Parser_tokens___rarg(x_5);
x_7 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_9 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_8);
lean::dec(x_8);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_2, x_11);
lean::dec(x_11);
lean::dec(x_2);
x_13 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault_Parser), 5, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::box(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_command_structBinderContent;
x_22 = l_Lean_Parser_command_structBinderContent_HasView;
x_23 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_21, x_20, x_22);
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_23;
}
}
obj* _init_l_Lean_Parser_command_structBinderContent_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_4 = 0;
x_5 = lean::box(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_binderDefault_Parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_Lean_Parser_command_structBinderContent_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structBinderContent;
x_6 = l_Lean_Parser_command_structBinderContent_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structExplicitBinderContent");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_notationLike_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_structExplicitBinderContent;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Lean_Parser_command_structBinderContent_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_structExplicitBinderContent;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_notationLike_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structExplicitBinderContent");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_17; 
lean::dec(x_15);
x_17 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_17;
}
case 1:
{
obj* x_18; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_18;
}
default: 
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_20, x_22);
lean::dec(x_20);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_21);
lean::dec(x_19);
x_24 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::nat_dec_eq(x_21, x_28);
lean::dec(x_21);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = l_Lean_Parser_command_structBinderContent_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::apply_1(x_31, x_27);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = l_Lean_Parser_command_notationLike_HasView;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_27);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
else
{
obj* x_38; 
lean::dec(x_26);
lean::dec(x_21);
lean::dec(x_19);
x_38 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_38;
}
}
}
}
}
}
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_6);
x_39 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1;
return x_39;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinderContent_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structExplicitBinderContent_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structExplicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_structExplicitBinder;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_structExplicitBinder;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_structExplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_structExplicitBinder;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_3, x_4);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_17; obj* x_18; obj* x_31; 
x_31 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3;
return x_32;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_17 = x_34;
x_18 = x_35;
goto block_30;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_17 = x_37;
x_18 = x_36;
goto block_30;
}
}
block_16:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structExplicitBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_7);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
}
block_30:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::box(0);
x_22 = l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_17, 1);
lean::inc(x_25);
lean::dec(x_17);
x_2 = x_20;
x_3 = x_24;
x_4 = x_25;
goto block_16;
}
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_17) == 0)
{
obj* x_26; 
x_26 = l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2;
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_29 = lean::box(0);
x_2 = x_29;
x_3 = x_27;
x_4 = x_28;
goto block_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structExplicitBinder_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structExplicitBinder_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structExplicitBinder_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structImplicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_structImplicitBinder;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_structImplicitBinder;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_structImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_structImplicitBinder;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_structBinderContent_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_structBinderContent_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_3, x_4);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_17; obj* x_18; obj* x_31; 
x_31 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3;
return x_32;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_17 = x_34;
x_18 = x_35;
goto block_30;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_17 = x_37;
x_18 = x_36;
goto block_30;
}
}
block_16:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_7);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
}
block_30:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::box(0);
x_22 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_17, 1);
lean::inc(x_25);
lean::dec(x_17);
x_2 = x_20;
x_3 = x_24;
x_4 = x_25;
goto block_16;
}
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_17) == 0)
{
obj* x_26; 
x_26 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2;
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_29 = lean::box(0);
x_2 = x_29;
x_3 = x_27;
x_4 = x_28;
goto block_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structImplicitBinder_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structImplicitBinder_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structImplicitBinder_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("strictImplicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_strictImplicitBinder;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_strictImplicitBinder;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_strictImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_strictImplicitBinder;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_structBinderContent_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_3, x_4);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_17; obj* x_18; obj* x_31; 
x_31 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2;
return x_32;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_17 = x_34;
x_18 = x_35;
goto block_30;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_17 = x_37;
x_18 = x_36;
goto block_30;
}
}
block_16:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_7);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
}
block_30:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::box(0);
x_22 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_17, 1);
lean::inc(x_25);
lean::dec(x_17);
x_2 = x_20;
x_3 = x_24;
x_4 = x_25;
goto block_16;
}
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_17) == 0)
{
obj* x_26; 
x_26 = l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1;
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_29 = lean::box(0);
x_2 = x_29;
x_3 = x_27;
x_4 = x_28;
goto block_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_strictImplicitBinder_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_strictImplicitBinder_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_strictImplicitBinder_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("instImplicitBinder");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_instImplicitBinder;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_instImplicitBinder;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_instImplicitBinder;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_instImplicitBinder;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_structBinderContent_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_3, x_4);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_17; obj* x_18; obj* x_31; 
x_31 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
x_32 = l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2;
return x_32;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_17 = x_34;
x_18 = x_35;
goto block_30;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_17 = x_37;
x_18 = x_36;
goto block_30;
}
}
block_16:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structBinderContent_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_4, 0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_7);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
}
block_30:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::box(0);
x_22 = l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_17, 1);
lean::inc(x_25);
lean::dec(x_17);
x_2 = x_20;
x_3 = x_24;
x_4 = x_25;
goto block_16;
}
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_17) == 0)
{
obj* x_26; 
x_26 = l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1;
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_29 = lean::box(0);
x_2 = x_29;
x_3 = x_27;
x_4 = x_28;
goto block_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instImplicitBinder_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_instImplicitBinder_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_instImplicitBinder_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structureFieldBlock");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_structureFieldBlock;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
case 1:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Lean_Parser_command_structImplicitBinder_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_structureFieldBlock;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
case 2:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_24 = l_Lean_Parser_command_strictImplicitBinder_HasView;
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
x_26 = lean::apply_1(x_25, x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
x_28 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_2);
x_31 = l_Lean_Parser_command_structureFieldBlock;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
default: 
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_34 = l_Lean_Parser_command_instImplicitBinder_HasView;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_33);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_2);
x_38 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
x_41 = l_Lean_Parser_command_structureFieldBlock;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structureFieldBlock");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_17; 
lean::dec(x_15);
x_17 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_17;
}
case 1:
{
obj* x_18; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_18;
}
default: 
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_20, x_22);
lean::dec(x_20);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_21);
lean::dec(x_19);
x_24 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::nat_dec_eq(x_21, x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_dec_eq(x_21, x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(2u);
x_33 = lean::nat_dec_eq(x_21, x_32);
lean::dec(x_21);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = l_Lean_Parser_command_instImplicitBinder_HasView;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_27);
x_37 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = l_Lean_Parser_command_strictImplicitBinder_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::apply_1(x_39, x_27);
x_41 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_21);
x_42 = l_Lean_Parser_command_structImplicitBinder_HasView;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::apply_1(x_43, x_27);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_21);
x_46 = l_Lean_Parser_command_structExplicitBinder_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_27);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
else
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_21);
lean::dec(x_19);
x_50 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_50;
}
}
}
}
}
}
}
else
{
obj* x_51; 
lean::dec(x_11);
lean::dec(x_6);
x_51 = l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1;
return x_51;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structureFieldBlock_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_1 = lean::mk_string("(");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_command_structBinderContent_Parser_Lean_Parser_HasTokens;
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_6);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_8);
lean::dec(x_8);
lean::dec(x_5);
x_10 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
x_11 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_6);
lean::dec(x_10);
x_12 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
x_13 = lean::mk_string(")");
x_14 = l_Lean_Parser_symbol_tokens___rarg(x_13, x_2);
lean::dec(x_13);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_14, x_6);
lean::dec(x_14);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_15);
lean::dec(x_15);
lean::dec(x_12);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_16);
lean::dec(x_16);
lean::dec(x_3);
x_18 = l_Lean_Parser_tokens___rarg(x_17);
lean::dec(x_17);
x_19 = lean::mk_string("{");
x_20 = l_Lean_Parser_symbol_tokens___rarg(x_19, x_2);
lean::dec(x_19);
x_21 = lean::mk_string("}");
x_22 = l_Lean_Parser_symbol_tokens___rarg(x_21, x_2);
lean::dec(x_21);
x_23 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_6);
lean::dec(x_22);
x_24 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_23);
lean::dec(x_23);
x_25 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_24);
lean::dec(x_24);
lean::dec(x_20);
x_26 = l_Lean_Parser_tokens___rarg(x_25);
lean::dec(x_25);
x_27 = lean::mk_string("⦃");
x_28 = l_Lean_Parser_symbol_tokens___rarg(x_27, x_2);
lean::dec(x_27);
x_29 = lean::mk_string("⦄");
x_30 = l_Lean_Parser_symbol_tokens___rarg(x_29, x_2);
lean::dec(x_29);
x_31 = l_Lean_Parser_List_cons_tokens___rarg(x_30, x_6);
lean::dec(x_30);
x_32 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_31);
lean::dec(x_31);
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_28, x_32);
lean::dec(x_32);
lean::dec(x_28);
x_34 = l_Lean_Parser_tokens___rarg(x_33);
lean::dec(x_33);
x_35 = lean::mk_string("[");
x_36 = l_Lean_Parser_symbol_tokens___rarg(x_35, x_2);
lean::dec(x_35);
x_37 = lean::mk_string("]");
x_38 = l_Lean_Parser_symbol_tokens___rarg(x_37, x_2);
lean::dec(x_37);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_38, x_6);
lean::dec(x_38);
x_40 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_39);
lean::dec(x_39);
x_41 = l_Lean_Parser_List_cons_tokens___rarg(x_36, x_40);
lean::dec(x_40);
lean::dec(x_36);
x_42 = l_Lean_Parser_tokens___rarg(x_41);
lean::dec(x_41);
x_43 = l_Lean_Parser_List_cons_tokens___rarg(x_42, x_6);
lean::dec(x_42);
x_44 = l_Lean_Parser_List_cons_tokens___rarg(x_34, x_43);
lean::dec(x_43);
lean::dec(x_34);
x_45 = l_Lean_Parser_List_cons_tokens___rarg(x_26, x_44);
lean::dec(x_44);
lean::dec(x_26);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_45);
lean::dec(x_45);
lean::dec(x_18);
x_47 = l_Lean_Parser_tokens___rarg(x_46);
lean::dec(x_46);
x_48 = l_Lean_Parser_List_cons_tokens___rarg(x_47, x_6);
lean::dec(x_47);
x_49 = l_Lean_Parser_tokens___rarg(x_48);
lean::dec(x_48);
return x_49;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("(");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_Parser), 4, 0);
lean::inc(x_13);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_8);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
x_18 = l_Lean_Parser_command_structExplicitBinderContent;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_17);
x_20 = lean::mk_string(")");
x_21 = l_String_trim(x_20);
lean::dec(x_20);
lean::inc(x_21);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_8);
lean::closure_set(x_23, 2, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_12);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_structExplicitBinder;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::mk_string("{");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_8);
lean::closure_set(x_32, 2, x_31);
x_33 = lean::mk_string("}");
x_34 = l_String_trim(x_33);
lean::dec(x_33);
lean::inc(x_34);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_35, 0, x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_36, 0, x_34);
lean::closure_set(x_36, 1, x_8);
lean::closure_set(x_36, 2, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_12);
lean::inc(x_13);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_13);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_32);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_command_structImplicitBinder;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_39);
x_42 = lean::mk_string("⦃");
x_43 = l_String_trim(x_42);
lean::dec(x_42);
lean::inc(x_43);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_45, 0, x_43);
lean::closure_set(x_45, 1, x_8);
lean::closure_set(x_45, 2, x_44);
x_46 = lean::mk_string("⦄");
x_47 = l_String_trim(x_46);
lean::dec(x_46);
lean::inc(x_47);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_48, 0, x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_8);
lean::closure_set(x_49, 2, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_12);
lean::inc(x_13);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_13);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_45);
lean::cnstr_set(x_52, 1, x_51);
x_53 = l_Lean_Parser_command_strictImplicitBinder;
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_54, 0, x_53);
lean::closure_set(x_54, 1, x_52);
x_55 = lean::mk_string("[");
x_56 = l_String_trim(x_55);
lean::dec(x_55);
lean::inc(x_56);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_57, 0, x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_58, 0, x_56);
lean::closure_set(x_58, 1, x_8);
lean::closure_set(x_58, 2, x_57);
x_59 = lean::mk_string("]");
x_60 = l_String_trim(x_59);
lean::dec(x_59);
lean::inc(x_60);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_61, 0, x_60);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_62, 0, x_60);
lean::closure_set(x_62, 1, x_8);
lean::closure_set(x_62, 2, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_12);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_13);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_58);
lean::cnstr_set(x_65, 1, x_64);
x_66 = l_Lean_Parser_command_instImplicitBinder;
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_67, 0, x_66);
lean::closure_set(x_67, 1, x_65);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_12);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_54);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_41);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_28);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_72, 0, x_71);
lean::closure_set(x_72, 1, x_8);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_12);
x_74 = l_Lean_Parser_command_structureFieldBlock;
x_75 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_76 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_74, x_73, x_75);
lean::dec(x_73);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_76;
}
}
obj* _init_l_Lean_Parser_command_structureFieldBlock_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_1 = lean::mk_string("(");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structBinderContent_Parser), 4, 0);
lean::inc(x_9);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_4);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
x_14 = l_Lean_Parser_command_structExplicitBinderContent;
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_15, 0, x_14);
lean::closure_set(x_15, 1, x_13);
x_16 = lean::mk_string(")");
x_17 = l_String_trim(x_16);
lean::dec(x_16);
lean::inc(x_17);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_19, 0, x_17);
lean::closure_set(x_19, 1, x_4);
lean::closure_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_8);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_15);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_5);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_command_structExplicitBinder;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::mk_string("{");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_4);
lean::closure_set(x_28, 2, x_27);
x_29 = lean::mk_string("}");
x_30 = l_String_trim(x_29);
lean::dec(x_29);
lean::inc(x_30);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_4);
lean::closure_set(x_32, 2, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_8);
lean::inc(x_9);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_structImplicitBinder;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_35);
x_38 = lean::mk_string("⦃");
x_39 = l_String_trim(x_38);
lean::dec(x_38);
lean::inc(x_39);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_40, 0, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_41, 0, x_39);
lean::closure_set(x_41, 1, x_4);
lean::closure_set(x_41, 2, x_40);
x_42 = lean::mk_string("⦄");
x_43 = l_String_trim(x_42);
lean::dec(x_42);
lean::inc(x_43);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_44, 0, x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_45, 0, x_43);
lean::closure_set(x_45, 1, x_4);
lean::closure_set(x_45, 2, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_8);
lean::inc(x_9);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_9);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_41);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_Lean_Parser_command_strictImplicitBinder;
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_50, 0, x_49);
lean::closure_set(x_50, 1, x_48);
x_51 = lean::mk_string("[");
x_52 = l_String_trim(x_51);
lean::dec(x_51);
lean::inc(x_52);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_53, 0, x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_54, 0, x_52);
lean::closure_set(x_54, 1, x_4);
lean::closure_set(x_54, 2, x_53);
x_55 = lean::mk_string("]");
x_56 = l_String_trim(x_55);
lean::dec(x_55);
lean::inc(x_56);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_57, 0, x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_58, 0, x_56);
lean::closure_set(x_58, 1, x_4);
lean::closure_set(x_58, 2, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_8);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_54);
lean::cnstr_set(x_61, 1, x_60);
x_62 = l_Lean_Parser_command_instImplicitBinder;
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_63, 0, x_62);
lean::closure_set(x_63, 1, x_61);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_8);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_50);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_37);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_24);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_68, 0, x_67);
lean::closure_set(x_68, 1, x_4);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_8);
return x_69;
}
}
obj* l_Lean_Parser_command_structureFieldBlock_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structureFieldBlock;
x_6 = l_Lean_Parser_command_structureFieldBlock_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("oldUnivParams");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(x_3);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_oldUnivParams;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_oldUnivParams;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_oldUnivParams;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_oldUnivParams;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_1);
return x_9;
}
}
}
obj* l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_49; 
x_49 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; 
x_50 = l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1;
return x_50;
}
else
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
lean::dec(x_49);
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
lean::dec(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; 
x_53 = lean::box(3);
x_2 = x_52;
x_3 = x_53;
goto block_48;
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_52, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_2 = x_55;
x_3 = x_54;
goto block_48;
}
}
block_48:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
lean::dec(x_3);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_4 = x_46;
goto block_44;
}
else
{
obj* x_47; 
lean::dec(x_3);
x_47 = lean::box(0);
x_4 = x_47;
goto block_44;
}
block_44:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_41; 
x_41 = lean::box(3);
x_5 = x_2;
x_6 = x_41;
goto block_40;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_2, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_2, 1);
lean::inc(x_43);
lean::dec(x_2);
x_5 = x_43;
x_6 = x_42;
goto block_40;
}
block_40:
{
obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_8);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
x_16 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_8);
return x_17;
}
}
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_7);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_21 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_20);
if (lean::obj_tag(x_5) == 0)
{
obj* x_22; obj* x_23; 
lean::free_heap_obj(x_7);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
lean::dec(x_5);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
lean::cnstr_set(x_7, 0, x_25);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_4);
lean::cnstr_set(x_26, 1, x_21);
lean::cnstr_set(x_26, 2, x_7);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_24);
lean::free_heap_obj(x_7);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_31);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_5, 0);
lean::inc(x_34);
lean::dec(x_5);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::dec(x_34);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_31);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_34);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_4);
lean::cnstr_set(x_39, 1, x_31);
lean::cnstr_set(x_39, 2, x_38);
return x_39;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_oldUnivParams_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::mk_string("{");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
x_6 = lean::mk_string("}");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_2);
lean::dec(x_6);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_4);
lean::dec(x_7);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_8);
lean::dec(x_8);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_9);
lean::dec(x_9);
lean::dec(x_3);
x_11 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("{");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::mk_string("}");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_8);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_Lean_Parser_command_oldUnivParams;
x_21 = l_Lean_Parser_command_oldUnivParams_HasView;
x_22 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_20, x_19, x_21);
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_22;
}
}
obj* _init_l_Lean_Parser_command_oldUnivParams_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::mk_string("{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string("}");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_4);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_Lean_Parser_command_oldUnivParams_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_oldUnivParams;
x_6 = l_Lean_Parser_command_oldUnivParams_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_univParams() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("univParams");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_univParams_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___elambda__1___spec__1(x_3);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_Lean_Parser_command_univParams;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_command_univParams;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_command_univParams;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
lean::dec(x_4);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_command_univParams;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
}
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_1);
return x_9;
}
}
}
obj* l_Lean_Parser_command_univParams_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_49; 
x_49 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; 
x_50 = l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1;
return x_50;
}
else
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
lean::dec(x_49);
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
lean::dec(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; 
x_53 = lean::box(3);
x_2 = x_52;
x_3 = x_53;
goto block_48;
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_52, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_2 = x_55;
x_3 = x_54;
goto block_48;
}
}
block_48:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
lean::dec(x_3);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_4 = x_46;
goto block_44;
}
else
{
obj* x_47; 
lean::dec(x_3);
x_47 = lean::box(0);
x_4 = x_47;
goto block_44;
}
block_44:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_41; 
x_41 = lean::box(3);
x_5 = x_2;
x_6 = x_41;
goto block_40;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_2, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_2, 1);
lean::inc(x_43);
lean::dec(x_2);
x_5 = x_43;
x_6 = x_42;
goto block_40;
}
block_40:
{
obj* x_7; 
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_8);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
x_16 = l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_8);
return x_17;
}
}
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_7);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_21 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_20);
if (lean::obj_tag(x_5) == 0)
{
obj* x_22; obj* x_23; 
lean::free_heap_obj(x_7);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
lean::dec(x_5);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
lean::cnstr_set(x_7, 0, x_25);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_4);
lean::cnstr_set(x_26, 1, x_21);
lean::cnstr_set(x_26, 2, x_7);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_24);
lean::free_heap_obj(x_7);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
lean::dec(x_7);
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_List_map___main___at_Lean_Parser_command_structBinderContent_HasView_x27___spec__1(x_30);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_31);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_5, 0);
lean::inc(x_34);
lean::dec(x_5);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::dec(x_34);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_31);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_34);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_4);
lean::cnstr_set(x_39, 1, x_31);
lean::cnstr_set(x_39, 2, x_38);
return x_39;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_univParams_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_univParams_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_univParams_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_univParams_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("identUnivParams");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_command_identUnivParams;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_command_univParams_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_13 = lean::apply_1(x_12, x_9);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
x_15 = l_Lean_Parser_noKind;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_Lean_Parser_command_identUnivParams;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::box(0);
x_2 = lean::mk_string("NOTAnIdent");
lean::inc(x_2);
x_3 = l_Lean_Parser_Substring_ofString(x_2);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = l_Lean_Parser_command_univParams_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::box(3);
x_11 = lean::apply_1(x_9, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::mk_string("NOTAnIdent");
lean::inc(x_2);
x_3 = l_Lean_Parser_Substring_ofString(x_2);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
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
x_7 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = l_Lean_Parser_command_univParams_HasView;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_9);
lean::cnstr_set(x_2, 0, x_12);
x_13 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
else
{
obj* x_15; 
lean::dec(x_8);
lean::dec(x_6);
lean::free_heap_obj(x_2);
x_15 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
return x_15;
}
}
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
x_18 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2;
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_21 = l_Lean_Parser_command_univParams_HasView;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::apply_1(x_22, x_20);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
return x_26;
}
else
{
obj* x_27; 
lean::dec(x_19);
lean::dec(x_17);
x_27 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
return x_27;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_univParams_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_98; 
x_98 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; 
x_99 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5;
return x_99;
}
else
{
obj* x_100; obj* x_101; 
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
lean::dec(x_98);
x_101 = lean::cnstr_get(x_100, 1);
lean::inc(x_101);
lean::dec(x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; 
x_102 = lean::box(3);
x_2 = x_101;
x_3 = x_102;
goto block_97;
}
else
{
obj* x_103; obj* x_104; 
x_103 = lean::cnstr_get(x_101, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
lean::dec(x_101);
x_2 = x_104;
x_3 = x_103;
goto block_97;
}
}
block_97:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 1)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_3, 0);
lean::inc(x_34);
lean::dec(x_3);
x_35 = lean::box(3);
x_36 = l_Lean_Parser_Syntax_asNode___main(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
x_37 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
else
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_36, 0);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; 
lean::free_heap_obj(x_36);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_34);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_41, 0);
lean::inc(x_45);
lean::dec(x_41);
x_46 = l_Lean_Parser_command_univParams_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_45);
lean::cnstr_set(x_36, 0, x_48);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_34);
lean::cnstr_set(x_49, 1, x_36);
return x_49;
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_44);
lean::dec(x_41);
lean::free_heap_obj(x_36);
x_50 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
obj* x_52; obj* x_53; 
x_52 = lean::cnstr_get(x_36, 0);
lean::inc(x_52);
lean::dec(x_36);
x_53 = lean::cnstr_get(x_52, 1);
lean::inc(x_53);
lean::dec(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_55; 
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
else
{
obj* x_56; 
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_57 = lean::cnstr_get(x_53, 0);
lean::inc(x_57);
lean::dec(x_53);
x_58 = l_Lean_Parser_command_univParams_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::apply_1(x_59, x_57);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_34);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
else
{
obj* x_63; obj* x_64; 
lean::dec(x_56);
lean::dec(x_53);
x_63 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_34);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_3, 0);
lean::inc(x_65);
lean::dec(x_3);
x_66 = lean::cnstr_get(x_2, 0);
lean::inc(x_66);
lean::dec(x_2);
x_67 = l_Lean_Parser_Syntax_asNode___main(x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; 
x_68 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
}
else
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_67);
if (x_70 == 0)
{
obj* x_71; obj* x_72; 
x_71 = lean::cnstr_get(x_67, 0);
x_72 = lean::cnstr_get(x_71, 1);
lean::inc(x_72);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; 
lean::free_heap_obj(x_67);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_65);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
else
{
obj* x_75; 
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::cnstr_get(x_72, 0);
lean::inc(x_76);
lean::dec(x_72);
x_77 = l_Lean_Parser_command_univParams_HasView;
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_79 = lean::apply_1(x_78, x_76);
lean::cnstr_set(x_67, 0, x_79);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_65);
lean::cnstr_set(x_80, 1, x_67);
return x_80;
}
else
{
obj* x_81; obj* x_82; 
lean::dec(x_75);
lean::dec(x_72);
lean::free_heap_obj(x_67);
x_81 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_65);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_67, 0);
lean::inc(x_83);
lean::dec(x_67);
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
lean::dec(x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; obj* x_86; 
x_85 = lean::box(0);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_65);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
else
{
obj* x_87; 
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_88 = lean::cnstr_get(x_84, 0);
lean::inc(x_88);
lean::dec(x_84);
x_89 = l_Lean_Parser_command_univParams_HasView;
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::apply_1(x_90, x_88);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_65);
lean::cnstr_set(x_93, 1, x_92);
return x_93;
}
else
{
obj* x_94; obj* x_95; 
lean::dec(x_87);
lean::dec(x_84);
x_94 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4;
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_65);
lean::cnstr_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
}
else
{
obj* x_96; 
lean::dec(x_3);
x_96 = lean::box(0);
x_4 = x_96;
goto block_33;
}
block_33:
{
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3;
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
return x_8;
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; 
lean::free_heap_obj(x_7);
x_12 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2;
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_15 = l_Lean_Parser_command_univParams_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
lean::cnstr_set(x_7, 0, x_17);
x_18 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_7);
return x_19;
}
else
{
obj* x_20; 
lean::dec(x_13);
lean::dec(x_11);
lean::free_heap_obj(x_7);
x_20 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_7, 0);
lean::inc(x_21);
lean::dec(x_7);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2;
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
lean::dec(x_22);
x_26 = l_Lean_Parser_command_univParams_HasView;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::apply_1(x_27, x_25);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
else
{
obj* x_32; 
lean::dec(x_24);
lean::dec(x_22);
x_32 = l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1;
return x_32;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_identUnivParams_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = lean::box(0);
x_2 = lean::mk_string(".{");
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Lean_Parser_symbol_tokens___rarg(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_Parser_tokens___rarg(x_1);
x_6 = lean::mk_string("}");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_3);
lean::dec(x_6);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_8);
lean::dec(x_8);
lean::dec(x_5);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
x_11 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_tokens___rarg(x_11);
lean::dec(x_11);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_12, x_1);
lean::dec(x_12);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_13);
lean::dec(x_13);
x_15 = l_Lean_Parser_tokens___rarg(x_14);
lean::dec(x_14);
return x_15;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string(".{");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
lean::inc(x_10);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::mk_string("}");
x_13 = l_String_trim(x_12);
lean::dec(x_12);
lean::inc(x_13);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_8);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
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
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_command_identUnivParams;
x_28 = l_Lean_Parser_command_identUnivParams_HasView;
x_29 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_27, x_26, x_28);
lean::dec(x_26);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_29;
}
}
obj* _init_l_Lean_Parser_command_identUnivParams_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_1 = lean::mk_string(".{");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__3), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string("}");
x_9 = l_String_trim(x_8);
lean::dec(x_8);
lean::inc(x_9);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_4);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_command_univParams;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_15);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_6);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
obj* l_Lean_Parser_command_identUnivParams_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_identUnivParams;
x_6 = l_Lean_Parser_command_identUnivParams_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_structureKw() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structureKw");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_structureKw;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_structureKw;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_structureKw;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_structureKw;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structureKw");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structureKw_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
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
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
lean::dec(x_22);
if (x_30 == 0)
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_31);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_13);
return x_32;
}
else
{
obj* x_33; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_33 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1;
return x_33;
}
}
else
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_34);
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_13);
return x_35;
}
else
{
obj* x_36; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_36 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2;
return x_36;
}
}
}
else
{
obj* x_37; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_37 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_37;
}
}
}
}
}
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_13, 0);
lean::inc(x_38);
lean::dec(x_13);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
switch (lean::obj_tag(x_39)) {
case 0:
{
obj* x_40; 
lean::dec(x_38);
x_40 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_40;
}
case 1:
{
obj* x_41; 
lean::dec(x_39);
lean::dec(x_38);
x_41 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_41;
}
default: 
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_42 = lean::cnstr_get(x_38, 1);
lean::inc(x_42);
lean::dec(x_38);
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_45 = lean::box(0);
x_46 = lean_name_dec_eq(x_43, x_45);
lean::dec(x_43);
if (x_46 == 0)
{
obj* x_47; 
lean::dec(x_44);
lean::dec(x_42);
x_47 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_47;
}
else
{
if (lean::obj_tag(x_42) == 0)
{
obj* x_48; 
lean::dec(x_44);
x_48 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_48;
}
else
{
obj* x_49; 
x_49 = lean::cnstr_get(x_42, 1);
lean::inc(x_49);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::nat_dec_eq(x_44, x_51);
lean::dec(x_44);
if (x_52 == 0)
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
lean::dec(x_50);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
else
{
obj* x_56; 
lean::dec(x_50);
x_56 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1;
return x_56;
}
}
else
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
else
{
obj* x_60; 
lean::dec(x_50);
x_60 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2;
return x_60;
}
}
}
else
{
obj* x_61; 
lean::dec(x_49);
lean::dec(x_44);
lean::dec(x_42);
x_61 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_61;
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
obj* x_62; 
lean::dec(x_11);
lean::dec(x_6);
x_62 = l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3;
return x_62;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureKw_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_structureKw_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structureKw_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structureKw_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_extends() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("extends");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_extends_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_List_map___main___at_Lean_Parser_Term_tuple_HasView_x27___elambda__1___spec__1(x_3);
x_5 = l_List_join___main___rarg(x_4);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_Lean_Parser_command_extends;
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
x_17 = l_Lean_Parser_command_extends;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::dec(x_8);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::box(0);
lean::cnstr_set(x_3, 1, x_11);
lean::cnstr_set(x_3, 0, x_10);
return x_3;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
lean::dec(x_3);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_18 = !lean::is_exclusive(x_5);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_5, 0);
x_20 = lean::cnstr_get(x_5, 1);
x_21 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_1, x_2, x_20);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_17);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_5, 1, x_21);
lean::cnstr_set(x_5, 0, x_25);
return x_5;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_19);
x_26 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_17);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set(x_5, 1, x_21);
lean::cnstr_set(x_5, 0, x_27);
return x_5;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_5, 0);
x_29 = lean::cnstr_get(x_5, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_5);
x_30 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_1, x_2, x_29);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_17);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_28);
x_36 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_17);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_30);
return x_38;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_Term_tuple_HasView_x27___lambda__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1;
x_9 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_10 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_8, x_9, x_7);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_command_extends_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_33; 
x_33 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3;
return x_34;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
lean::dec(x_33);
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; 
x_37 = lean::box(3);
x_2 = x_36;
x_3 = x_37;
goto block_32;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_2 = x_39;
x_3 = x_38;
goto block_32;
}
}
block_32:
{
obj* x_4; obj* x_5; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
lean::dec(x_3);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
if (lean::obj_tag(x_2) == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::box(3);
x_19 = l_Lean_Parser_Syntax_asNode___main(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_Term_tuple_HasView_x27___lambda__1___closed__1;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1;
x_25 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_26 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_24, x_25, x_23);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_17);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
lean::dec(x_2);
x_4 = x_17;
x_5 = x_28;
goto block_15;
}
}
else
{
lean::dec(x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_29; 
x_29 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2;
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
lean::dec(x_2);
x_31 = lean::box(0);
x_4 = x_31;
x_5 = x_30;
goto block_15;
}
}
block_15:
{
obj* x_6; 
x_6 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_Term_tuple_HasView_x27___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1;
x_12 = l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3;
x_13 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_11, x_12, x_10);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_extends_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_extends_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_extends_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___at_Lean_Parser_command_extends_HasView_x27___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_extends_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_extends_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structureCtor() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structureCtor");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_structureCtor_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
x_6 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_Parser_Term_paren_HasView_x27___elambda__1___closed__2;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_command_structureCtor;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
x_14 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_command_structureCtor;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_20 = l_Lean_Parser_command_inferModifier_HasView;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_22 = lean::apply_1(x_21, x_19);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_6);
x_24 = l_Lean_Parser_noKind;
x_25 = l_Lean_Parser_Syntax_mkNode(x_24, x_23);
if (lean::obj_tag(x_4) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_command_structureCtor;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_4, 0);
lean::inc(x_31);
lean::dec(x_4);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_6);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_25);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_5);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_structureCtor;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
}
}
}
obj* _init_l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(3);
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_5 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
return x_6;
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::free_heap_obj(x_2);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
lean::cnstr_set(x_12, 2, x_10);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_9, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_15 = l_Lean_Parser_command_inferModifier_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
lean::cnstr_set(x_2, 0, x_17);
x_18 = lean::box(0);
x_19 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_13);
lean::dec(x_9);
lean::free_heap_obj(x_2);
x_21 = lean::box(0);
x_22 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_23 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set(x_24, 2, x_21);
return x_24;
}
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::box(0);
x_28 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_29, 2, x_27);
return x_29;
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_26, 1);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
lean::dec(x_26);
x_32 = l_Lean_Parser_command_inferModifier_HasView;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::apply_1(x_33, x_31);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::box(0);
x_37 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set(x_38, 2, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_30);
lean::dec(x_26);
x_39 = lean::box(0);
x_40 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_41 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set(x_42, 2, x_39);
return x_42;
}
}
}
}
}
}
obj* l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_67; 
x_67 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; 
x_68 = l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1;
return x_68;
}
else
{
obj* x_69; obj* x_70; 
x_69 = lean::cnstr_get(x_67, 0);
lean::inc(x_69);
lean::dec(x_67);
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; 
x_71 = lean::box(3);
x_2 = x_70;
x_3 = x_71;
goto block_66;
}
else
{
obj* x_72; obj* x_73; 
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_2 = x_73;
x_3 = x_72;
goto block_66;
}
}
block_66:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 1)
{
obj* x_64; 
x_64 = lean::cnstr_get(x_3, 0);
lean::inc(x_64);
lean::dec(x_3);
x_4 = x_64;
goto block_63;
}
else
{
obj* x_65; 
lean::dec(x_3);
x_65 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
x_4 = x_65;
goto block_63;
}
block_63:
{
obj* x_5; obj* x_6; obj* x_13; obj* x_14; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_60; 
x_60 = lean::box(3);
x_13 = x_2;
x_14 = x_60;
goto block_59;
}
else
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_2, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_2, 1);
lean::inc(x_62);
lean::dec(x_2);
x_13 = x_62;
x_14 = x_61;
goto block_59;
}
block_12:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
block_59:
{
obj* x_15; 
x_15 = l_Lean_Parser_Syntax_asNode___main(x_14);
if (lean::obj_tag(x_15) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::box(0);
x_17 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_20 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_5 = x_20;
x_6 = x_19;
goto block_12;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_15);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_15, 0);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
lean::free_heap_obj(x_15);
x_24 = lean::box(0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_25; 
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_13, 0);
lean::inc(x_26);
lean::dec(x_13);
x_5 = x_24;
x_6 = x_26;
goto block_12;
}
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_29 = l_Lean_Parser_command_inferModifier_HasView;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_31 = lean::apply_1(x_30, x_28);
lean::cnstr_set(x_15, 0, x_31);
if (lean::obj_tag(x_13) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_15);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_13, 0);
lean::inc(x_34);
lean::dec(x_13);
x_5 = x_15;
x_6 = x_34;
goto block_12;
}
}
else
{
lean::dec(x_27);
lean::dec(x_23);
lean::free_heap_obj(x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::box(0);
x_36 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_36);
lean::cnstr_set(x_37, 2, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_13, 0);
lean::inc(x_38);
lean::dec(x_13);
x_39 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_5 = x_39;
x_6 = x_38;
goto block_12;
}
}
}
}
else
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_15, 0);
lean::inc(x_40);
lean::dec(x_15);
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; 
x_42 = lean::box(0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_43; 
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_4);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_13, 0);
lean::inc(x_44);
lean::dec(x_13);
x_5 = x_42;
x_6 = x_44;
goto block_12;
}
}
else
{
obj* x_45; 
x_45 = lean::cnstr_get(x_41, 1);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
x_47 = l_Lean_Parser_command_inferModifier_HasView;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::apply_1(x_48, x_46);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
if (lean::obj_tag(x_13) == 0)
{
obj* x_51; obj* x_52; 
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_4);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_51);
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_13, 0);
lean::inc(x_53);
lean::dec(x_13);
x_5 = x_50;
x_6 = x_53;
goto block_12;
}
}
else
{
lean::dec(x_45);
lean::dec(x_41);
if (lean::obj_tag(x_13) == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::box(0);
x_55 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_4);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set(x_56, 2, x_54);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = lean::cnstr_get(x_13, 0);
lean::inc(x_57);
lean::dec(x_13);
x_58 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1;
x_5 = x_58;
x_6 = x_57;
goto block_12;
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
obj* _init_l_Lean_Parser_command_structureCtor_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureCtor_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structureCtor_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structureCtor_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structure() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("structure");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_command_structure_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 5);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_1, 6);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 7);
lean::inc(x_9);
lean::dec(x_1);
x_10 = l_Lean_Parser_command_structureKw_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_2);
x_13 = l_Lean_Parser_command_identUnivParams_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_4);
x_16 = l_Lean_Parser_command_optDeclSig_HasView;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_5);
x_19 = l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1;
x_20 = l_List_map___main___rarg(x_19, x_9);
x_21 = l_Lean_Parser_noKind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
if (lean::obj_tag(x_3) == 0)
{
obj* x_95; 
x_95 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_25 = x_95;
goto block_94;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_3, 0);
lean::inc(x_96);
lean::dec(x_3);
x_97 = l_Lean_Parser_command_oldUnivParams_HasView;
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
x_99 = lean::apply_1(x_98, x_96);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_23);
x_101 = l_Lean_Parser_Syntax_mkNode(x_21, x_100);
x_25 = x_101;
goto block_94;
}
block_94:
{
obj* x_26; obj* x_55; obj* x_56; 
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_84; 
x_84 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_26 = x_84;
goto block_54;
}
else
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_7, 0);
lean::inc(x_85);
lean::dec(x_7);
x_86 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_55 = x_86;
x_56 = x_85;
goto block_83;
}
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_6, 0);
lean::inc(x_87);
lean::dec(x_6);
x_88 = l_Lean_Parser_command_extends_HasView;
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
x_90 = lean::apply_1(x_89, x_87);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_23);
x_92 = l_Lean_Parser_Syntax_mkNode(x_21, x_91);
if (lean::obj_tag(x_7) == 0)
{
x_26 = x_92;
goto block_54;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_7, 0);
lean::inc(x_93);
lean::dec(x_7);
x_55 = x_92;
x_56 = x_93;
goto block_83;
}
}
block_54:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_27 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
x_29 = lean::box(3);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_18);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_15);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_25);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_structure;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_38 = lean::cnstr_get(x_8, 0);
lean::inc(x_38);
lean::dec(x_8);
x_39 = l_Lean_Parser_command_structureCtor_HasView;
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
x_41 = lean::apply_1(x_40, x_38);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_23);
x_43 = l_Lean_Parser_Syntax_mkNode(x_21, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_24);
x_45 = lean::box(3);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_26);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_15);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_25);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_12);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_Lean_Parser_command_structure;
x_53 = l_Lean_Parser_Syntax_mkNode(x_52, x_51);
return x_53;
}
}
block_83:
{
obj* x_57; 
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
if (lean::obj_tag(x_8) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_58 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_24);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_55);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_18);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_15);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_25);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_12);
lean::cnstr_set(x_65, 1, x_64);
x_66 = l_Lean_Parser_command_structure;
x_67 = l_Lean_Parser_Syntax_mkNode(x_66, x_65);
return x_67;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_68 = lean::cnstr_get(x_8, 0);
lean::inc(x_68);
lean::dec(x_8);
x_69 = l_Lean_Parser_command_structureCtor_HasView;
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_71 = lean::apply_1(x_70, x_68);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_23);
x_73 = l_Lean_Parser_Syntax_mkNode(x_21, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_24);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_57);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_55);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_18);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_15);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_25);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_12);
lean::cnstr_set(x_80, 1, x_79);
x_81 = l_Lean_Parser_command_structure;
x_82 = l_Lean_Parser_Syntax_mkNode(x_81, x_80);
return x_82;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_command_structureFieldBlock_HasView;
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
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_structureFieldBlock_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_structureCtor_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_extends_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_oldUnivParams_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_68; 
x_1 = l_Lean_Parser_command_structureKw_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_68 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
x_69 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_5 = x_69;
goto block_67;
}
else
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_68);
if (x_70 == 0)
{
obj* x_71; obj* x_72; 
x_71 = lean::cnstr_get(x_68, 0);
x_72 = lean::cnstr_get(x_71, 1);
lean::inc(x_72);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; 
lean::free_heap_obj(x_68);
x_73 = lean::box(0);
x_5 = x_73;
goto block_67;
}
else
{
obj* x_74; 
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_72, 0);
lean::inc(x_75);
lean::dec(x_72);
x_76 = l_Lean_Parser_command_oldUnivParams_HasView;
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_78 = lean::apply_1(x_77, x_75);
lean::cnstr_set(x_68, 0, x_78);
x_5 = x_68;
goto block_67;
}
else
{
obj* x_79; 
lean::dec(x_74);
lean::dec(x_72);
lean::free_heap_obj(x_68);
x_79 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_5 = x_79;
goto block_67;
}
}
}
else
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_68, 0);
lean::inc(x_80);
lean::dec(x_68);
x_81 = lean::cnstr_get(x_80, 1);
lean::inc(x_81);
lean::dec(x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; 
x_82 = lean::box(0);
x_5 = x_82;
goto block_67;
}
else
{
obj* x_83; 
x_83 = lean::cnstr_get(x_81, 1);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
lean::dec(x_81);
x_85 = l_Lean_Parser_command_oldUnivParams_HasView;
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_87 = lean::apply_1(x_86, x_84);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_5 = x_88;
goto block_67;
}
else
{
obj* x_89; 
lean::dec(x_83);
lean::dec(x_81);
x_89 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_5 = x_89;
goto block_67;
}
}
}
}
block_67:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_45; 
x_6 = l_Lean_Parser_command_identUnivParams_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::apply_1(x_7, x_3);
x_9 = l_Lean_Parser_command_optDeclSig_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_3);
x_45 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_12 = x_46;
goto block_44;
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_45);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_45, 0);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; 
lean::free_heap_obj(x_45);
x_50 = lean::box(0);
x_12 = x_50;
goto block_44;
}
else
{
obj* x_51; 
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
lean::dec(x_49);
x_53 = l_Lean_Parser_command_extends_HasView;
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::apply_1(x_54, x_52);
lean::cnstr_set(x_45, 0, x_55);
x_12 = x_45;
goto block_44;
}
else
{
obj* x_56; 
lean::dec(x_51);
lean::dec(x_49);
lean::free_heap_obj(x_45);
x_56 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_12 = x_56;
goto block_44;
}
}
}
else
{
obj* x_57; obj* x_58; 
x_57 = lean::cnstr_get(x_45, 0);
lean::inc(x_57);
lean::dec(x_45);
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; 
x_59 = lean::box(0);
x_12 = x_59;
goto block_44;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
lean::dec(x_58);
x_62 = l_Lean_Parser_command_extends_HasView;
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_64 = lean::apply_1(x_63, x_61);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_12 = x_65;
goto block_44;
}
else
{
obj* x_66; 
lean::dec(x_60);
lean::dec(x_58);
x_66 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_12 = x_66;
goto block_44;
}
}
}
}
block_44:
{
obj* x_13; obj* x_14; obj* x_24; 
x_13 = lean::box(0);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; 
x_25 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_14 = x_25;
goto block_23;
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
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
lean::free_heap_obj(x_24);
x_14 = x_13;
goto block_23;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_31 = l_Lean_Parser_command_structureCtor_HasView;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::apply_1(x_32, x_30);
lean::cnstr_set(x_24, 0, x_33);
x_14 = x_24;
goto block_23;
}
else
{
obj* x_34; 
lean::dec(x_29);
lean::dec(x_28);
lean::free_heap_obj(x_24);
x_34 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_14 = x_34;
goto block_23;
}
}
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_24, 0);
lean::inc(x_35);
lean::dec(x_24);
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
x_14 = x_13;
goto block_23;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 1);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
lean::dec(x_36);
x_39 = l_Lean_Parser_command_structureCtor_HasView;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::apply_1(x_40, x_38);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
x_14 = x_42;
goto block_23;
}
else
{
obj* x_43; 
lean::dec(x_37);
lean::dec(x_36);
x_43 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_14 = x_43;
goto block_23;
}
}
}
}
block_23:
{
obj* x_15; 
x_15 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_17, 2, x_8);
lean::cnstr_set(x_17, 3, x_11);
lean::cnstr_set(x_17, 4, x_12);
lean::cnstr_set(x_17, 5, x_13);
lean::cnstr_set(x_17, 6, x_14);
lean::cnstr_set(x_17, 7, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_20 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2;
x_21 = l_List_map___main___rarg(x_20, x_19);
x_22 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_22, 0, x_4);
lean::cnstr_set(x_22, 1, x_5);
lean::cnstr_set(x_22, 2, x_8);
lean::cnstr_set(x_22, 3, x_11);
lean::cnstr_set(x_22, 4, x_12);
lean::cnstr_set(x_22, 5, x_13);
lean::cnstr_set(x_22, 6, x_14);
lean::cnstr_set(x_22, 7, x_21);
return x_22;
}
}
}
}
}
}
obj* l_Lean_Parser_command_structure_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_157; 
x_157 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; 
x_158 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6;
return x_158;
}
else
{
obj* x_159; obj* x_160; 
x_159 = lean::cnstr_get(x_157, 0);
lean::inc(x_159);
lean::dec(x_157);
x_160 = lean::cnstr_get(x_159, 1);
lean::inc(x_160);
lean::dec(x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_161; 
x_161 = lean::box(3);
x_2 = x_160;
x_3 = x_161;
goto block_156;
}
else
{
obj* x_162; obj* x_163; 
x_162 = lean::cnstr_get(x_160, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_160, 1);
lean::inc(x_163);
lean::dec(x_160);
x_2 = x_163;
x_3 = x_162;
goto block_156;
}
}
block_156:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_Lean_Parser_command_structureKw_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_153; 
x_153 = lean::box(3);
x_7 = x_2;
x_8 = x_153;
goto block_152;
}
else
{
obj* x_154; obj* x_155; 
x_154 = lean::cnstr_get(x_2, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_2, 1);
lean::inc(x_155);
lean::dec(x_2);
x_7 = x_155;
x_8 = x_154;
goto block_152;
}
block_152:
{
obj* x_9; obj* x_130; 
x_130 = l_Lean_Parser_Syntax_asNode___main(x_8);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; 
x_131 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_9 = x_131;
goto block_129;
}
else
{
uint8 x_132; 
x_132 = !lean::is_exclusive(x_130);
if (x_132 == 0)
{
obj* x_133; obj* x_134; 
x_133 = lean::cnstr_get(x_130, 0);
x_134 = lean::cnstr_get(x_133, 1);
lean::inc(x_134);
lean::dec(x_133);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; 
lean::free_heap_obj(x_130);
x_135 = lean::box(0);
x_9 = x_135;
goto block_129;
}
else
{
obj* x_136; 
x_136 = lean::cnstr_get(x_134, 1);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_137 = lean::cnstr_get(x_134, 0);
lean::inc(x_137);
lean::dec(x_134);
x_138 = l_Lean_Parser_command_oldUnivParams_HasView;
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_140 = lean::apply_1(x_139, x_137);
lean::cnstr_set(x_130, 0, x_140);
x_9 = x_130;
goto block_129;
}
else
{
obj* x_141; 
lean::dec(x_136);
lean::dec(x_134);
lean::free_heap_obj(x_130);
x_141 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_9 = x_141;
goto block_129;
}
}
}
else
{
obj* x_142; obj* x_143; 
x_142 = lean::cnstr_get(x_130, 0);
lean::inc(x_142);
lean::dec(x_130);
x_143 = lean::cnstr_get(x_142, 1);
lean::inc(x_143);
lean::dec(x_142);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; 
x_144 = lean::box(0);
x_9 = x_144;
goto block_129;
}
else
{
obj* x_145; 
x_145 = lean::cnstr_get(x_143, 1);
lean::inc(x_145);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_146 = lean::cnstr_get(x_143, 0);
lean::inc(x_146);
lean::dec(x_143);
x_147 = l_Lean_Parser_command_oldUnivParams_HasView;
x_148 = lean::cnstr_get(x_147, 0);
lean::inc(x_148);
x_149 = lean::apply_1(x_148, x_146);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_9 = x_150;
goto block_129;
}
else
{
obj* x_151; 
lean::dec(x_145);
lean::dec(x_143);
x_151 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_9 = x_151;
goto block_129;
}
}
}
}
block_129:
{
obj* x_10; obj* x_11; 
if (lean::obj_tag(x_7) == 0)
{
obj* x_126; 
x_126 = lean::box(3);
x_10 = x_7;
x_11 = x_126;
goto block_125;
}
else
{
obj* x_127; obj* x_128; 
x_127 = lean::cnstr_get(x_7, 0);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_7, 1);
lean::inc(x_128);
lean::dec(x_7);
x_10 = x_128;
x_11 = x_127;
goto block_125;
}
block_125:
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = l_Lean_Parser_command_identUnivParams_HasView;
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = lean::apply_1(x_13, x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_122; 
x_122 = lean::box(3);
x_15 = x_10;
x_16 = x_122;
goto block_121;
}
else
{
obj* x_123; obj* x_124; 
x_123 = lean::cnstr_get(x_10, 0);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_10, 1);
lean::inc(x_124);
lean::dec(x_10);
x_15 = x_124;
x_16 = x_123;
goto block_121;
}
block_121:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = l_Lean_Parser_command_optDeclSig_HasView;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::apply_1(x_18, x_16);
if (lean::obj_tag(x_15) == 0)
{
obj* x_118; 
x_118 = lean::box(3);
x_20 = x_15;
x_21 = x_118;
goto block_117;
}
else
{
obj* x_119; obj* x_120; 
x_119 = lean::cnstr_get(x_15, 0);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_15, 1);
lean::inc(x_120);
lean::dec(x_15);
x_20 = x_120;
x_21 = x_119;
goto block_117;
}
block_117:
{
obj* x_22; obj* x_95; 
x_95 = l_Lean_Parser_Syntax_asNode___main(x_21);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; 
x_96 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_22 = x_96;
goto block_94;
}
else
{
uint8 x_97; 
x_97 = !lean::is_exclusive(x_95);
if (x_97 == 0)
{
obj* x_98; obj* x_99; 
x_98 = lean::cnstr_get(x_95, 0);
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
lean::dec(x_98);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; 
lean::free_heap_obj(x_95);
x_100 = lean::box(0);
x_22 = x_100;
goto block_94;
}
else
{
obj* x_101; 
x_101 = lean::cnstr_get(x_99, 1);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
lean::dec(x_99);
x_103 = l_Lean_Parser_command_extends_HasView;
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_105 = lean::apply_1(x_104, x_102);
lean::cnstr_set(x_95, 0, x_105);
x_22 = x_95;
goto block_94;
}
else
{
obj* x_106; 
lean::dec(x_101);
lean::dec(x_99);
lean::free_heap_obj(x_95);
x_106 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_22 = x_106;
goto block_94;
}
}
}
else
{
obj* x_107; obj* x_108; 
x_107 = lean::cnstr_get(x_95, 0);
lean::inc(x_107);
lean::dec(x_95);
x_108 = lean::cnstr_get(x_107, 1);
lean::inc(x_108);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; 
x_109 = lean::box(0);
x_22 = x_109;
goto block_94;
}
else
{
obj* x_110; 
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_111 = lean::cnstr_get(x_108, 0);
lean::inc(x_111);
lean::dec(x_108);
x_112 = l_Lean_Parser_command_extends_HasView;
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_114 = lean::apply_1(x_113, x_111);
x_115 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_115, 0, x_114);
x_22 = x_115;
goto block_94;
}
else
{
obj* x_116; 
lean::dec(x_110);
lean::dec(x_108);
x_116 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4;
x_22 = x_116;
goto block_94;
}
}
}
}
block_94:
{
obj* x_23; obj* x_24; 
if (lean::obj_tag(x_20) == 0)
{
obj* x_91; 
x_91 = lean::box(3);
x_23 = x_20;
x_24 = x_91;
goto block_90;
}
else
{
obj* x_92; obj* x_93; 
x_92 = lean::cnstr_get(x_20, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_20, 1);
lean::inc(x_93);
lean::dec(x_20);
x_23 = x_93;
x_24 = x_92;
goto block_90;
}
block_90:
{
obj* x_25; 
if (lean::obj_tag(x_24) == 0)
{
obj* x_87; obj* x_88; 
x_87 = lean::cnstr_get(x_24, 0);
lean::inc(x_87);
lean::dec(x_24);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_25 = x_88;
goto block_86;
}
else
{
obj* x_89; 
lean::dec(x_24);
x_89 = lean::box(0);
x_25 = x_89;
goto block_86;
}
block_86:
{
obj* x_26; obj* x_37; obj* x_38; obj* x_48; obj* x_49; 
if (lean::obj_tag(x_23) == 0)
{
obj* x_83; 
x_83 = lean::box(3);
x_48 = x_23;
x_49 = x_83;
goto block_82;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_23, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_23, 1);
lean::inc(x_85);
lean::dec(x_23);
x_48 = x_85;
x_49 = x_84;
goto block_82;
}
block_36:
{
obj* x_27; obj* x_28; 
x_27 = lean::box(3);
x_28 = l_Lean_Parser_Syntax_asNode___main(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
x_29 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1;
x_30 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_9);
lean::cnstr_set(x_30, 2, x_14);
lean::cnstr_set(x_30, 3, x_19);
lean::cnstr_set(x_30, 4, x_22);
lean::cnstr_set(x_30, 5, x_25);
lean::cnstr_set(x_30, 6, x_26);
lean::cnstr_set(x_30, 7, x_29);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
lean::dec(x_31);
x_33 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2;
x_34 = l_List_map___main___rarg(x_33, x_32);
x_35 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_35, 0, x_6);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_14);
lean::cnstr_set(x_35, 3, x_19);
lean::cnstr_set(x_35, 4, x_22);
lean::cnstr_set(x_35, 5, x_25);
lean::cnstr_set(x_35, 6, x_26);
lean::cnstr_set(x_35, 7, x_34);
return x_35;
}
}
block_47:
{
obj* x_39; 
x_39 = l_Lean_Parser_Syntax_asNode___main(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; 
x_40 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1;
x_41 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_41, 0, x_6);
lean::cnstr_set(x_41, 1, x_9);
lean::cnstr_set(x_41, 2, x_14);
lean::cnstr_set(x_41, 3, x_19);
lean::cnstr_set(x_41, 4, x_22);
lean::cnstr_set(x_41, 5, x_25);
lean::cnstr_set(x_41, 6, x_37);
lean::cnstr_set(x_41, 7, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
lean::dec(x_39);
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_44 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2;
x_45 = l_List_map___main___rarg(x_44, x_43);
x_46 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_46, 0, x_6);
lean::cnstr_set(x_46, 1, x_9);
lean::cnstr_set(x_46, 2, x_14);
lean::cnstr_set(x_46, 3, x_19);
lean::cnstr_set(x_46, 4, x_22);
lean::cnstr_set(x_46, 5, x_25);
lean::cnstr_set(x_46, 6, x_37);
lean::cnstr_set(x_46, 7, x_45);
return x_46;
}
}
block_82:
{
obj* x_50; 
x_50 = l_Lean_Parser_Syntax_asNode___main(x_49);
if (lean::obj_tag(x_50) == 0)
{
if (lean::obj_tag(x_48) == 0)
{
obj* x_51; 
x_51 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_26 = x_51;
goto block_36;
}
else
{
obj* x_52; obj* x_53; 
x_52 = lean::cnstr_get(x_48, 0);
lean::inc(x_52);
lean::dec(x_48);
x_53 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_37 = x_53;
x_38 = x_52;
goto block_47;
}
}
else
{
uint8 x_54; 
x_54 = !lean::is_exclusive(x_50);
if (x_54 == 0)
{
obj* x_55; obj* x_56; 
x_55 = lean::cnstr_get(x_50, 0);
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
lean::free_heap_obj(x_50);
x_57 = lean::box(0);
if (lean::obj_tag(x_48) == 0)
{
x_26 = x_57;
goto block_36;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_48, 0);
lean::inc(x_58);
lean::dec(x_48);
x_37 = x_57;
x_38 = x_58;
goto block_47;
}
}
else
{
obj* x_59; 
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_56, 0);
lean::inc(x_60);
lean::dec(x_56);
x_61 = l_Lean_Parser_command_structureCtor_HasView;
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_63 = lean::apply_1(x_62, x_60);
lean::cnstr_set(x_50, 0, x_63);
if (lean::obj_tag(x_48) == 0)
{
x_26 = x_50;
goto block_36;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_48, 0);
lean::inc(x_64);
lean::dec(x_48);
x_37 = x_50;
x_38 = x_64;
goto block_47;
}
}
else
{
lean::dec(x_59);
lean::dec(x_56);
lean::free_heap_obj(x_50);
if (lean::obj_tag(x_48) == 0)
{
obj* x_65; 
x_65 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_26 = x_65;
goto block_36;
}
else
{
obj* x_66; obj* x_67; 
x_66 = lean::cnstr_get(x_48, 0);
lean::inc(x_66);
lean::dec(x_48);
x_67 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_37 = x_67;
x_38 = x_66;
goto block_47;
}
}
}
}
else
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_50, 0);
lean::inc(x_68);
lean::dec(x_50);
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
x_70 = lean::box(0);
if (lean::obj_tag(x_48) == 0)
{
x_26 = x_70;
goto block_36;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_48, 0);
lean::inc(x_71);
lean::dec(x_48);
x_37 = x_70;
x_38 = x_71;
goto block_47;
}
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
lean::dec(x_69);
x_74 = l_Lean_Parser_command_structureCtor_HasView;
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::apply_1(x_75, x_73);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
if (lean::obj_tag(x_48) == 0)
{
x_26 = x_77;
goto block_36;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_48, 0);
lean::inc(x_78);
lean::dec(x_48);
x_37 = x_77;
x_38 = x_78;
goto block_47;
}
}
else
{
lean::dec(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_48) == 0)
{
obj* x_79; 
x_79 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_26 = x_79;
goto block_36;
}
else
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_48, 0);
lean::inc(x_80);
lean::dec(x_48);
x_81 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3;
x_37 = x_81;
x_38 = x_80;
goto block_47;
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
}
obj* _init_l_Lean_Parser_command_structure_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_structure_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_structure_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_1 = lean::mk_string("structure");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::mk_string("class");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_2);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_7);
lean::dec(x_7);
lean::dec(x_3);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_6);
lean::dec(x_9);
x_11 = l_Lean_Parser_tokens___rarg(x_10);
lean::dec(x_10);
x_12 = l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
x_13 = l_Lean_Parser_tokens___rarg(x_12);
x_14 = lean::mk_string("extends");
x_15 = l_Lean_Parser_symbol_tokens___rarg(x_14, x_2);
lean::dec(x_14);
x_16 = l_Lean_Parser_Term_Parser_Lean_Parser_HasTokens(x_2);
x_17 = l_Lean_Parser_tokens___rarg(x_16);
lean::dec(x_16);
x_18 = lean::mk_string(",");
x_19 = l_Lean_Parser_symbol_tokens___rarg(x_18, x_2);
lean::dec(x_18);
x_20 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_17, x_19);
lean::dec(x_19);
lean::dec(x_17);
x_21 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_6);
lean::dec(x_20);
x_22 = l_Lean_Parser_List_cons_tokens___rarg(x_15, x_21);
lean::dec(x_21);
lean::dec(x_15);
x_23 = l_Lean_Parser_tokens___rarg(x_22);
lean::dec(x_22);
x_24 = l_Lean_Parser_tokens___rarg(x_23);
lean::dec(x_23);
x_25 = lean::mk_string(":=");
x_26 = l_Lean_Parser_symbol_tokens___rarg(x_25, x_2);
lean::dec(x_25);
x_27 = l_Lean_Parser_command_inferModifier_Parser_Lean_Parser_HasTokens;
x_28 = l_Lean_Parser_tokens___rarg(x_27);
x_29 = lean::mk_string("::");
x_30 = l_Lean_Parser_symbol_tokens___rarg(x_29, x_2);
lean::dec(x_29);
x_31 = l_Lean_Parser_List_cons_tokens___rarg(x_30, x_6);
lean::dec(x_30);
x_32 = l_Lean_Parser_List_cons_tokens___rarg(x_28, x_31);
lean::dec(x_31);
lean::dec(x_28);
x_33 = l_Lean_Parser_List_cons_tokens___rarg(x_6, x_32);
lean::dec(x_32);
x_34 = l_Lean_Parser_tokens___rarg(x_33);
lean::dec(x_33);
x_35 = l_Lean_Parser_tokens___rarg(x_34);
lean::dec(x_34);
x_36 = l_Lean_Parser_command_structureFieldBlock_Parser_Lean_Parser_HasTokens;
x_37 = l_Lean_Parser_tokens___rarg(x_36);
x_38 = l_Lean_Parser_List_cons_tokens___rarg(x_37, x_6);
lean::dec(x_37);
x_39 = l_Lean_Parser_List_cons_tokens___rarg(x_35, x_38);
lean::dec(x_38);
lean::dec(x_35);
x_40 = l_Lean_Parser_List_cons_tokens___rarg(x_26, x_39);
lean::dec(x_39);
lean::dec(x_26);
x_41 = l_Lean_Parser_List_cons_tokens___rarg(x_24, x_40);
lean::dec(x_40);
lean::dec(x_24);
x_42 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_43 = l_Lean_Parser_List_cons_tokens___rarg(x_42, x_41);
lean::dec(x_41);
x_44 = l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
x_45 = l_Lean_Parser_List_cons_tokens___rarg(x_44, x_43);
lean::dec(x_43);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_13, x_45);
lean::dec(x_45);
lean::dec(x_13);
x_47 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_46);
lean::dec(x_46);
lean::dec(x_11);
x_48 = l_Lean_Parser_tokens___rarg(x_47);
lean::dec(x_47);
return x_48;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("structure");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::mk_string("class");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_17, 0, x_16);
lean::closure_set(x_17, 1, x_8);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
x_19 = l_Lean_Parser_command_structureKw;
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_20, 0, x_19);
lean::closure_set(x_20, 1, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_22 = 0;
x_23 = lean::box(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_24, 0, x_21);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::mk_string("extends");
x_26 = l_String_trim(x_25);
lean::dec(x_25);
lean::inc(x_26);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_27, 0, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_28, 0, x_26);
lean::closure_set(x_28, 1, x_8);
lean::closure_set(x_28, 2, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_29, 0, x_8);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::mk_string(",");
x_32 = l_String_trim(x_31);
lean::dec(x_31);
lean::inc(x_32);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_33, 0, x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_8);
lean::closure_set(x_34, 2, x_33);
x_35 = 1;
x_36 = lean::box(x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_37, 0, x_30);
lean::closure_set(x_37, 1, x_34);
lean::closure_set(x_37, 2, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_14);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_28);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_command_extends;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_41, 0, x_40);
lean::closure_set(x_41, 1, x_39);
x_42 = lean::box(x_22);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_42);
x_44 = lean::mk_string(":=");
x_45 = l_String_trim(x_44);
lean::dec(x_44);
lean::inc(x_45);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_46, 0, x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_47, 0, x_45);
lean::closure_set(x_47, 1, x_8);
lean::closure_set(x_47, 2, x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_49 = lean::box(x_22);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_50, 0, x_48);
lean::closure_set(x_50, 1, x_49);
x_51 = lean::mk_string("::");
x_52 = l_String_trim(x_51);
lean::dec(x_51);
lean::inc(x_52);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_53, 0, x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_54, 0, x_52);
lean::closure_set(x_54, 1, x_8);
lean::closure_set(x_54, 2, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_14);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
x_59 = l_Lean_Parser_command_structureCtor;
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_60, 0, x_59);
lean::closure_set(x_60, 1, x_58);
x_61 = lean::box(x_22);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_62, 0, x_60);
lean::closure_set(x_62, 1, x_61);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_Parser), 4, 0);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_14);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_47);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_43);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_24);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_20);
lean::cnstr_set(x_74, 1, x_73);
x_75 = l_Lean_Parser_command_structure;
x_76 = l_Lean_Parser_command_structure_HasView;
x_77 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_75, x_74, x_76);
lean::dec(x_74);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_77;
}
}
obj* _init_l_Lean_Parser_command_structure_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_1 = lean::mk_string("structure");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("class");
x_7 = l_String_trim(x_6);
lean::dec(x_6);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_4);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_13, 0, x_12);
lean::closure_set(x_13, 1, x_4);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
x_15 = l_Lean_Parser_command_structureKw;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_15);
lean::closure_set(x_16, 1, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_19);
x_21 = lean::mk_string("extends");
x_22 = l_String_trim(x_21);
lean::dec(x_21);
lean::inc(x_22);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_24, 0, x_22);
lean::closure_set(x_24, 1, x_4);
lean::closure_set(x_24, 2, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Term_Parser), 6, 1);
lean::closure_set(x_25, 0, x_4);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_26, 0, x_25);
x_27 = lean::mk_string(",");
x_28 = l_String_trim(x_27);
lean::dec(x_27);
lean::inc(x_28);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_29, 0, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_4);
lean::closure_set(x_30, 2, x_29);
x_31 = 1;
x_32 = lean::box(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___at_Lean_Parser_command_declAttributes_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_33, 0, x_26);
lean::closure_set(x_33, 1, x_30);
lean::closure_set(x_33, 2, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_10);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_24);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_Lean_Parser_command_extends;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_35);
x_38 = lean::box(x_18);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::mk_string(":=");
x_41 = l_String_trim(x_40);
lean::dec(x_40);
lean::inc(x_41);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_42, 0, x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_4);
lean::closure_set(x_43, 2, x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inferModifier_Parser), 4, 0);
x_45 = lean::box(x_18);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_46, 0, x_44);
lean::closure_set(x_46, 1, x_45);
x_47 = lean::mk_string("::");
x_48 = l_String_trim(x_47);
lean::dec(x_47);
lean::inc(x_48);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_49, 0, x_48);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_50, 0, x_48);
lean::closure_set(x_50, 1, x_4);
lean::closure_set(x_50, 2, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_10);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_46);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___at_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens___spec__1___boxed), 4, 0);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_Lean_Parser_command_structureCtor;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_56, 0, x_55);
lean::closure_set(x_56, 1, x_54);
x_57 = lean::box(x_18);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_58, 0, x_56);
lean::closure_set(x_58, 1, x_57);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structureFieldBlock_Parser), 4, 0);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_10);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_58);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_43);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_39);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_20);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_16);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
}
obj* l_Lean_Parser_command_structure_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_structure;
x_6 = l_Lean_Parser_command_structure_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("defLike");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("kind");
x_11 = lean_name_mk_string(x_9, x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_defLike_kind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_defLike_kind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(2u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_defLike_kind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(3u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_defLike_kind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(4u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_defLike_kind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_defLike_kind;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
case 1:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_defLike_kind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
case 2:
{
obj* x_23; 
x_23 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
x_24 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3;
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
x_28 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_2);
x_31 = l_Lean_Parser_command_defLike_kind;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
case 3:
{
obj* x_33; 
x_33 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_2);
x_38 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
x_41 = l_Lean_Parser_command_defLike_kind;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
default: 
{
obj* x_43; 
x_43 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; 
x_44 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5;
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_2);
x_48 = l_Lean_Parser_command_mixfix_kind_HasView_x27___elambda__1___closed__6;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_2);
x_51 = l_Lean_Parser_command_defLike_kind;
x_52 = l_Lean_Parser_Syntax_mkNode(x_51, x_50);
return x_52;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("defLike");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("kind");
x_11 = lean_name_mk_string(x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
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
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_dec_eq(x_22, x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = lean::mk_nat_obj(2u);
x_34 = lean::nat_dec_eq(x_22, x_33);
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
x_35 = lean::mk_nat_obj(3u);
x_36 = lean::nat_dec_eq(x_22, x_35);
lean::dec(x_22);
if (x_36 == 0)
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_28, 0);
lean::inc(x_37);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_37);
x_38 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_38, 0, x_13);
return x_38;
}
else
{
obj* x_39; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_39 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1;
return x_39;
}
}
else
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_28, 0);
lean::inc(x_40);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_40);
x_41 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_41, 0, x_13);
return x_41;
}
else
{
obj* x_42; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_42 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2;
return x_42;
}
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_28, 0);
lean::inc(x_43);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_43);
x_44 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_44, 0, x_13);
return x_44;
}
else
{
obj* x_45; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_45 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3;
return x_45;
}
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_28, 0);
lean::inc(x_46);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_46);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_13);
return x_47;
}
else
{
obj* x_48; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_48 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4;
return x_48;
}
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_28, 0);
lean::inc(x_49);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_49);
x_50 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_50, 0, x_13);
return x_50;
}
else
{
obj* x_51; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_51 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5;
return x_51;
}
}
}
else
{
obj* x_52; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_52 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_52;
}
}
}
}
}
}
else
{
obj* x_53; obj* x_54; 
x_53 = lean::cnstr_get(x_13, 0);
lean::inc(x_53);
lean::dec(x_13);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
switch (lean::obj_tag(x_54)) {
case 0:
{
obj* x_55; 
lean::dec(x_53);
x_55 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_55;
}
case 1:
{
obj* x_56; 
lean::dec(x_54);
lean::dec(x_53);
x_56 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_56;
}
default: 
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; uint8 x_61; 
x_57 = lean::cnstr_get(x_53, 1);
lean::inc(x_57);
lean::dec(x_53);
x_58 = lean::cnstr_get(x_54, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_54, 1);
lean::inc(x_59);
lean::dec(x_54);
x_60 = lean::box(0);
x_61 = lean_name_dec_eq(x_58, x_60);
lean::dec(x_58);
if (x_61 == 0)
{
obj* x_62; 
lean::dec(x_59);
lean::dec(x_57);
x_62 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_62;
}
else
{
if (lean::obj_tag(x_57) == 0)
{
obj* x_63; 
lean::dec(x_59);
x_63 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_63;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_57, 1);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; uint8 x_67; 
x_65 = lean::cnstr_get(x_57, 0);
lean::inc(x_65);
lean::dec(x_57);
x_66 = lean::mk_nat_obj(0u);
x_67 = lean::nat_dec_eq(x_59, x_66);
if (x_67 == 0)
{
obj* x_68; uint8 x_69; 
x_68 = lean::mk_nat_obj(1u);
x_69 = lean::nat_dec_eq(x_59, x_68);
if (x_69 == 0)
{
obj* x_70; uint8 x_71; 
x_70 = lean::mk_nat_obj(2u);
x_71 = lean::nat_dec_eq(x_59, x_70);
if (x_71 == 0)
{
obj* x_72; uint8 x_73; 
x_72 = lean::mk_nat_obj(3u);
x_73 = lean::nat_dec_eq(x_59, x_72);
lean::dec(x_59);
if (x_73 == 0)
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_65, 0);
lean::inc(x_74);
lean::dec(x_65);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
else
{
obj* x_77; 
lean::dec(x_65);
x_77 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1;
return x_77;
}
}
else
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_65, 0);
lean::inc(x_78);
lean::dec(x_65);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
else
{
obj* x_81; 
lean::dec(x_65);
x_81 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2;
return x_81;
}
}
}
else
{
lean::dec(x_59);
if (lean::obj_tag(x_65) == 0)
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_65, 0);
lean::inc(x_82);
lean::dec(x_65);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_84 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
else
{
obj* x_85; 
lean::dec(x_65);
x_85 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3;
return x_85;
}
}
}
else
{
lean::dec(x_59);
if (lean::obj_tag(x_65) == 0)
{
obj* x_86; obj* x_87; obj* x_88; 
x_86 = lean::cnstr_get(x_65, 0);
lean::inc(x_86);
lean::dec(x_65);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
else
{
obj* x_89; 
lean::dec(x_65);
x_89 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4;
return x_89;
}
}
}
else
{
lean::dec(x_59);
if (lean::obj_tag(x_65) == 0)
{
obj* x_90; obj* x_91; obj* x_92; 
x_90 = lean::cnstr_get(x_65, 0);
lean::inc(x_90);
lean::dec(x_65);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
return x_92;
}
else
{
obj* x_93; 
lean::dec(x_65);
x_93 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5;
return x_93;
}
}
}
else
{
obj* x_94; 
lean::dec(x_64);
lean::dec(x_59);
lean::dec(x_57);
x_94 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_94;
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
obj* x_95; 
lean::dec(x_11);
lean::dec(x_6);
x_95 = l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6;
return x_95;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_defLike_kind_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_defLike_kind_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_defLike() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("defLike");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_defLike_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
lean::dec(x_1);
x_7 = l_Lean_Parser_command_defLike_kind_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::apply_1(x_8, x_2);
x_10 = l_Lean_Parser_command_identUnivParams_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_4);
x_13 = l_Lean_Parser_command_optDeclSig_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_5);
x_16 = l_Lean_Parser_command_declVal_HasView;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_6);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_15);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
if (lean::obj_tag(x_3) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_command_defLike;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_29 = l_Lean_Parser_command_oldUnivParams_HasView;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
x_31 = lean::apply_1(x_30, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_19);
x_33 = l_Lean_Parser_noKind;
x_34 = l_Lean_Parser_Syntax_mkNode(x_33, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_22);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_9);
lean::cnstr_set(x_36, 1, x_35);
x_37 = l_Lean_Parser_command_defLike;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
return x_38;
}
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_identUnivParams_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_declVal_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_defLike_kind_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_7 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_8 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_9 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_10, 2, x_7);
lean::cnstr_set(x_10, 3, x_8);
lean::cnstr_set(x_10, 4, x_9);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_5);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_5, 0);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::free_heap_obj(x_5);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_16 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_17 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_16);
lean::cnstr_set(x_18, 4, x_17);
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_21 = l_Lean_Parser_command_oldUnivParams_HasView;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::apply_1(x_22, x_20);
lean::cnstr_set(x_5, 0, x_23);
x_24 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_25 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_26 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_5);
lean::cnstr_set(x_27, 2, x_24);
lean::cnstr_set(x_27, 3, x_25);
lean::cnstr_set(x_27, 4, x_26);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_19);
lean::dec(x_13);
lean::free_heap_obj(x_5);
x_28 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_29 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_30 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_31 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_32 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_32, 0, x_4);
lean::cnstr_set(x_32, 1, x_28);
lean::cnstr_set(x_32, 2, x_29);
lean::cnstr_set(x_32, 3, x_30);
lean::cnstr_set(x_32, 4, x_31);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_5, 0);
lean::inc(x_33);
lean::dec(x_5);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = lean::box(0);
x_36 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_37 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_38 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_39 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_39, 0, x_4);
lean::cnstr_set(x_39, 1, x_35);
lean::cnstr_set(x_39, 2, x_36);
lean::cnstr_set(x_39, 3, x_37);
lean::cnstr_set(x_39, 4, x_38);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_34, 1);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
x_42 = l_Lean_Parser_command_oldUnivParams_HasView;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::apply_1(x_43, x_41);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_47 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_48 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_49 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_45);
lean::cnstr_set(x_49, 2, x_46);
lean::cnstr_set(x_49, 3, x_47);
lean::cnstr_set(x_49, 4, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_40);
lean::dec(x_34);
x_50 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_51 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_52 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_53 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_54 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_54, 0, x_4);
lean::cnstr_set(x_54, 1, x_50);
lean::cnstr_set(x_54, 2, x_51);
lean::cnstr_set(x_54, 3, x_52);
lean::cnstr_set(x_54, 4, x_53);
return x_54;
}
}
}
}
}
}
obj* l_Lean_Parser_command_defLike_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_103; 
x_103 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; 
x_104 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3;
return x_104;
}
else
{
obj* x_105; obj* x_106; 
x_105 = lean::cnstr_get(x_103, 0);
lean::inc(x_105);
lean::dec(x_103);
x_106 = lean::cnstr_get(x_105, 1);
lean::inc(x_106);
lean::dec(x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_107; 
x_107 = lean::box(3);
x_2 = x_106;
x_3 = x_107;
goto block_102;
}
else
{
obj* x_108; obj* x_109; 
x_108 = lean::cnstr_get(x_106, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
x_2 = x_109;
x_3 = x_108;
goto block_102;
}
}
block_102:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_29; obj* x_30; 
x_4 = l_Lean_Parser_command_defLike_kind_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_99; 
x_99 = lean::box(3);
x_29 = x_2;
x_30 = x_99;
goto block_98;
}
else
{
obj* x_100; obj* x_101; 
x_100 = lean::cnstr_get(x_2, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_2, 1);
lean::inc(x_101);
lean::dec(x_2);
x_29 = x_101;
x_30 = x_100;
goto block_98;
}
block_28:
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = l_Lean_Parser_command_identUnivParams_HasView;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_14 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_12);
lean::cnstr_set(x_15, 3, x_13);
lean::cnstr_set(x_15, 4, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_9, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_9, 1);
lean::inc(x_17);
lean::dec(x_9);
x_18 = l_Lean_Parser_command_optDeclSig_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::apply_1(x_19, x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; 
x_21 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_6);
lean::cnstr_set(x_22, 1, x_7);
lean::cnstr_set(x_22, 2, x_12);
lean::cnstr_set(x_22, 3, x_20);
lean::cnstr_set(x_22, 4, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_17, 0);
lean::inc(x_23);
lean::dec(x_17);
x_24 = l_Lean_Parser_command_declVal_HasView;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::apply_1(x_25, x_23);
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_7);
lean::cnstr_set(x_27, 2, x_12);
lean::cnstr_set(x_27, 3, x_20);
lean::cnstr_set(x_27, 4, x_26);
return x_27;
}
}
}
block_98:
{
obj* x_31; 
x_31 = l_Lean_Parser_Syntax_asNode___main(x_30);
if (lean::obj_tag(x_31) == 0)
{
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_33 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_34 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_35 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_32);
lean::cnstr_set(x_36, 2, x_33);
lean::cnstr_set(x_36, 3, x_34);
lean::cnstr_set(x_36, 4, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_29, 1);
lean::inc(x_38);
lean::dec(x_29);
x_39 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_7 = x_39;
x_8 = x_37;
x_9 = x_38;
goto block_28;
}
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_31);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_31, 0);
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; 
lean::free_heap_obj(x_31);
x_43 = lean::box(0);
if (lean::obj_tag(x_29) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_45 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_46 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_47 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_47, 0, x_6);
lean::cnstr_set(x_47, 1, x_43);
lean::cnstr_set(x_47, 2, x_44);
lean::cnstr_set(x_47, 3, x_45);
lean::cnstr_set(x_47, 4, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_29, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_29, 1);
lean::inc(x_49);
lean::dec(x_29);
x_7 = x_43;
x_8 = x_48;
x_9 = x_49;
goto block_28;
}
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_52 = l_Lean_Parser_command_oldUnivParams_HasView;
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::apply_1(x_53, x_51);
lean::cnstr_set(x_31, 0, x_54);
if (lean::obj_tag(x_29) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_55 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_56 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_57 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_58 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_58, 0, x_6);
lean::cnstr_set(x_58, 1, x_31);
lean::cnstr_set(x_58, 2, x_55);
lean::cnstr_set(x_58, 3, x_56);
lean::cnstr_set(x_58, 4, x_57);
return x_58;
}
else
{
obj* x_59; obj* x_60; 
x_59 = lean::cnstr_get(x_29, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_29, 1);
lean::inc(x_60);
lean::dec(x_29);
x_7 = x_31;
x_8 = x_59;
x_9 = x_60;
goto block_28;
}
}
else
{
lean::dec(x_50);
lean::dec(x_42);
lean::free_heap_obj(x_31);
if (lean::obj_tag(x_29) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_61 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_62 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_63 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_64 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_65 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_65, 0, x_6);
lean::cnstr_set(x_65, 1, x_61);
lean::cnstr_set(x_65, 2, x_62);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set(x_65, 4, x_64);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; 
x_66 = lean::cnstr_get(x_29, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_29, 1);
lean::inc(x_67);
lean::dec(x_29);
x_68 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_7 = x_68;
x_8 = x_66;
x_9 = x_67;
goto block_28;
}
}
}
}
else
{
obj* x_69; obj* x_70; 
x_69 = lean::cnstr_get(x_31, 0);
lean::inc(x_69);
lean::dec(x_31);
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; 
x_71 = lean::box(0);
if (lean::obj_tag(x_29) == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_72 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_73 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_74 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_75 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_75, 0, x_6);
lean::cnstr_set(x_75, 1, x_71);
lean::cnstr_set(x_75, 2, x_72);
lean::cnstr_set(x_75, 3, x_73);
lean::cnstr_set(x_75, 4, x_74);
return x_75;
}
else
{
obj* x_76; obj* x_77; 
x_76 = lean::cnstr_get(x_29, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_29, 1);
lean::inc(x_77);
lean::dec(x_29);
x_7 = x_71;
x_8 = x_76;
x_9 = x_77;
goto block_28;
}
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_70, 1);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = lean::cnstr_get(x_70, 0);
lean::inc(x_79);
lean::dec(x_70);
x_80 = l_Lean_Parser_command_oldUnivParams_HasView;
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_82 = lean::apply_1(x_81, x_79);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
if (lean::obj_tag(x_29) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_84 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_85 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_86 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_87 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_87, 0, x_6);
lean::cnstr_set(x_87, 1, x_83);
lean::cnstr_set(x_87, 2, x_84);
lean::cnstr_set(x_87, 3, x_85);
lean::cnstr_set(x_87, 4, x_86);
return x_87;
}
else
{
obj* x_88; obj* x_89; 
x_88 = lean::cnstr_get(x_29, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_29, 1);
lean::inc(x_89);
lean::dec(x_29);
x_7 = x_83;
x_8 = x_88;
x_9 = x_89;
goto block_28;
}
}
else
{
lean::dec(x_78);
lean::dec(x_70);
if (lean::obj_tag(x_29) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_90 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_91 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_92 = l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2;
x_93 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_94 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_94, 0, x_6);
lean::cnstr_set(x_94, 1, x_90);
lean::cnstr_set(x_94, 2, x_91);
lean::cnstr_set(x_94, 3, x_92);
lean::cnstr_set(x_94, 4, x_93);
return x_94;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
x_95 = lean::cnstr_get(x_29, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_29, 1);
lean::inc(x_96);
lean::dec(x_29);
x_97 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_7 = x_97;
x_8 = x_95;
x_9 = x_96;
goto block_28;
}
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_defLike_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_defLike_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_defLike_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_instance() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("instance");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_instance_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_Parser_command_declSig_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_8 = lean::apply_1(x_7, x_4);
x_9 = l_Lean_Parser_command_declVal_HasView;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_5);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_13);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::box(3);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_command_instance;
x_20 = l_Lean_Parser_Syntax_mkNode(x_19, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_21 = lean::cnstr_get(x_3, 0);
lean::inc(x_21);
lean::dec(x_3);
x_22 = l_Lean_Parser_command_identUnivParams_HasView;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_24 = lean::apply_1(x_23, x_21);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_12);
x_26 = l_Lean_Parser_noKind;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_25);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_14);
x_29 = lean::box(3);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = l_Lean_Parser_command_instance;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_2, 0);
lean::inc(x_33);
lean::dec(x_2);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
if (lean::obj_tag(x_3) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_14);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_command_instance;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_3, 0);
lean::inc(x_40);
lean::dec(x_3);
x_41 = l_Lean_Parser_command_identUnivParams_HasView;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
x_43 = lean::apply_1(x_42, x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_12);
x_45 = l_Lean_Parser_noKind;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_14);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_34);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_Lean_Parser_command_instance;
x_50 = l_Lean_Parser_Syntax_mkNode(x_49, x_48);
return x_50;
}
}
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_identUnivParams_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_declSig_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_5 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_6 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
lean::free_heap_obj(x_3);
x_11 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_12 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_12);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_16 = l_Lean_Parser_command_identUnivParams_HasView;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::apply_1(x_17, x_15);
lean::cnstr_set(x_3, 0, x_18);
x_19 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_20 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_19);
lean::cnstr_set(x_21, 3, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::dec(x_10);
lean::free_heap_obj(x_3);
x_22 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_23 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_24 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_1);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_3, 0);
lean::inc(x_26);
lean::dec(x_3);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_29 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_1);
lean::cnstr_set(x_30, 2, x_28);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_27, 0);
lean::inc(x_32);
lean::dec(x_27);
x_33 = l_Lean_Parser_command_identUnivParams_HasView;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::apply_1(x_34, x_32);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_38 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_1);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
lean::cnstr_set(x_39, 3, x_38);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_31);
lean::dec(x_27);
x_40 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_41 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_42 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_43 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_43, 0, x_1);
lean::cnstr_set(x_43, 1, x_40);
lean::cnstr_set(x_43, 2, x_41);
lean::cnstr_set(x_43, 3, x_42);
return x_43;
}
}
}
}
}
}
obj* l_Lean_Parser_command_instance_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_90; 
x_90 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; 
x_91 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3;
return x_91;
}
else
{
obj* x_92; obj* x_93; 
x_92 = lean::cnstr_get(x_90, 0);
lean::inc(x_92);
lean::dec(x_90);
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
lean::dec(x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; 
x_94 = lean::box(3);
x_2 = x_93;
x_3 = x_94;
goto block_89;
}
else
{
obj* x_95; obj* x_96; 
x_95 = lean::cnstr_get(x_93, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
x_2 = x_96;
x_3 = x_95;
goto block_89;
}
}
block_89:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_3, 0);
lean::inc(x_86);
lean::dec(x_3);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_4 = x_87;
goto block_85;
}
else
{
obj* x_88; 
lean::dec(x_3);
x_88 = lean::box(0);
x_4 = x_88;
goto block_85;
}
block_85:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_19; obj* x_20; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_82; 
x_82 = lean::box(3);
x_19 = x_2;
x_20 = x_82;
goto block_81;
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_2, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_2, 1);
lean::inc(x_84);
lean::dec(x_2);
x_19 = x_84;
x_20 = x_83;
goto block_81;
}
block_18:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = l_Lean_Parser_command_declSig_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::apply_1(x_9, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_12; 
x_11 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_5);
lean::cnstr_set(x_12, 2, x_10);
lean::cnstr_set(x_12, 3, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_14 = l_Lean_Parser_command_declVal_HasView;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_5);
lean::cnstr_set(x_17, 2, x_10);
lean::cnstr_set(x_17, 3, x_16);
return x_17;
}
}
block_81:
{
obj* x_21; 
x_21 = l_Lean_Parser_Syntax_asNode___main(x_20);
if (lean::obj_tag(x_21) == 0)
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_23 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_24 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_19, 1);
lean::inc(x_27);
lean::dec(x_19);
x_28 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_5 = x_28;
x_6 = x_26;
x_7 = x_27;
goto block_18;
}
}
else
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_21);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_21, 0);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
lean::free_heap_obj(x_21);
x_32 = lean::box(0);
if (lean::obj_tag(x_19) == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_34 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_35 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_35, 0, x_4);
lean::cnstr_set(x_35, 1, x_32);
lean::cnstr_set(x_35, 2, x_33);
lean::cnstr_set(x_35, 3, x_34);
return x_35;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_19, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_19, 1);
lean::inc(x_37);
lean::dec(x_19);
x_5 = x_32;
x_6 = x_36;
x_7 = x_37;
goto block_18;
}
}
else
{
obj* x_38; 
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_31, 0);
lean::inc(x_39);
lean::dec(x_31);
x_40 = l_Lean_Parser_command_identUnivParams_HasView;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::apply_1(x_41, x_39);
lean::cnstr_set(x_21, 0, x_42);
if (lean::obj_tag(x_19) == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_44 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_4);
lean::cnstr_set(x_45, 1, x_21);
lean::cnstr_set(x_45, 2, x_43);
lean::cnstr_set(x_45, 3, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_19, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_19, 1);
lean::inc(x_47);
lean::dec(x_19);
x_5 = x_21;
x_6 = x_46;
x_7 = x_47;
goto block_18;
}
}
else
{
lean::dec(x_38);
lean::dec(x_31);
lean::free_heap_obj(x_21);
if (lean::obj_tag(x_19) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_48 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_49 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_50 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_4);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set(x_51, 2, x_49);
lean::cnstr_set(x_51, 3, x_50);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; 
x_52 = lean::cnstr_get(x_19, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_19, 1);
lean::inc(x_53);
lean::dec(x_19);
x_54 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_5 = x_54;
x_6 = x_52;
x_7 = x_53;
goto block_18;
}
}
}
}
else
{
obj* x_55; obj* x_56; 
x_55 = lean::cnstr_get(x_21, 0);
lean::inc(x_55);
lean::dec(x_21);
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; 
x_57 = lean::box(0);
if (lean::obj_tag(x_19) == 0)
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_59 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_4);
lean::cnstr_set(x_60, 1, x_57);
lean::cnstr_set(x_60, 2, x_58);
lean::cnstr_set(x_60, 3, x_59);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_19, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_19, 1);
lean::inc(x_62);
lean::dec(x_19);
x_5 = x_57;
x_6 = x_61;
x_7 = x_62;
goto block_18;
}
}
else
{
obj* x_63; 
x_63 = lean::cnstr_get(x_56, 1);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_64 = lean::cnstr_get(x_56, 0);
lean::inc(x_64);
lean::dec(x_56);
x_65 = l_Lean_Parser_command_identUnivParams_HasView;
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_67 = lean::apply_1(x_66, x_64);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
if (lean::obj_tag(x_19) == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_70 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_4);
lean::cnstr_set(x_71, 1, x_68);
lean::cnstr_set(x_71, 2, x_69);
lean::cnstr_set(x_71, 3, x_70);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = lean::cnstr_get(x_19, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_19, 1);
lean::inc(x_73);
lean::dec(x_19);
x_5 = x_68;
x_6 = x_72;
x_7 = x_73;
goto block_18;
}
}
else
{
lean::dec(x_63);
lean::dec(x_56);
if (lean::obj_tag(x_19) == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_74 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_75 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_76 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_4);
lean::cnstr_set(x_77, 1, x_74);
lean::cnstr_set(x_77, 2, x_75);
lean::cnstr_set(x_77, 3, x_76);
return x_77;
}
else
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_19, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_19, 1);
lean::inc(x_79);
lean::dec(x_19);
x_80 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1;
x_5 = x_80;
x_6 = x_78;
x_7 = x_79;
goto block_18;
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
obj* _init_l_Lean_Parser_command_instance_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instance_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_instance_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_instance_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_instance_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_example() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("example");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_example_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_declSig_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = l_Lean_Parser_command_declVal_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::apply_1(x_9, x_4);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::box(3);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_Lean_Parser_command_example;
x_17 = l_Lean_Parser_Syntax_mkNode(x_16, x_15);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
x_21 = l_Lean_Parser_command_example;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_command_declSig_HasView;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_3, x_4);
x_6 = l_Lean_Parser_command_declVal_HasView;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::apply_1(x_7, x_4);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_command_example_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_16; obj* x_17; obj* x_30; 
x_30 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; 
x_31 = l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2;
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::dec(x_30);
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = lean::box(3);
x_16 = x_33;
x_17 = x_34;
goto block_29;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_16 = x_36;
x_17 = x_35;
goto block_29;
}
}
block_15:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declSig_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_11 = l_Lean_Parser_command_declVal_HasView;
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::apply_1(x_12, x_10);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
}
block_29:
{
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
lean::dec(x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_21 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2;
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_16, 1);
lean::inc(x_24);
lean::dec(x_16);
x_2 = x_19;
x_3 = x_23;
x_4 = x_24;
goto block_15;
}
}
else
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_25; 
x_25 = l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_16, 1);
lean::inc(x_27);
lean::dec(x_16);
x_28 = lean::box(0);
x_2 = x_28;
x_3 = x_26;
x_4 = x_27;
goto block_15;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_example_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_example_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_example_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_example_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_example_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("constantKeyword");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_command_constantKeyword;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
x_10 = l_Lean_Parser_command_constantKeyword;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("constantKeyword");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
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
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
lean::dec(x_17);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_21, x_22);
lean::dec(x_21);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_24 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; 
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_20, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 0);
lean::inc(x_27);
lean::dec(x_20);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
lean::dec(x_27);
lean::cnstr_set(x_13, 0, x_28);
return x_13;
}
else
{
obj* x_29; 
lean::dec(x_27);
lean::free_heap_obj(x_13);
x_29 = lean::box(0);
return x_29;
}
}
else
{
obj* x_30; 
lean::dec(x_26);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_30 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_30;
}
}
}
}
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_13, 0);
lean::inc(x_31);
lean::dec(x_13);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
switch (lean::obj_tag(x_32)) {
case 0:
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_33;
}
case 1:
{
obj* x_34; 
lean::dec(x_32);
lean::dec(x_31);
x_34 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_34;
}
default: 
{
obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_35 = lean::cnstr_get(x_31, 1);
lean::inc(x_35);
lean::dec(x_31);
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
x_37 = lean::box(0);
x_38 = lean_name_dec_eq(x_36, x_37);
lean::dec(x_36);
if (x_38 == 0)
{
obj* x_39; 
lean::dec(x_35);
x_39 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_39;
}
else
{
if (lean::obj_tag(x_35) == 0)
{
obj* x_40; 
x_40 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_40;
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_35, 1);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; 
x_42 = lean::cnstr_get(x_35, 0);
lean::inc(x_42);
lean::dec(x_35);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
lean::dec(x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
else
{
obj* x_45; 
lean::dec(x_42);
x_45 = lean::box(0);
return x_45;
}
}
else
{
obj* x_46; 
lean::dec(x_41);
lean::dec(x_35);
x_46 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_46;
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
obj* x_47; 
lean::dec(x_11);
lean::dec(x_6);
x_47 = l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1;
return x_47;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_constantKeyword_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_constantKeyword_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_axiom() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("axiom");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_axiom_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Parser_command_constantKeyword_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_2);
x_8 = l_Lean_Parser_command_identUnivParams_HasView;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_10 = lean::apply_1(x_9, x_3);
x_11 = l_Lean_Parser_command_declSig_HasView;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_13 = lean::apply_1(x_12, x_4);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_command_axiom;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = l_Lean_Parser_command_constantKeyword_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_command_identUnivParams_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = l_Lean_Parser_command_declSig_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::apply_1(x_9, x_3);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
obj* l_Lean_Parser_command_axiom_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_Lean_Parser_command_constantKeyword_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1;
x_13 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
lean::dec(x_8);
x_17 = l_Lean_Parser_command_identUnivParams_HasView;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::apply_1(x_18, x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_21; 
x_20 = l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set(x_21, 2, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_16, 0);
lean::inc(x_22);
lean::dec(x_16);
x_23 = l_Lean_Parser_command_declSig_HasView;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = lean::apply_1(x_24, x_22);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_19);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_axiom_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_axiom_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_axiom_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_axiom_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_inductive() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("inductive");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_introRule_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_command_inductive_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 4);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 5);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_1, 6);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::box(0);
x_10 = l_Lean_Parser_command_identUnivParams_HasView;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::apply_1(x_11, x_5);
x_13 = l_Lean_Parser_command_optDeclSig_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_6);
x_16 = l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1;
x_17 = l_List_map___main___rarg(x_16, x_8);
x_18 = l_Lean_Parser_noKind;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_9);
if (lean::obj_tag(x_2) == 0)
{
obj* x_80; 
x_80 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_21 = x_80;
goto block_79;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_2, 0);
lean::inc(x_81);
lean::dec(x_2);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; 
x_82 = l_Lean_Parser_command_notation_HasView_x27___elambda__1___closed__1;
x_21 = x_82;
goto block_79;
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_83 = lean::cnstr_get(x_81, 0);
lean::inc(x_83);
lean::dec(x_81);
x_84 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_9);
x_86 = l_Lean_Parser_Syntax_mkNode(x_18, x_85);
x_21 = x_86;
goto block_79;
}
}
block_79:
{
obj* x_22; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_76; 
x_76 = lean::box(3);
x_22 = x_76;
goto block_75;
}
else
{
obj* x_77; obj* x_78; 
x_77 = lean::cnstr_get(x_3, 0);
lean::inc(x_77);
lean::dec(x_3);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
x_22 = x_78;
goto block_75;
}
block_75:
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_Syntax_mkNode(x_18, x_24);
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_20);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_12);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_25);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_command_inductive;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_34 = lean::cnstr_get(x_7, 0);
lean::inc(x_34);
lean::dec(x_7);
x_35 = l_Lean_Parser_command_notationLike_HasView;
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
x_37 = lean::apply_1(x_36, x_34);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_9);
x_39 = l_Lean_Parser_Syntax_mkNode(x_18, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_20);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_15);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_12);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_command_inductive;
x_47 = l_Lean_Parser_Syntax_mkNode(x_46, x_45);
return x_47;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_4, 0);
lean::inc(x_48);
lean::dec(x_4);
x_49 = l_Lean_Parser_command_oldUnivParams_HasView;
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
x_51 = lean::apply_1(x_50, x_48);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_9);
x_53 = l_Lean_Parser_Syntax_mkNode(x_18, x_52);
if (lean::obj_tag(x_7) == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_20);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_15);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_12);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_25);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_Lean_Parser_command_inductive;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_62 = lean::cnstr_get(x_7, 0);
lean::inc(x_62);
lean::dec(x_7);
x_63 = l_Lean_Parser_command_notationLike_HasView;
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_65 = lean::apply_1(x_64, x_62);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_9);
x_67 = l_Lean_Parser_Syntax_mkNode(x_18, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_20);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_15);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_12);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_53);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_25);
lean::cnstr_set(x_72, 1, x_71);
x_73 = l_Lean_Parser_command_inductive;
x_74 = l_Lean_Parser_Syntax_mkNode(x_73, x_72);
return x_74;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_Parser_command_introRule_HasView;
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
obj* _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_command_introRule_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_notationLike_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_64; obj* x_65; 
x_64 = lean::box(3);
x_65 = l_Lean_Parser_Syntax_asNode___main(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; 
x_66 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_1 = x_66;
goto block_63;
}
else
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_65);
if (x_67 == 0)
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_65, 0);
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
lean::free_heap_obj(x_65);
x_70 = lean::box(0);
x_1 = x_70;
goto block_63;
}
else
{
obj* x_71; 
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; 
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; 
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
lean::dec(x_72);
lean::cnstr_set(x_65, 0, x_73);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_65);
x_1 = x_74;
goto block_63;
}
else
{
obj* x_75; 
lean::dec(x_72);
lean::free_heap_obj(x_65);
x_75 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_1 = x_75;
goto block_63;
}
}
else
{
obj* x_76; 
lean::dec(x_71);
lean::dec(x_69);
lean::free_heap_obj(x_65);
x_76 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_1 = x_76;
goto block_63;
}
}
}
else
{
obj* x_77; obj* x_78; 
x_77 = lean::cnstr_get(x_65, 0);
lean::inc(x_77);
lean::dec(x_65);
x_78 = lean::cnstr_get(x_77, 1);
lean::inc(x_78);
lean::dec(x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; 
x_79 = lean::box(0);
x_1 = x_79;
goto block_63;
}
else
{
obj* x_80; 
x_80 = lean::cnstr_get(x_78, 1);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; 
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
lean::dec(x_81);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
x_1 = x_84;
goto block_63;
}
else
{
obj* x_85; 
lean::dec(x_81);
x_85 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_1 = x_85;
goto block_63;
}
}
else
{
obj* x_86; 
lean::dec(x_80);
lean::dec(x_78);
x_86 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_1 = x_86;
goto block_63;
}
}
}
}
block_63:
{
obj* x_2; obj* x_3; obj* x_42; obj* x_43; 
x_2 = lean::box(0);
x_42 = lean::box(3);
x_43 = l_Lean_Parser_Syntax_asNode___main(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; 
x_44 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_3 = x_44;
goto block_41;
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_43);
if (x_45 == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_43, 0);
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
lean::free_heap_obj(x_43);
x_3 = x_2;
goto block_41;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
lean::dec(x_47);
x_50 = l_Lean_Parser_command_oldUnivParams_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::apply_1(x_51, x_49);
lean::cnstr_set(x_43, 0, x_52);
x_3 = x_43;
goto block_41;
}
else
{
obj* x_53; 
lean::dec(x_48);
lean::dec(x_47);
lean::free_heap_obj(x_43);
x_53 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_3 = x_53;
goto block_41;
}
}
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_43, 0);
lean::inc(x_54);
lean::dec(x_43);
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
x_3 = x_2;
goto block_41;
}
else
{
obj* x_56; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_55, 0);
lean::inc(x_57);
lean::dec(x_55);
x_58 = l_Lean_Parser_command_oldUnivParams_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::apply_1(x_59, x_57);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_3 = x_61;
goto block_41;
}
else
{
obj* x_62; 
lean::dec(x_56);
lean::dec(x_55);
x_62 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_3 = x_62;
goto block_41;
}
}
}
}
block_41:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_21; 
x_4 = l_Lean_Parser_command_identUnivParams_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::box(3);
x_7 = lean::apply_1(x_5, x_6);
x_8 = l_Lean_Parser_command_optDeclSig_HasView;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::apply_1(x_9, x_6);
x_21 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
x_22 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_11 = x_22;
goto block_20;
}
else
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_21);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_21, 0);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
lean::free_heap_obj(x_21);
x_11 = x_2;
goto block_20;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
x_28 = l_Lean_Parser_command_notationLike_HasView;
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::apply_1(x_29, x_27);
lean::cnstr_set(x_21, 0, x_30);
x_11 = x_21;
goto block_20;
}
else
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_25);
lean::free_heap_obj(x_21);
x_31 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_11 = x_31;
goto block_20;
}
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::cnstr_get(x_21, 0);
lean::inc(x_32);
lean::dec(x_21);
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
x_11 = x_2;
goto block_20;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
lean::dec(x_33);
x_36 = l_Lean_Parser_command_notationLike_HasView;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::apply_1(x_37, x_35);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_11 = x_39;
goto block_20;
}
else
{
obj* x_40; 
lean::dec(x_34);
lean::dec(x_33);
x_40 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_11 = x_40;
goto block_20;
}
}
}
}
block_20:
{
obj* x_12; 
x_12 = l_Lean_Parser_Syntax_asNode___main(x_6);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1;
x_14 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_3);
lean::cnstr_set(x_14, 3, x_7);
lean::cnstr_set(x_14, 4, x_10);
lean::cnstr_set(x_14, 5, x_11);
lean::cnstr_set(x_14, 6, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2;
x_18 = l_List_map___main___rarg(x_17, x_16);
x_19 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_2);
lean::cnstr_set(x_19, 2, x_3);
lean::cnstr_set(x_19, 3, x_7);
lean::cnstr_set(x_19, 4, x_10);
lean::cnstr_set(x_19, 5, x_11);
lean::cnstr_set(x_19, 6, x_18);
return x_19;
}
}
}
}
}
}
obj* l_Lean_Parser_command_inductive_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_148; 
x_148 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; 
x_149 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4;
return x_149;
}
else
{
obj* x_150; obj* x_151; 
x_150 = lean::cnstr_get(x_148, 0);
lean::inc(x_150);
lean::dec(x_148);
x_151 = lean::cnstr_get(x_150, 1);
lean::inc(x_151);
lean::dec(x_150);
if (lean::obj_tag(x_151) == 0)
{
obj* x_152; 
x_152 = lean::box(3);
x_2 = x_151;
x_3 = x_152;
goto block_147;
}
else
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = lean::cnstr_get(x_151, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_151, 1);
lean::inc(x_154);
lean::dec(x_151);
x_155 = l_Lean_Parser_Syntax_asNode___main(x_153);
if (lean::obj_tag(x_155) == 0)
{
if (lean::obj_tag(x_154) == 0)
{
obj* x_156; 
x_156 = lean::box(3);
x_2 = x_154;
x_3 = x_156;
goto block_147;
}
else
{
obj* x_157; obj* x_158; 
x_157 = lean::cnstr_get(x_154, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_154, 1);
lean::inc(x_158);
lean::dec(x_154);
x_2 = x_158;
x_3 = x_157;
goto block_147;
}
}
else
{
obj* x_159; obj* x_160; obj* x_161; 
x_159 = lean::cnstr_get(x_155, 0);
lean::inc(x_159);
lean::dec(x_155);
x_160 = lean::cnstr_get(x_159, 1);
lean::inc(x_160);
lean::dec(x_159);
x_161 = l_List_append___rarg(x_160, x_154);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; 
x_162 = lean::box(3);
x_2 = x_161;
x_3 = x_162;
goto block_147;
}
else
{
obj* x_163; obj* x_164; 
x_163 = lean::cnstr_get(x_161, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_161, 1);
lean::inc(x_164);
lean::dec(x_161);
x_2 = x_164;
x_3 = x_163;
goto block_147;
}
}
}
}
block_147:
{
obj* x_4; obj* x_125; 
x_125 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; 
x_126 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_126;
goto block_124;
}
else
{
uint8 x_127; 
x_127 = !lean::is_exclusive(x_125);
if (x_127 == 0)
{
obj* x_128; obj* x_129; 
x_128 = lean::cnstr_get(x_125, 0);
x_129 = lean::cnstr_get(x_128, 1);
lean::inc(x_129);
lean::dec(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; 
lean::free_heap_obj(x_125);
x_130 = lean::box(0);
x_4 = x_130;
goto block_124;
}
else
{
obj* x_131; 
x_131 = lean::cnstr_get(x_129, 1);
lean::inc(x_131);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; 
x_132 = lean::cnstr_get(x_129, 0);
lean::inc(x_132);
lean::dec(x_129);
if (lean::obj_tag(x_132) == 0)
{
obj* x_133; obj* x_134; 
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
lean::dec(x_132);
lean::cnstr_set(x_125, 0, x_133);
x_134 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_134, 0, x_125);
x_4 = x_134;
goto block_124;
}
else
{
obj* x_135; 
lean::dec(x_132);
lean::free_heap_obj(x_125);
x_135 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_135;
goto block_124;
}
}
else
{
obj* x_136; 
lean::dec(x_131);
lean::dec(x_129);
lean::free_heap_obj(x_125);
x_136 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_136;
goto block_124;
}
}
}
else
{
obj* x_137; obj* x_138; 
x_137 = lean::cnstr_get(x_125, 0);
lean::inc(x_137);
lean::dec(x_125);
x_138 = lean::cnstr_get(x_137, 1);
lean::inc(x_138);
lean::dec(x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; 
x_139 = lean::box(0);
x_4 = x_139;
goto block_124;
}
else
{
obj* x_140; 
x_140 = lean::cnstr_get(x_138, 1);
lean::inc(x_140);
if (lean::obj_tag(x_140) == 0)
{
obj* x_141; 
x_141 = lean::cnstr_get(x_138, 0);
lean::inc(x_141);
lean::dec(x_138);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_143; obj* x_144; 
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
lean::dec(x_141);
x_143 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_143, 0, x_142);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_143);
x_4 = x_144;
goto block_124;
}
else
{
obj* x_145; 
lean::dec(x_141);
x_145 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_145;
goto block_124;
}
}
else
{
obj* x_146; 
lean::dec(x_140);
lean::dec(x_138);
x_146 = l_Lean_Parser_command_notation_HasView_x27___lambda__1___closed__1;
x_4 = x_146;
goto block_124;
}
}
}
}
block_124:
{
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_121; 
x_121 = lean::box(3);
x_5 = x_2;
x_6 = x_121;
goto block_120;
}
else
{
obj* x_122; obj* x_123; 
x_122 = lean::cnstr_get(x_2, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_2, 1);
lean::inc(x_123);
lean::dec(x_2);
x_5 = x_123;
x_6 = x_122;
goto block_120;
}
block_120:
{
obj* x_7; 
if (lean::obj_tag(x_6) == 0)
{
obj* x_117; obj* x_118; 
x_117 = lean::cnstr_get(x_6, 0);
lean::inc(x_117);
lean::dec(x_6);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
x_7 = x_118;
goto block_116;
}
else
{
obj* x_119; 
lean::dec(x_6);
x_119 = lean::box(0);
x_7 = x_119;
goto block_116;
}
block_116:
{
obj* x_8; obj* x_9; 
if (lean::obj_tag(x_5) == 0)
{
obj* x_113; 
x_113 = lean::box(3);
x_8 = x_5;
x_9 = x_113;
goto block_112;
}
else
{
obj* x_114; obj* x_115; 
x_114 = lean::cnstr_get(x_5, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_5, 1);
lean::inc(x_115);
lean::dec(x_5);
x_8 = x_115;
x_9 = x_114;
goto block_112;
}
block_112:
{
obj* x_10; obj* x_90; 
x_90 = l_Lean_Parser_Syntax_asNode___main(x_9);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; 
x_91 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_10 = x_91;
goto block_89;
}
else
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_90);
if (x_92 == 0)
{
obj* x_93; obj* x_94; 
x_93 = lean::cnstr_get(x_90, 0);
x_94 = lean::cnstr_get(x_93, 1);
lean::inc(x_94);
lean::dec(x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; 
lean::free_heap_obj(x_90);
x_95 = lean::box(0);
x_10 = x_95;
goto block_89;
}
else
{
obj* x_96; 
x_96 = lean::cnstr_get(x_94, 1);
lean::inc(x_96);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_97 = lean::cnstr_get(x_94, 0);
lean::inc(x_97);
lean::dec(x_94);
x_98 = l_Lean_Parser_command_oldUnivParams_HasView;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_100 = lean::apply_1(x_99, x_97);
lean::cnstr_set(x_90, 0, x_100);
x_10 = x_90;
goto block_89;
}
else
{
obj* x_101; 
lean::dec(x_96);
lean::dec(x_94);
lean::free_heap_obj(x_90);
x_101 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_10 = x_101;
goto block_89;
}
}
}
else
{
obj* x_102; obj* x_103; 
x_102 = lean::cnstr_get(x_90, 0);
lean::inc(x_102);
lean::dec(x_90);
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
lean::dec(x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; 
x_104 = lean::box(0);
x_10 = x_104;
goto block_89;
}
else
{
obj* x_105; 
x_105 = lean::cnstr_get(x_103, 1);
lean::inc(x_105);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_106 = lean::cnstr_get(x_103, 0);
lean::inc(x_106);
lean::dec(x_103);
x_107 = l_Lean_Parser_command_oldUnivParams_HasView;
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_109 = lean::apply_1(x_108, x_106);
x_110 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_110, 0, x_109);
x_10 = x_110;
goto block_89;
}
else
{
obj* x_111; 
lean::dec(x_105);
lean::dec(x_103);
x_111 = l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5;
x_10 = x_111;
goto block_89;
}
}
}
}
block_89:
{
obj* x_11; obj* x_12; 
if (lean::obj_tag(x_8) == 0)
{
obj* x_86; 
x_86 = lean::box(3);
x_11 = x_8;
x_12 = x_86;
goto block_85;
}
else
{
obj* x_87; obj* x_88; 
x_87 = lean::cnstr_get(x_8, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_8, 1);
lean::inc(x_88);
lean::dec(x_8);
x_11 = x_88;
x_12 = x_87;
goto block_85;
}
block_85:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = l_Lean_Parser_command_identUnivParams_HasView;
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_12);
if (lean::obj_tag(x_11) == 0)
{
obj* x_82; 
x_82 = lean::box(3);
x_16 = x_11;
x_17 = x_82;
goto block_81;
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_11, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_11, 1);
lean::inc(x_84);
lean::dec(x_11);
x_16 = x_84;
x_17 = x_83;
goto block_81;
}
block_81:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_32; obj* x_33; obj* x_43; obj* x_44; 
x_18 = l_Lean_Parser_command_optDeclSig_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::apply_1(x_19, x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_78; 
x_78 = lean::box(3);
x_43 = x_16;
x_44 = x_78;
goto block_77;
}
else
{
obj* x_79; obj* x_80; 
x_79 = lean::cnstr_get(x_16, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_16, 1);
lean::inc(x_80);
lean::dec(x_16);
x_43 = x_80;
x_44 = x_79;
goto block_77;
}
block_31:
{
obj* x_22; obj* x_23; 
x_22 = lean::box(3);
x_23 = l_Lean_Parser_Syntax_asNode___main(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
x_24 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1;
x_25 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_7);
lean::cnstr_set(x_25, 2, x_10);
lean::cnstr_set(x_25, 3, x_15);
lean::cnstr_set(x_25, 4, x_20);
lean::cnstr_set(x_25, 5, x_21);
lean::cnstr_set(x_25, 6, x_24);
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
x_28 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2;
x_29 = l_List_map___main___rarg(x_28, x_27);
x_30 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_30, 0, x_4);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_15);
lean::cnstr_set(x_30, 4, x_20);
lean::cnstr_set(x_30, 5, x_21);
lean::cnstr_set(x_30, 6, x_29);
return x_30;
}
}
block_42:
{
obj* x_34; 
x_34 = l_Lean_Parser_Syntax_asNode___main(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; 
x_35 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_36, 0, x_4);
lean::cnstr_set(x_36, 1, x_7);
lean::cnstr_set(x_36, 2, x_10);
lean::cnstr_set(x_36, 3, x_15);
lean::cnstr_set(x_36, 4, x_20);
lean::cnstr_set(x_36, 5, x_32);
lean::cnstr_set(x_36, 6, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
lean::dec(x_34);
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_39 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2;
x_40 = l_List_map___main___rarg(x_39, x_38);
x_41 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_41, 0, x_4);
lean::cnstr_set(x_41, 1, x_7);
lean::cnstr_set(x_41, 2, x_10);
lean::cnstr_set(x_41, 3, x_15);
lean::cnstr_set(x_41, 4, x_20);
lean::cnstr_set(x_41, 5, x_32);
lean::cnstr_set(x_41, 6, x_40);
return x_41;
}
}
block_77:
{
obj* x_45; 
x_45 = l_Lean_Parser_Syntax_asNode___main(x_44);
if (lean::obj_tag(x_45) == 0)
{
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_21 = x_46;
goto block_31;
}
else
{
obj* x_47; obj* x_48; 
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_48 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_32 = x_48;
x_33 = x_47;
goto block_42;
}
}
else
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_45);
if (x_49 == 0)
{
obj* x_50; obj* x_51; 
x_50 = lean::cnstr_get(x_45, 0);
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; 
lean::free_heap_obj(x_45);
x_52 = lean::box(0);
if (lean::obj_tag(x_43) == 0)
{
x_21 = x_52;
goto block_31;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_43, 0);
lean::inc(x_53);
lean::dec(x_43);
x_32 = x_52;
x_33 = x_53;
goto block_42;
}
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_55 = lean::cnstr_get(x_51, 0);
lean::inc(x_55);
lean::dec(x_51);
x_56 = l_Lean_Parser_command_notationLike_HasView;
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::apply_1(x_57, x_55);
lean::cnstr_set(x_45, 0, x_58);
if (lean::obj_tag(x_43) == 0)
{
x_21 = x_45;
goto block_31;
}
else
{
obj* x_59; 
x_59 = lean::cnstr_get(x_43, 0);
lean::inc(x_59);
lean::dec(x_43);
x_32 = x_45;
x_33 = x_59;
goto block_42;
}
}
else
{
lean::dec(x_54);
lean::dec(x_51);
lean::free_heap_obj(x_45);
if (lean::obj_tag(x_43) == 0)
{
obj* x_60; 
x_60 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_21 = x_60;
goto block_31;
}
else
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_43, 0);
lean::inc(x_61);
lean::dec(x_43);
x_62 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_32 = x_62;
x_33 = x_61;
goto block_42;
}
}
}
}
else
{
obj* x_63; obj* x_64; 
x_63 = lean::cnstr_get(x_45, 0);
lean::inc(x_63);
lean::dec(x_45);
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
lean::dec(x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; 
x_65 = lean::box(0);
if (lean::obj_tag(x_43) == 0)
{
x_21 = x_65;
goto block_31;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_43, 0);
lean::inc(x_66);
lean::dec(x_43);
x_32 = x_65;
x_33 = x_66;
goto block_42;
}
}
else
{
obj* x_67; 
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
lean::dec(x_64);
x_69 = l_Lean_Parser_command_notationLike_HasView;
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::apply_1(x_70, x_68);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
if (lean::obj_tag(x_43) == 0)
{
x_21 = x_72;
goto block_31;
}
else
{
obj* x_73; 
x_73 = lean::cnstr_get(x_43, 0);
lean::inc(x_73);
lean::dec(x_43);
x_32 = x_72;
x_33 = x_73;
goto block_42;
}
}
else
{
lean::dec(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_43) == 0)
{
obj* x_74; 
x_74 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_21 = x_74;
goto block_31;
}
else
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_43, 0);
lean::inc(x_75);
lean::dec(x_43);
x_76 = l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3;
x_32 = x_76;
x_33 = x_75;
goto block_42;
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
obj* _init_l_Lean_Parser_command_inductive_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inductive_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_inductive_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_inductive_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_inductive_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declaration");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("inner");
x_11 = lean_name_mk_string(x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_defLike_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_command_declaration_inner;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
case 1:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Lean_Parser_command_instance_HasView;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::apply_1(x_15, x_13);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_command_declaration_inner;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
case 2:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_24 = l_Lean_Parser_command_example_HasView;
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
x_26 = lean::apply_1(x_25, x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
x_28 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_2);
x_31 = l_Lean_Parser_command_declaration_inner;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
case 3:
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_34 = l_Lean_Parser_command_axiom_HasView;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_33);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_2);
x_38 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
x_41 = l_Lean_Parser_command_declaration_inner;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
case 4:
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_1, 0);
lean::inc(x_43);
lean::dec(x_1);
x_44 = l_Lean_Parser_command_inductive_HasView;
x_45 = lean::cnstr_get(x_44, 1);
lean::inc(x_45);
x_46 = lean::apply_1(x_45, x_43);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_2);
x_48 = l_Lean_Parser_command_mixfix_kind_HasView_x27___elambda__1___closed__6;
x_49 = l_Lean_Parser_Syntax_mkNode(x_48, x_47);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_2);
x_51 = l_Lean_Parser_command_declaration_inner;
x_52 = l_Lean_Parser_Syntax_mkNode(x_51, x_50);
return x_52;
}
default: 
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
x_54 = l_Lean_Parser_command_structure_HasView;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_56 = lean::apply_1(x_55, x_53);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_2);
x_58 = l_Lean_Parser_Level_leading_HasView_x27___elambda__1___closed__3;
x_59 = l_Lean_Parser_Syntax_mkNode(x_58, x_57);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_2);
x_61 = l_Lean_Parser_command_declaration_inner;
x_62 = l_Lean_Parser_Syntax_mkNode(x_61, x_60);
return x_62;
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_command_defLike_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declaration");
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean::mk_string("inner");
x_11 = lean_name_mk_string(x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_17; 
lean::dec(x_15);
x_17 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_17;
}
case 1:
{
obj* x_18; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_18;
}
default: 
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
lean::dec(x_15);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::box(0);
x_23 = lean_name_dec_eq(x_20, x_22);
lean::dec(x_20);
if (x_23 == 0)
{
obj* x_24; 
lean::dec(x_21);
lean::dec(x_19);
x_24 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_24;
}
else
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::nat_dec_eq(x_21, x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_dec_eq(x_21, x_30);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(2u);
x_33 = lean::nat_dec_eq(x_21, x_32);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = lean::mk_nat_obj(3u);
x_35 = lean::nat_dec_eq(x_21, x_34);
if (x_35 == 0)
{
obj* x_36; uint8 x_37; 
x_36 = lean::mk_nat_obj(4u);
x_37 = lean::nat_dec_eq(x_21, x_36);
lean::dec(x_21);
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = l_Lean_Parser_command_structure_HasView;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::apply_1(x_39, x_27);
x_41 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = l_Lean_Parser_command_inductive_HasView;
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::apply_1(x_43, x_27);
x_45 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_21);
x_46 = l_Lean_Parser_command_axiom_HasView;
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::apply_1(x_47, x_27);
x_49 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_21);
x_50 = l_Lean_Parser_command_example_HasView;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::apply_1(x_51, x_27);
x_53 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_21);
x_54 = l_Lean_Parser_command_instance_HasView;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_56 = lean::apply_1(x_55, x_27);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_21);
x_58 = l_Lean_Parser_command_defLike_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::apply_1(x_59, x_27);
x_61 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
else
{
obj* x_62; 
lean::dec(x_26);
lean::dec(x_21);
lean::dec(x_19);
x_62 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_62;
}
}
}
}
}
}
}
else
{
obj* x_63; 
lean::dec(x_11);
lean::dec(x_6);
x_63 = l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1;
return x_63;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_inner_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declaration_inner_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declaration_inner_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declaration() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("command");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string("declaration");
x_9 = lean_name_mk_string(x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_command_declModifiers_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_2);
x_7 = l_Lean_Parser_command_declaration_inner_HasView;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_9 = lean::apply_1(x_8, x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_command_declaration;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_Lean_Parser_command_declModifiers_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_command_declaration_inner_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_command_declaration_inner_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_command_declaration_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_Lean_Parser_command_declModifiers_HasView;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::apply_1(x_10, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_13; 
x_12 = l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_15 = l_Lean_Parser_command_declaration_inner_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_command_declaration_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_command_declaration_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_1 = lean::mk_string("def");
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::mk_string("abbreviation");
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_4, x_2);
lean::dec(x_4);
x_6 = lean::mk_string("abbrev");
x_7 = l_Lean_Parser_symbol_tokens___rarg(x_6, x_2);
lean::dec(x_6);
x_8 = lean::mk_string("theorem");
x_9 = l_Lean_Parser_symbol_tokens___rarg(x_8, x_2);
lean::dec(x_8);
x_10 = lean::mk_string("constant");
x_11 = l_Lean_Parser_symbol_tokens___rarg(x_10, x_2);
lean::dec(x_10);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_List_cons_tokens___rarg(x_11, x_12);
lean::dec(x_11);
x_14 = l_Lean_Parser_List_cons_tokens___rarg(x_9, x_13);
lean::dec(x_13);
lean::dec(x_9);
x_15 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_16 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_15);
lean::dec(x_15);
lean::dec(x_5);
x_17 = l_Lean_Parser_List_cons_tokens___rarg(x_3, x_16);
lean::dec(x_16);
lean::dec(x_3);
x_18 = l_Lean_Parser_tokens___rarg(x_17);
lean::dec(x_17);
x_19 = l_Lean_Parser_List_cons_tokens___rarg(x_18, x_12);
lean::dec(x_18);
x_20 = l_Lean_Parser_tokens___rarg(x_19);
lean::dec(x_19);
x_21 = l_Lean_Parser_command_oldUnivParams_Parser_Lean_Parser_HasTokens;
x_22 = l_Lean_Parser_tokens___rarg(x_21);
x_23 = l_Lean_Parser_command_declVal_Parser_Lean_Parser_HasTokens;
x_24 = l_Lean_Parser_List_cons_tokens___rarg(x_23, x_12);
x_25 = l_Lean_Parser_command_optDeclSig_Parser_Lean_Parser_HasTokens;
x_26 = l_Lean_Parser_List_cons_tokens___rarg(x_25, x_24);
x_27 = l_Lean_Parser_command_identUnivParams_Parser_Lean_Parser_HasTokens;
x_28 = l_Lean_Parser_List_cons_tokens___rarg(x_27, x_26);
lean::dec(x_26);
x_29 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_28);
lean::dec(x_28);
x_30 = l_Lean_Parser_List_cons_tokens___rarg(x_20, x_29);
lean::dec(x_29);
lean::dec(x_20);
x_31 = l_Lean_Parser_tokens___rarg(x_30);
lean::dec(x_30);
x_32 = lean::mk_string("instance");
x_33 = l_Lean_Parser_symbol_tokens___rarg(x_32, x_2);
lean::dec(x_32);
x_34 = l_Lean_Parser_tokens___rarg(x_27);
x_35 = l_Lean_Parser_command_declSig_Parser_Lean_Parser_HasTokens;
x_36 = l_Lean_Parser_List_cons_tokens___rarg(x_35, x_24);
lean::dec(x_24);
x_37 = l_Lean_Parser_List_cons_tokens___rarg(x_34, x_36);
lean::dec(x_34);
x_38 = l_Lean_Parser_List_cons_tokens___rarg(x_33, x_37);
lean::dec(x_37);
lean::dec(x_33);
x_39 = l_Lean_Parser_tokens___rarg(x_38);
lean::dec(x_38);
x_40 = lean::mk_string("example");
x_41 = l_Lean_Parser_symbol_tokens___rarg(x_40, x_2);
lean::dec(x_40);
x_42 = l_Lean_Parser_List_cons_tokens___rarg(x_41, x_36);
lean::dec(x_36);
lean::dec(x_41);
x_43 = l_Lean_Parser_tokens___rarg(x_42);
lean::dec(x_42);
x_44 = lean::mk_string("axiom");
x_45 = l_Lean_Parser_symbol_tokens___rarg(x_44, x_2);
lean::dec(x_44);
x_46 = l_Lean_Parser_List_cons_tokens___rarg(x_45, x_12);
lean::dec(x_45);
x_47 = l_Lean_Parser_tokens___rarg(x_46);
lean::dec(x_46);
x_48 = l_Lean_Parser_List_cons_tokens___rarg(x_47, x_12);
lean::dec(x_47);
x_49 = l_Lean_Parser_tokens___rarg(x_48);
lean::dec(x_48);
x_50 = l_Lean_Parser_List_cons_tokens___rarg(x_35, x_12);
x_51 = l_Lean_Parser_List_cons_tokens___rarg(x_27, x_50);
lean::dec(x_50);
x_52 = l_Lean_Parser_List_cons_tokens___rarg(x_49, x_51);
lean::dec(x_51);
lean::dec(x_49);
x_53 = l_Lean_Parser_tokens___rarg(x_52);
lean::dec(x_52);
x_54 = lean::mk_string("class");
x_55 = l_Lean_Parser_symbol_tokens___rarg(x_54, x_2);
lean::dec(x_54);
x_56 = l_Lean_Parser_tokens___rarg(x_55);
lean::dec(x_55);
x_57 = lean::mk_string("inductive");
x_58 = l_Lean_Parser_symbol_tokens___rarg(x_57, x_2);
lean::dec(x_57);
x_59 = l_Lean_Parser_List_cons_tokens___rarg(x_58, x_12);
lean::dec(x_58);
x_60 = l_Lean_Parser_List_cons_tokens___rarg(x_56, x_59);
lean::dec(x_59);
lean::dec(x_56);
x_61 = l_Lean_Parser_tokens___rarg(x_60);
lean::dec(x_60);
x_62 = l_Lean_Parser_tokens___rarg(x_61);
lean::dec(x_61);
x_63 = l_Lean_Parser_command_notationLike_Parser_Lean_Parser_HasTokens;
x_64 = l_Lean_Parser_tokens___rarg(x_63);
x_65 = l_Lean_Parser_tokens___rarg(x_64);
lean::dec(x_64);
x_66 = l_Lean_Parser_command_introRule_Parser_Lean_Parser_HasTokens;
x_67 = l_Lean_Parser_tokens___rarg(x_66);
x_68 = l_Lean_Parser_List_cons_tokens___rarg(x_67, x_12);
lean::dec(x_67);
x_69 = l_Lean_Parser_List_cons_tokens___rarg(x_65, x_68);
lean::dec(x_68);
lean::dec(x_65);
x_70 = l_Lean_Parser_List_cons_tokens___rarg(x_25, x_69);
lean::dec(x_69);
x_71 = l_Lean_Parser_List_cons_tokens___rarg(x_27, x_70);
lean::dec(x_70);
x_72 = l_Lean_Parser_List_cons_tokens___rarg(x_22, x_71);
lean::dec(x_71);
lean::dec(x_22);
x_73 = l_Lean_Parser_List_cons_tokens___rarg(x_62, x_72);
lean::dec(x_72);
lean::dec(x_62);
x_74 = l_Lean_Parser_tokens___rarg(x_73);
lean::dec(x_73);
x_75 = l_Lean_Parser_command_structure_Parser_Lean_Parser_HasTokens;
x_76 = l_Lean_Parser_List_cons_tokens___rarg(x_75, x_12);
x_77 = l_Lean_Parser_List_cons_tokens___rarg(x_74, x_76);
lean::dec(x_76);
lean::dec(x_74);
x_78 = l_Lean_Parser_List_cons_tokens___rarg(x_53, x_77);
lean::dec(x_77);
lean::dec(x_53);
x_79 = l_Lean_Parser_List_cons_tokens___rarg(x_43, x_78);
lean::dec(x_78);
lean::dec(x_43);
x_80 = l_Lean_Parser_List_cons_tokens___rarg(x_39, x_79);
lean::dec(x_79);
lean::dec(x_39);
x_81 = l_Lean_Parser_List_cons_tokens___rarg(x_31, x_80);
lean::dec(x_80);
lean::dec(x_31);
x_82 = l_Lean_Parser_tokens___rarg(x_81);
lean::dec(x_81);
x_83 = l_Lean_Parser_List_cons_tokens___rarg(x_82, x_12);
lean::dec(x_82);
x_84 = l_Lean_Parser_tokens___rarg(x_83);
lean::dec(x_83);
x_85 = l_Lean_Parser_List_cons_tokens___rarg(x_84, x_12);
lean::dec(x_84);
x_86 = l_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens;
x_87 = l_Lean_Parser_List_cons_tokens___rarg(x_86, x_85);
lean::dec(x_85);
x_88 = l_Lean_Parser_tokens___rarg(x_87);
lean::dec(x_87);
return x_88;
}
}
obj* l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_6, x_1, x_2, x_3, x_4, x_5);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_9);
lean::cnstr_set(x_7, 0, x_10);
return x_7;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_1 = l_Lean_Parser_CommandParserM_Monad(lean::box(0));
x_2 = l_Lean_Parser_CommandParserM_MonadExcept(lean::box(0));
x_3 = l_Lean_Parser_CommandParserM_Lean_Parser_MonadParsec(lean::box(0));
x_4 = l_Lean_Parser_CommandParserM_Alternative(lean::box(0));
x_5 = lean::mk_string("def");
x_6 = l_String_trim(x_5);
lean::dec(x_5);
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::mk_string("abbreviation");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::mk_string("abbrev");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_8);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::mk_string("theorem");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_8);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::mk_string("constant");
x_23 = l_String_trim(x_22);
lean::dec(x_22);
lean::inc(x_23);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_8);
lean::closure_set(x_25, 2, x_24);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_21);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_17);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_13);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_32, 0, x_31);
lean::closure_set(x_32, 1, x_8);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
x_34 = l_Lean_Parser_command_defLike_kind;
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_35, 0, x_34);
lean::closure_set(x_35, 1, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_37 = 0;
x_38 = lean::box(x_37);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_39, 0, x_36);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_Parser), 4, 0);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_26);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
lean::inc(x_41);
lean::inc(x_42);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
lean::inc(x_44);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
lean::inc(x_39);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_39);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_35);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_command_defLike;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_49, 0, x_48);
lean::closure_set(x_49, 1, x_47);
x_50 = lean::mk_string("instance");
x_51 = l_String_trim(x_50);
lean::dec(x_50);
lean::inc(x_51);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_52, 0, x_51);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_53, 0, x_51);
lean::closure_set(x_53, 1, x_8);
lean::closure_set(x_53, 2, x_52);
x_54 = lean::box(x_37);
lean::inc(x_44);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_55, 0, x_44);
lean::closure_set(x_55, 1, x_54);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_Parser), 4, 0);
lean::inc(x_56);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_41);
lean::inc(x_57);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_53);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_Lean_Parser_command_instance;
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_61, 0, x_60);
lean::closure_set(x_61, 1, x_59);
x_62 = lean::mk_string("example");
x_63 = l_String_trim(x_62);
lean::dec(x_62);
lean::inc(x_63);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_64, 0, x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_8);
lean::closure_set(x_65, 2, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_57);
x_67 = l_Lean_Parser_command_example;
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_68, 0, x_67);
lean::closure_set(x_68, 1, x_66);
x_69 = lean::mk_string("axiom");
x_70 = l_String_trim(x_69);
lean::dec(x_69);
lean::inc(x_70);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_71, 0, x_70);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_72, 0, x_70);
lean::closure_set(x_72, 1, x_8);
lean::closure_set(x_72, 2, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_26);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_74, 0, x_73);
lean::closure_set(x_74, 1, x_8);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_26);
x_76 = l_Lean_Parser_command_constantKeyword;
x_77 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_77, 0, x_76);
lean::closure_set(x_77, 1, x_75);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_56);
lean::cnstr_set(x_78, 1, x_26);
lean::inc(x_44);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_44);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_79);
x_81 = l_Lean_Parser_command_axiom;
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_82, 0, x_81);
lean::closure_set(x_82, 1, x_80);
x_83 = lean::mk_string("class");
x_84 = l_String_trim(x_83);
lean::dec(x_83);
lean::inc(x_84);
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_85, 0, x_84);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_86, 0, x_84);
lean::closure_set(x_86, 1, x_8);
lean::closure_set(x_86, 2, x_85);
x_87 = lean::box(x_37);
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_88, 0, x_86);
lean::closure_set(x_88, 1, x_87);
x_89 = lean::mk_string("inductive");
x_90 = l_String_trim(x_89);
lean::dec(x_89);
lean::inc(x_90);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_91, 0, x_90);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_92, 0, x_90);
lean::closure_set(x_92, 1, x_8);
lean::closure_set(x_92, 2, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_26);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_88);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_95, 0, x_94);
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_97, 0, x_96);
x_98 = lean::box(x_37);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_99, 0, x_97);
lean::closure_set(x_99, 1, x_98);
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_Parser), 4, 0);
x_101 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_101, 0, x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_26);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_99);
lean::cnstr_set(x_103, 1, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_42);
lean::cnstr_set(x_104, 1, x_103);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_44);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_39);
lean::cnstr_set(x_106, 1, x_105);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_95);
lean::cnstr_set(x_107, 1, x_106);
x_108 = l_Lean_Parser_command_inductive;
x_109 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_109, 0, x_108);
lean::closure_set(x_109, 1, x_107);
x_110 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_Parser), 4, 0);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_26);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_82);
lean::cnstr_set(x_113, 1, x_112);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_68);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_61);
lean::cnstr_set(x_115, 1, x_114);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_49);
lean::cnstr_set(x_116, 1, x_115);
x_117 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_117, 0, x_116);
lean::closure_set(x_117, 1, x_8);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_26);
x_119 = l_Lean_Parser_command_declaration_inner;
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_120, 0, x_119);
lean::closure_set(x_120, 1, x_118);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_26);
x_122 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_Parser), 4, 0);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
x_124 = l_Lean_Parser_command_declaration;
x_125 = l_Lean_Parser_command_declaration_HasView;
x_126 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_124, x_123, x_125);
lean::dec(x_123);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_126;
}
}
obj* _init_l_Lean_Parser_command_declaration_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_1 = lean::mk_string("def");
x_2 = l_String_trim(x_1);
lean::dec(x_1);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_string("abbreviation");
x_7 = l_String_trim(x_6);
lean::dec(x_6);
lean::inc(x_7);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_4);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::mk_string("abbrev");
x_11 = l_String_trim(x_10);
lean::dec(x_10);
lean::inc(x_11);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::mk_string("theorem");
x_15 = l_String_trim(x_14);
lean::dec(x_14);
lean::inc(x_15);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_17, 0, x_15);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_16);
x_18 = lean::mk_string("constant");
x_19 = l_String_trim(x_18);
lean::dec(x_18);
lean::inc(x_19);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_4);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
x_30 = l_Lean_Parser_command_defLike_kind;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_31, 0, x_30);
lean::closure_set(x_31, 1, x_29);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_oldUnivParams_Parser), 4, 0);
x_33 = 0;
x_34 = lean::box(x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_35, 0, x_32);
lean::closure_set(x_35, 1, x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declVal_Parser), 4, 0);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_22);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_optDeclSig_Parser), 4, 0);
lean::inc(x_37);
lean::inc(x_38);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_identUnivParams_Parser), 4, 0);
lean::inc(x_40);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
lean::inc(x_35);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_35);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_31);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_Lean_Parser_command_defLike;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_45, 0, x_44);
lean::closure_set(x_45, 1, x_43);
x_46 = lean::mk_string("instance");
x_47 = l_String_trim(x_46);
lean::dec(x_46);
lean::inc(x_47);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_48, 0, x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_4);
lean::closure_set(x_49, 2, x_48);
x_50 = lean::box(x_33);
lean::inc(x_40);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_51, 0, x_40);
lean::closure_set(x_51, 1, x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declSig_Parser), 4, 0);
lean::inc(x_52);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_37);
lean::inc(x_53);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_49);
lean::cnstr_set(x_55, 1, x_54);
x_56 = l_Lean_Parser_command_instance;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_57, 0, x_56);
lean::closure_set(x_57, 1, x_55);
x_58 = lean::mk_string("example");
x_59 = l_String_trim(x_58);
lean::dec(x_58);
lean::inc(x_59);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_61, 0, x_59);
lean::closure_set(x_61, 1, x_4);
lean::closure_set(x_61, 2, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_53);
x_63 = l_Lean_Parser_command_example;
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_64, 0, x_63);
lean::closure_set(x_64, 1, x_62);
x_65 = lean::mk_string("axiom");
x_66 = l_String_trim(x_65);
lean::dec(x_65);
lean::inc(x_66);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_67, 0, x_66);
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_68, 0, x_66);
lean::closure_set(x_68, 1, x_4);
lean::closure_set(x_68, 2, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_22);
x_70 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_70, 0, x_69);
lean::closure_set(x_70, 1, x_4);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_22);
x_72 = l_Lean_Parser_command_constantKeyword;
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_73, 0, x_72);
lean::closure_set(x_73, 1, x_71);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_52);
lean::cnstr_set(x_74, 1, x_22);
lean::inc(x_40);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_40);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_Lean_Parser_command_axiom;
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_78, 0, x_77);
lean::closure_set(x_78, 1, x_76);
x_79 = lean::mk_string("class");
x_80 = l_String_trim(x_79);
lean::dec(x_79);
lean::inc(x_80);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_81, 0, x_80);
x_82 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_82, 0, x_80);
lean::closure_set(x_82, 1, x_4);
lean::closure_set(x_82, 2, x_81);
x_83 = lean::box(x_33);
x_84 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_84, 0, x_82);
lean::closure_set(x_84, 1, x_83);
x_85 = lean::mk_string("inductive");
x_86 = l_String_trim(x_85);
lean::dec(x_85);
lean::inc(x_86);
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_87, 0, x_86);
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_command_docComment_Parser_Lean_Parser_HasTokens___spec__1___boxed), 7, 3);
lean::closure_set(x_88, 0, x_86);
lean::closure_set(x_88, 1, x_4);
lean::closure_set(x_88, 2, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_22);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_84);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declaration_Parser_Lean_Parser_HasView___lambda__1), 5, 1);
lean::closure_set(x_91, 0, x_90);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_notationLike_Parser), 5, 0);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_termParser_run), 5, 1);
lean::closure_set(x_93, 0, x_92);
x_94 = lean::box(x_33);
x_95 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__1___boxed), 6, 2);
lean::closure_set(x_95, 0, x_93);
lean::closure_set(x_95, 1, x_94);
x_96 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_introRule_Parser), 4, 0);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___at_Lean_Parser_command_attrInstance_Parser_Lean_Parser_HasTokens___spec__2), 5, 1);
lean::closure_set(x_97, 0, x_96);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_22);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_38);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_40);
lean::cnstr_set(x_101, 1, x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_35);
lean::cnstr_set(x_102, 1, x_101);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_91);
lean::cnstr_set(x_103, 1, x_102);
x_104 = l_Lean_Parser_command_inductive;
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_105, 0, x_104);
lean::closure_set(x_105, 1, x_103);
x_106 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_structure_Parser), 4, 0);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_22);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_107);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_78);
lean::cnstr_set(x_109, 1, x_108);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_64);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_57);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_45);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_command_declModifiers_Parser_Lean_Parser_HasTokens___spec__2), 6, 2);
lean::closure_set(x_113, 0, x_112);
lean::closure_set(x_113, 1, x_4);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_22);
x_115 = l_Lean_Parser_command_declaration_inner;
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2), 6, 2);
lean::closure_set(x_116, 0, x_115);
lean::closure_set(x_116, 1, x_114);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_22);
x_118 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_command_declModifiers_Parser), 4, 0);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
obj* l_Lean_Parser_command_declaration_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_command_declaration;
x_6 = l_Lean_Parser_command_declaration_Parser___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_command_docComment_Parser___spec__2(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
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
l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_docComment_HasView_x27 = _init_l_Lean_Parser_command_docComment_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_docComment_HasView_x27);
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
l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_attrInstance_HasView_x27 = _init_l_Lean_Parser_command_attrInstance_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_attrInstance_HasView_x27);
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
l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_declAttributes_HasView_x27 = _init_l_Lean_Parser_command_declAttributes_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declAttributes_HasView_x27);
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
l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_visibility_HasView_x27 = _init_l_Lean_Parser_command_visibility_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView_x27);
l_Lean_Parser_command_visibility_HasView = _init_l_Lean_Parser_command_visibility_HasView();
lean::mark_persistent(l_Lean_Parser_command_visibility_HasView);
l_Lean_Parser_command_declModifiers = _init_l_Lean_Parser_command_declModifiers();
lean::mark_persistent(l_Lean_Parser_command_declModifiers);
l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_declModifiers_HasView_x27 = _init_l_Lean_Parser_command_declModifiers_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declModifiers_HasView_x27);
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
l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2 = _init_l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x27___elambda__2___closed__2);
l_Lean_Parser_command_declSig_HasView_x27 = _init_l_Lean_Parser_command_declSig_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declSig_HasView_x27);
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
l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_optDeclSig_HasView_x27 = _init_l_Lean_Parser_command_optDeclSig_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_optDeclSig_HasView_x27);
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
l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_equation_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_equation_HasView_x27 = _init_l_Lean_Parser_command_equation_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_equation_HasView_x27);
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
l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_command_simpleDeclVal_HasView_x27 = _init_l_Lean_Parser_command_simpleDeclVal_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView_x27);
l_Lean_Parser_command_simpleDeclVal_HasView = _init_l_Lean_Parser_command_simpleDeclVal_HasView();
lean::mark_persistent(l_Lean_Parser_command_simpleDeclVal_HasView);
l_Lean_Parser_command_declVal = _init_l_Lean_Parser_command_declVal();
lean::mark_persistent(l_Lean_Parser_command_declVal);
l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_command_declVal_HasView_x27 = _init_l_Lean_Parser_command_declVal_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declVal_HasView_x27);
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
l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_relaxedInferModifier_HasView_x27 = _init_l_Lean_Parser_command_relaxedInferModifier_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView_x27);
l_Lean_Parser_command_relaxedInferModifier_HasView = _init_l_Lean_Parser_command_relaxedInferModifier_HasView();
lean::mark_persistent(l_Lean_Parser_command_relaxedInferModifier_HasView);
l_Lean_Parser_command_strictInferModifier = _init_l_Lean_Parser_command_strictInferModifier();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier);
l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_strictInferModifier_HasView_x27 = _init_l_Lean_Parser_command_strictInferModifier_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView_x27);
l_Lean_Parser_command_strictInferModifier_HasView = _init_l_Lean_Parser_command_strictInferModifier_HasView();
lean::mark_persistent(l_Lean_Parser_command_strictInferModifier_HasView);
l_Lean_Parser_command_inferModifier = _init_l_Lean_Parser_command_inferModifier();
lean::mark_persistent(l_Lean_Parser_command_inferModifier);
l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_inferModifier_HasView_x27 = _init_l_Lean_Parser_command_inferModifier_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_inferModifier_HasView_x27);
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
l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_introRule_HasView_x27 = _init_l_Lean_Parser_command_introRule_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_introRule_HasView_x27);
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
l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structBinderContent_HasView_x27 = _init_l_Lean_Parser_command_structBinderContent_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structBinderContent_HasView_x27);
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
l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structExplicitBinderContent_HasView_x27 = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView_x27);
l_Lean_Parser_command_structExplicitBinderContent_HasView = _init_l_Lean_Parser_command_structExplicitBinderContent_HasView();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinderContent_HasView);
l_Lean_Parser_command_structExplicitBinder = _init_l_Lean_Parser_command_structExplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder);
l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_structExplicitBinder_HasView_x27 = _init_l_Lean_Parser_command_structExplicitBinder_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView_x27);
l_Lean_Parser_command_structExplicitBinder_HasView = _init_l_Lean_Parser_command_structExplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_structExplicitBinder_HasView);
l_Lean_Parser_command_structImplicitBinder = _init_l_Lean_Parser_command_structImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder);
l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_structImplicitBinder_HasView_x27 = _init_l_Lean_Parser_command_structImplicitBinder_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView_x27);
l_Lean_Parser_command_structImplicitBinder_HasView = _init_l_Lean_Parser_command_structImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_structImplicitBinder_HasView);
l_Lean_Parser_command_strictImplicitBinder = _init_l_Lean_Parser_command_strictImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder);
l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_strictImplicitBinder_HasView_x27 = _init_l_Lean_Parser_command_strictImplicitBinder_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView_x27);
l_Lean_Parser_command_strictImplicitBinder_HasView = _init_l_Lean_Parser_command_strictImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_strictImplicitBinder_HasView);
l_Lean_Parser_command_instImplicitBinder = _init_l_Lean_Parser_command_instImplicitBinder();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder);
l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_instImplicitBinder_HasView_x27 = _init_l_Lean_Parser_command_instImplicitBinder_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView_x27);
l_Lean_Parser_command_instImplicitBinder_HasView = _init_l_Lean_Parser_command_instImplicitBinder_HasView();
lean::mark_persistent(l_Lean_Parser_command_instImplicitBinder_HasView);
l_Lean_Parser_command_structureFieldBlock = _init_l_Lean_Parser_command_structureFieldBlock();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock);
l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structureFieldBlock_HasView_x27 = _init_l_Lean_Parser_command_structureFieldBlock_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structureFieldBlock_HasView_x27);
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
l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_oldUnivParams_HasView_x27 = _init_l_Lean_Parser_command_oldUnivParams_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_oldUnivParams_HasView_x27);
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
l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_univParams_HasView_x27 = _init_l_Lean_Parser_command_univParams_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView_x27);
l_Lean_Parser_command_univParams_HasView = _init_l_Lean_Parser_command_univParams_HasView();
lean::mark_persistent(l_Lean_Parser_command_univParams_HasView);
l_Lean_Parser_command_identUnivParams = _init_l_Lean_Parser_command_identUnivParams();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams);
l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_command_identUnivParams_HasView_x27 = _init_l_Lean_Parser_command_identUnivParams_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_identUnivParams_HasView_x27);
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
l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_structureKw_HasView_x27 = _init_l_Lean_Parser_command_structureKw_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView_x27);
l_Lean_Parser_command_structureKw_HasView = _init_l_Lean_Parser_command_structureKw_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureKw_HasView);
l_Lean_Parser_command_extends = _init_l_Lean_Parser_command_extends();
lean::mark_persistent(l_Lean_Parser_command_extends);
l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_extends_HasView_x27 = _init_l_Lean_Parser_command_extends_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView_x27);
l_Lean_Parser_command_extends_HasView = _init_l_Lean_Parser_command_extends_HasView();
lean::mark_persistent(l_Lean_Parser_command_extends_HasView);
l_Lean_Parser_command_structureCtor = _init_l_Lean_Parser_command_structureCtor();
lean::mark_persistent(l_Lean_Parser_command_structureCtor);
l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structureCtor_HasView_x27 = _init_l_Lean_Parser_command_structureCtor_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView_x27);
l_Lean_Parser_command_structureCtor_HasView = _init_l_Lean_Parser_command_structureCtor_HasView();
lean::mark_persistent(l_Lean_Parser_command_structureCtor_HasView);
l_Lean_Parser_command_structure = _init_l_Lean_Parser_command_structure();
lean::mark_persistent(l_Lean_Parser_command_structure);
l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6 = _init_l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27___lambda__1___closed__6);
l_Lean_Parser_command_structure_HasView_x27 = _init_l_Lean_Parser_command_structure_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_structure_HasView_x27);
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
l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__3);
l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__4);
l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___elambda__1___closed__5);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__6);
l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27___lambda__1___closed__7);
l_Lean_Parser_command_defLike_kind_HasView_x27 = _init_l_Lean_Parser_command_defLike_kind_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView_x27);
l_Lean_Parser_command_defLike_kind_HasView = _init_l_Lean_Parser_command_defLike_kind_HasView();
lean::mark_persistent(l_Lean_Parser_command_defLike_kind_HasView);
l_Lean_Parser_command_defLike = _init_l_Lean_Parser_command_defLike();
lean::mark_persistent(l_Lean_Parser_command_defLike);
l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_defLike_HasView_x27 = _init_l_Lean_Parser_command_defLike_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView_x27);
l_Lean_Parser_command_defLike_HasView = _init_l_Lean_Parser_command_defLike_HasView();
lean::mark_persistent(l_Lean_Parser_command_defLike_HasView);
l_Lean_Parser_command_instance = _init_l_Lean_Parser_command_instance();
lean::mark_persistent(l_Lean_Parser_command_instance);
l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_instance_HasView_x27 = _init_l_Lean_Parser_command_instance_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView_x27);
l_Lean_Parser_command_instance_HasView = _init_l_Lean_Parser_command_instance_HasView();
lean::mark_persistent(l_Lean_Parser_command_instance_HasView);
l_Lean_Parser_command_example = _init_l_Lean_Parser_command_example();
lean::mark_persistent(l_Lean_Parser_command_example);
l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_example_HasView_x27 = _init_l_Lean_Parser_command_example_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_example_HasView_x27);
l_Lean_Parser_command_example_HasView = _init_l_Lean_Parser_command_example_HasView();
lean::mark_persistent(l_Lean_Parser_command_example_HasView);
l_Lean_Parser_command_constantKeyword = _init_l_Lean_Parser_command_constantKeyword();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword);
l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_constantKeyword_HasView_x27 = _init_l_Lean_Parser_command_constantKeyword_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView_x27);
l_Lean_Parser_command_constantKeyword_HasView = _init_l_Lean_Parser_command_constantKeyword_HasView();
lean::mark_persistent(l_Lean_Parser_command_constantKeyword_HasView);
l_Lean_Parser_command_axiom = _init_l_Lean_Parser_command_axiom();
lean::mark_persistent(l_Lean_Parser_command_axiom);
l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_command_axiom_HasView_x27 = _init_l_Lean_Parser_command_axiom_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView_x27);
l_Lean_Parser_command_axiom_HasView = _init_l_Lean_Parser_command_axiom_HasView();
lean::mark_persistent(l_Lean_Parser_command_axiom_HasView);
l_Lean_Parser_command_inductive = _init_l_Lean_Parser_command_inductive();
lean::mark_persistent(l_Lean_Parser_command_inductive);
l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_command_inductive_HasView_x27 = _init_l_Lean_Parser_command_inductive_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView_x27);
l_Lean_Parser_command_inductive_HasView = _init_l_Lean_Parser_command_inductive_HasView();
lean::mark_persistent(l_Lean_Parser_command_inductive_HasView);
l_Lean_Parser_command_declaration_inner = _init_l_Lean_Parser_command_declaration_inner();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner);
l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_command_declaration_inner_HasView_x27 = _init_l_Lean_Parser_command_declaration_inner_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView_x27);
l_Lean_Parser_command_declaration_inner_HasView = _init_l_Lean_Parser_command_declaration_inner_HasView();
lean::mark_persistent(l_Lean_Parser_command_declaration_inner_HasView);
l_Lean_Parser_command_declaration = _init_l_Lean_Parser_command_declaration();
lean::mark_persistent(l_Lean_Parser_command_declaration);
l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2 = _init_l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x27___elambda__2___closed__2);
l_Lean_Parser_command_declaration_HasView_x27 = _init_l_Lean_Parser_command_declaration_HasView_x27();
lean::mark_persistent(l_Lean_Parser_command_declaration_HasView_x27);
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
