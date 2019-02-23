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
extern obj* l_lean_parser_command_reserve__mixfix;
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
extern obj* l_lean_parser_term_subtype;
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj*, obj*, obj*);
obj* l_lean_expander_mk__simple__binder___boxed(obj*, obj*, obj*);
obj* l_lean_expander_intro__rule_transform___boxed(obj*, obj*);
extern obj* l_lean_parser_command_variables;
extern obj* l_lean_parser_term_arrow_has__view;
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_expander_let_transform___closed__1;
obj* l_lean_expander_universes_transform___boxed(obj*, obj*);
obj* l_lean_expander_let_transform___boxed(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__name__ident(obj*);
obj* l_lean_expander_variable_transform___boxed(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder(obj*, obj*);
obj* l_lean_expander_sorry_transform___closed__1;
obj* l_id___boxed(obj*);
obj* l_lean_expander_pi_transform___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_term_binder__ident_has__view;
obj* l_lean_expander_if_transform___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(uint8, obj*, obj*);
extern obj* l_lean_parser_command_constant_has__view;
obj* l_lean_expander_coe__simple__binder__binders(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj*, obj*);
obj* l_lean_expander_assume_transform___boxed(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_universes;
obj* l_lean_expander_get__opt__type___main___boxed(obj*);
obj* l_lean_expander_expand(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__2;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_lean_expander_if_transform(obj*, obj*);
obj* l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2___boxed(obj*, obj*);
obj* l_lean_expander_no__expansion___boxed(obj*);
extern obj* l_lean_parser_command_declaration;
obj* l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(obj*);
obj* l_lean_expander_universes_transform(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8, obj*, obj*);
obj* l_lean_expander_error___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10___boxed(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7___boxed(obj*, obj*, obj*);
obj* l_lean_expander_variables_transform(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
obj* l_lean_expander_mixfix_transform___closed__2;
extern obj* l_lean_parser_command_variable;
extern obj* l_lean_parser_term_match_has__view;
obj* l_lean_expander_mixfix_transform___closed__1;
obj* l_lean_expander_coe__binders__ext___rarg(obj*, obj*);
extern obj* l_lean_parser_term_if_has__view;
extern obj* l_lean_parser_term_bracketed__binders;
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_expander_if_transform___closed__2;
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(obj*, obj*);
obj* l_lean_expander_arrow_transform___boxed(obj*, obj*);
obj* l_lean_expander_paren_transform___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj*, obj*);
obj* l_lean_expander_coe__binders__ext(obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(obj*, obj*);
obj* l_lean_parser_syntax_flip__scopes___main(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___boxed(obj*, obj*, obj*);
obj* l_lean_expander_constant_transform___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___boxed(obj*);
obj* l_lean_expander_assume_transform___closed__1;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view;
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1(obj*);
obj* l_lean_expander_mk__notation__transformer___lambda__1___boxed(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2___boxed(obj*);
extern obj* l_lean_parser_command_mixfix_has__view;
obj* l_lean_expander_intro__rule_transform(obj*, obj*);
extern obj* l_lean_parser_command_universes_has__view;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__6;
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
obj* l_lean_expander_declaration_transform___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(uint8, obj*, obj*, obj*);
obj* l_lean_expander_subtype_transform___closed__1;
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_transform__m_monad;
obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13___boxed(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
extern obj* l_lean_parser_command_variable_has__view;
obj* l_lean_expander_arrow_transform___closed__1;
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___boxed(obj*);
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
extern obj* l_lean_parser_level_leading;
obj* l___private_init_lean_expander_1__pop__stx__arg___closed__1;
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__3;
obj* l_lean_expander_builtin__transformers;
obj* l_lean_expander_mk__simple__binder___closed__4;
obj* l_lean_expander_if_transform___closed__3;
obj* l_lean_expander_if_transform___boxed(obj*, obj*);
obj* l_lean_expander_expander__config_has__lift___boxed(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
extern obj* l_lean_parser_term_pi_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16___boxed(obj*, obj*);
obj* l___private_init_lean_expander_1__pop__stx__arg___boxed(obj*, obj*);
extern obj* l_lean_parser_command_universe_has__view;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj*);
extern obj* l_lean_parser_ident__univs;
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj*);
extern obj* l_lean_parser_term_sorry;
obj* l___private_init_lean_expander_1__pop__stx__arg(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1___boxed(obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___boxed(obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform___closed__1;
extern obj* l_lean_parser_command_intro__rule_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14___boxed(obj*, obj*);
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___boxed(obj*, obj*);
obj* l_lean_expander_lambda_transform___lambda__1___boxed(obj*, obj*);
obj* l_lean_expander_bracketed__binders_transform(obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
obj* l_lean_expander_sorry_transform___boxed(obj*, obj*);
extern obj* l_lean_parser_command_variables_has__view;
obj* l_lean_expander_mk__simple__binder___closed__7;
obj* l_lean_expander_expand__binders___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_binding__annotation__update_parser___closed__1;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4___boxed(obj*, obj*);
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17___boxed(obj*, obj*);
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1(obj*);
extern obj* l_lean_parser_term_binders_has__view;
extern obj* l_lean_parser_command_reserve__mixfix_has__view;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5___boxed(obj*, obj*, obj*);
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__2;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15___boxed(obj*, obj*, obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12___boxed(obj*, obj*);
obj* l_lean_expander_sorry_transform(obj*, obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___boxed(obj*, obj*);
obj* l_lean_expander_arrow_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder___boxed(obj*);
obj* l_lean_expander_coe__ident__ident__univs___boxed(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__3;
obj* l_list_map___main___at_lean_expander_paren_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__ident__binder__id(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view_x_27;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder___closed__2;
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___boxed(obj*);
obj* l_lean_expander_glob__id(obj*);
obj* l_lean_expander_mk__simple__binder(obj*, uint8, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_expander_mixfix_transform___boxed(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__5;
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mk__scope(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__6;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8, obj*, obj*);
extern obj* l_lean_parser_term_bracketed__binders_has__view;
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(obj*, obj*, obj*);
obj* l_lean_expander_level_leading_transform___boxed(obj*, obj*);
obj* l_lean_expander_lambda_transform___closed__1;
extern obj* l_lean_parser_term_pi;
extern obj* l_lean_parser_term_paren_has__view;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
extern obj* l_lean_parser_term__parser__m_lean_parser_monad__parsec;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8, obj*, obj*);
obj* l_lean_expander_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_term__parser__m_monad;
extern obj* l_lean_parser_term_let_has__view;
obj* l_lean_expander_transform__m_monad__reader;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_expander_mk__simple__binder___closed__2;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_pi_transform(obj*, obj*);
obj* l_lean_expander_transformer;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_expander_2__expand__core(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__1;
obj* l_lean_expander_subtype_transform(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_expander_2__expand__core___main___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4(obj*, obj*, obj*, obj*);
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___boxed(obj*);
obj* l_lean_expander_mixfix_transform___closed__4;
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
obj* l_lean_expander_lambda_transform(obj*, obj*);
obj* l_lean_expander_declaration_transform(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_arrow_transform___closed__2;
obj* l_lean_expander_no__expansion(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___boxed(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__2;
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_expander_binder__ident__to__ident(obj*);
obj* l_lean_expander_coe__simple__binder__binders___boxed(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main(obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_expander_declaration_transform___closed__3;
obj* l_lean_expander_error___boxed(obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_lean_expander_expander__config_has__lift(obj*);
obj* l_lean_expander_lambda_transform___boxed(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1(obj*);
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj*, obj*);
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj*, obj*);
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_subtype_transform___boxed(obj*, obj*);
obj* l_lean_expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1___boxed(obj*, obj*);
obj* l_lean_expander_mk__simple__binder___closed__6;
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj*);
obj* l_lean_expander_reserve__mixfix_transform___boxed(obj*, obj*);
extern obj* l_lean_parser_term_assume_has__view;
extern obj* l_lean_parser_command_intro__rule;
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9___boxed(obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main___closed__1;
obj* l_lean_expander_transform__m_monad__except;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__3;
extern obj* l_lean_parser_term_paren;
obj* l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2(obj*, obj*);
obj* l_lean_expander_transformer__config__coe__frontend__config___boxed(obj*);
extern obj* l_lean_parser_term_hole_has__view;
obj* l_lean_expander_error(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
obj* l_lean_expander_coe__binder__bracketed__binder___closed__1;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_expander_error___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__1;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___boxed(obj*);
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2___boxed(obj*, obj*);
obj* l_lean_expander_coe__binders__ext__binders(obj*);
obj* l_lean_expander_mixfix_transform(obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__1;
obj* l_lean_expander_coe__binders__ext__binders___boxed(obj*);
obj* l_lean_expander_paren_transform___closed__1;
obj* l_lean_expander_pi_transform___lambda__1___boxed(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18___boxed(obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_expander_coe__ident__ident__univs(obj*);
obj* l_lean_expander_get__opt__type___boxed(obj*);
obj* l_lean_expander_paren_transform(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj*, obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main___boxed(obj*);
obj* l_lean_expander_transformer__config__coe__frontend__config(obj*);
obj* l_lean_expander_expand__bracketed__binder___main(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1(obj*);
obj* l_lean_expander_coe__ident__binder__id___boxed(obj*);
obj* l_string_trim(obj*);
obj* l_lean_expander_variable_transform___closed__1;
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(obj*, obj*);
obj* l_lean_expander_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_transform__m;
extern obj* l_lean_parser_command_constant;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7___boxed(obj*, obj*, obj*);
obj* l_lean_expander_paren_transform___closed__2;
extern obj* l_lean_parser_term_if;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_term_assume;
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__6;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(uint8, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
obj* l_lean_expander_mixfix_transform___closed__5;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22___boxed(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
extern obj* l_lean_parser_command_declaration_has__view;
obj* l___private_init_lean_expander_2__expand__core___main(obj*, obj*, obj*, obj*);
obj* l_lean_expander_assume_transform(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(obj*, obj*);
obj* l_list_map___main___at_lean_expander_constant_transform___spec__1(obj*);
obj* l_lean_expander_mk__simple__binder___closed__1;
extern obj* l_lean_parser_command_notation__spec_precedence_has__view;
obj* l_lean_expander_variable_transform(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__5;
obj* l_id_bind___boxed(obj*, obj*);
obj* l_lean_expander_expand__binders(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mk__scope___boxed(obj*, obj*);
obj* l_lean_expander_mk__simple__binder___closed__5;
obj* l_lean_expander_mk__notation__transformer___boxed(obj*, obj*, obj*);
obj* l_lean_expander_expander__state_new;
extern obj* l_lean_parser_term_anonymous__constructor_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_term_subtype_has__view;
extern obj* l_lean_parser_term_binder__default_has__view;
extern obj* l_lean_parser_command_mixfix;
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_lambda;
extern obj* l_lean_parser_term_arrow;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_expander_get__opt__type(obj*);
obj* l_lean_expander_variables_transform___boxed(obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform(obj*, obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
obj* l_lean_expander_level_leading_transform(obj*, obj*);
obj* l_lean_expander_coe__binders__ext___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_expander_binding__annotation__update_parser_lean_parser_has__view;
obj* l_lean_expander_expander__m;
obj* l_lean_file__map_to__position(obj*, obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj*, obj*, obj*);
obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_lean_expander_constant_transform___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__4;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder(obj*);
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_expander_no__expansion___closed__1;
obj* l_lean_expander_bracketed__binders_transform___boxed(obj*, obj*);
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
extern obj* l_lean_parser_term__parser__m_monad__except;
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1(obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6___boxed(obj*, obj*);
obj* l_lean_expander_pi_transform___boxed(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_mk__simple__binder___closed__3;
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_let_transform(obj*, obj*);
extern obj* l_lean_parser_term_let;
obj* l_lean_expander_expand__bracketed__binder___main___closed__7;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(obj*, obj*);
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
obj* l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(obj*, obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1(obj*, obj*);
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2___boxed(obj*);
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_expander_constant_transform(obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___boxed(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
extern obj* l_lean_parser_term__parser__m_alternative;
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_expander_transformer__config__coe__frontend__config(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_expander_transformer__config__coe__frontend__config___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_transformer__config__coe__frontend__config(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_transform__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
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
x_10 = l_except__t_monad___rarg(x_9);
x_11 = l_reader__t_monad___rarg(x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
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
x_10 = l_except__t_monad___rarg(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
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
x_10 = l_except__t_monad__except___rarg(x_9);
x_11 = l_reader__t_monad__except___rarg(x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_expander_transformer() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_expander_no__expansion___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_no__expansion(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_no__expansion___closed__1;
return x_1;
}
}
obj* l_lean_expander_no__expansion___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_no__expansion(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_21; uint8 x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_1, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_lean_parser_syntax_get__pos(x_2);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_option_get__or__else___main___rarg(x_14, x_15);
lean::dec(x_14);
x_18 = l_lean_file__map_to__position(x_11, x_16);
lean::dec(x_16);
lean::dec(x_11);
x_21 = lean::box(0);
x_22 = 2;
x_23 = l_string_join___closed__1;
lean::inc(x_3);
x_25 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_18);
lean::cnstr_set(x_25, 2, x_21);
lean::cnstr_set(x_25, 3, x_23);
lean::cnstr_set(x_25, 4, x_3);
lean::cnstr_set_scalar(x_25, sizeof(void*)*5, x_22);
x_26 = x_25;
x_27 = lean::apply_2(x_5, lean::box(0), x_26);
return x_27;
}
}
obj* l_lean_expander_error___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_10, 0, x_3);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_5);
lean::closure_set(x_10, 3, x_6);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_1, x_10);
return x_11;
}
}
obj* l_lean_expander_error(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_lean_expander_error___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_expander_error___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_expander_error___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_expander_error___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_lean_expander_error___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_error(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_coe__name__ident(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
x_4 = l_lean_name_to__string__with__sep___main(x_2, x_0);
x_5 = l_lean_parser_substring_of__string(x_4);
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
obj* l_lean_expander_glob__id(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
x_8 = l_lean_name_to__string__with__sep___main(x_6, x_0);
x_9 = l_lean_parser_substring_of__string(x_8);
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
obj* l_lean_expander_coe__ident__ident__univs(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::box(0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_lean_expander_coe__ident__ident__univs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__ident__ident__univs(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_coe__ident__binder__id(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* l_lean_expander_coe__ident__binder__id___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__ident__binder__id(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg), 2, 0);
return x_1;
}
}
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(obj* x_0, obj* x_1) {
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
x_11 = l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(x_0, x_6);
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
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_expander_coe__binders__ext___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_lean_expander_coe__binders__ext(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_coe__binders__ext___rarg), 2, 0);
return x_1;
}
}
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_coe___at_lean_expander_coe__binders__ext___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_map___main___at_lean_expander_coe__binders__ext___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_coe__binders__ext___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__binders__ext(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_coe__binders__ext__binders(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* l_lean_expander_coe__binders__ext__binders___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__binders__ext__binders(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_coe__simple__binder__binders(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* l_lean_expander_coe__simple__binder__binders___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__simple__binder__binders(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_coe__binder__bracketed__binder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("(");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_coe__binder__bracketed__binder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(")");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_coe__binder__bracketed__binder(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_3);
x_6 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_7 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
obj* l_lean_expander_coe__binder__bracketed__binder___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_coe__binder__bracketed__binder(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; uint8 x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = l_lean_parser_syntax_get__pos(x_0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_option_get__or__else___main___rarg(x_6, x_7);
lean::dec(x_6);
x_10 = l_lean_file__map_to__position(x_5, x_8);
lean::dec(x_8);
x_12 = lean::box(0);
x_13 = 2;
x_14 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_4);
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_10);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_14);
lean::cnstr_set(x_17, 4, x_1);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_13);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* _init_l___private_init_lean_expander_1__pop__stx__arg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mk_notation_transformer: unreachable");
return x_0;
}
}
obj* l___private_init_lean_expander_1__pop__stx__arg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_5 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_3, x_4, x_0, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_15; obj* x_17; obj* x_18; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_8 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 2);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_7);
lean::inc(x_8);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_9);
lean::cnstr_set(x_15, 3, x_10);
lean::inc(x_6);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_expander_1__pop__stx__arg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_expander_1__pop__stx__arg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; uint8 x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 2);
x_5 = l_lean_parser_syntax_get__pos(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_option_get__or__else___main___rarg(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_file__map_to__position(x_4, x_7);
lean::dec(x_7);
x_11 = lean::box(0);
x_12 = 2;
x_13 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_16 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_9);
lean::cnstr_set(x_16, 2, x_11);
lean::cnstr_set(x_16, 3, x_13);
lean::cnstr_set(x_16, 4, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*5, x_12);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_4);
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
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mk_notation_transformer: unimplemented");
return x_0;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2() {
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
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(",");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_11 = x_1;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_1);
 x_11 = lean::box(0);
}
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
lean::dec(x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_22; 
x_21 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_22 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_21, x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
 lean::dec(x_22);
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
obj* x_31; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_12 = x_31;
goto lbl_13;
}
}
else
{
obj* x_36; 
lean::dec(x_11);
lean::dec(x_18);
x_36 = l___private_init_lean_expander_1__pop__stx__arg(x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_7);
lean::dec(x_9);
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
obj* x_44; 
x_44 = lean::cnstr_get(x_36, 0);
lean::inc(x_44);
lean::dec(x_36);
x_14 = x_44;
goto lbl_15;
}
}
lbl_13:
{
obj* x_47; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
if (lean::obj_tag(x_47) == 0)
{
obj* x_51; 
lean::dec(x_11);
x_51 = lean::cnstr_get(x_12, 1);
lean::inc(x_51);
lean::dec(x_12);
x_1 = x_9;
x_2 = x_51;
goto _start;
}
else
{
obj* x_55; obj* x_57; 
x_55 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 x_57 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
switch (lean::obj_tag(x_55)) {
case 0:
{
obj* x_59; obj* x_62; 
lean::dec(x_55);
x_59 = lean::cnstr_get(x_12, 1);
lean::inc(x_59);
lean::dec(x_12);
x_62 = l___private_init_lean_expander_1__pop__stx__arg(x_59, x_3);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_57);
x_67 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_67);
 lean::dec(x_62);
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
obj* x_71; obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_71 = lean::cnstr_get(x_62, 0);
lean::inc(x_71);
lean::dec(x_62);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
lean::dec(x_71);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_76, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_76, 2);
lean::inc(x_83);
lean::dec(x_76);
x_86 = l_lean_parser_term_binder__ident_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_90 = lean::apply_1(x_87, x_74);
x_91 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_92 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_92 = x_11;
}
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::box(0);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_57)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_57;
}
lean::cnstr_set(x_96, 0, x_95);
x_97 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_97, 0, x_79);
lean::cnstr_set(x_97, 1, x_81);
lean::cnstr_set(x_97, 2, x_83);
lean::cnstr_set(x_97, 3, x_96);
x_1 = x_9;
x_2 = x_97;
goto _start;
}
}
case 1:
{
obj* x_101; obj* x_104; 
lean::dec(x_11);
lean::dec(x_55);
x_101 = lean::cnstr_get(x_12, 1);
lean::inc(x_101);
lean::dec(x_12);
x_104 = l___private_init_lean_expander_1__pop__stx__arg(x_101, x_3);
lean::dec(x_101);
if (lean::obj_tag(x_104) == 0)
{
obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_9);
lean::dec(x_57);
x_108 = lean::cnstr_get(x_104, 0);
if (lean::is_exclusive(x_104)) {
 x_110 = x_104;
} else {
 lean::inc(x_108);
 lean::dec(x_104);
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
obj* x_112; obj* x_115; obj* x_117; obj* x_120; obj* x_122; obj* x_124; obj* x_127; obj* x_128; obj* x_131; obj* x_132; obj* x_133; 
x_112 = lean::cnstr_get(x_104, 0);
lean::inc(x_112);
lean::dec(x_104);
x_115 = lean::cnstr_get(x_112, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
lean::dec(x_112);
x_120 = lean::cnstr_get(x_117, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_117, 2);
lean::inc(x_124);
lean::dec(x_117);
x_127 = l_lean_parser_term_binders_has__view;
x_128 = lean::cnstr_get(x_127, 0);
lean::inc(x_128);
lean::dec(x_127);
x_131 = lean::apply_1(x_128, x_115);
if (lean::is_scalar(x_57)) {
 x_132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_132 = x_57;
}
lean::cnstr_set(x_132, 0, x_131);
x_133 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_133, 0, x_120);
lean::cnstr_set(x_133, 1, x_122);
lean::cnstr_set(x_133, 2, x_124);
lean::cnstr_set(x_133, 3, x_132);
x_1 = x_9;
x_2 = x_133;
goto _start;
}
}
default:
{
obj* x_136; obj* x_139; 
lean::dec(x_57);
x_136 = lean::cnstr_get(x_55, 0);
lean::inc(x_136);
lean::dec(x_55);
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_141; obj* x_144; obj* x_147; 
x_141 = lean::cnstr_get(x_12, 1);
lean::inc(x_141);
lean::dec(x_12);
x_144 = lean::cnstr_get(x_136, 0);
lean::inc(x_144);
lean::dec(x_136);
x_147 = l___private_init_lean_expander_1__pop__stx__arg(x_141, x_3);
lean::dec(x_141);
if (lean::obj_tag(x_147) == 0)
{
obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_144);
x_152 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_154 = x_147;
} else {
 lean::inc(x_152);
 lean::dec(x_147);
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
obj* x_156; obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_169; obj* x_171; obj* x_172; obj* x_175; 
x_156 = lean::cnstr_get(x_147, 0);
lean::inc(x_156);
lean::dec(x_147);
x_159 = lean::cnstr_get(x_156, 0);
x_161 = lean::cnstr_get(x_156, 1);
if (lean::is_exclusive(x_156)) {
 x_163 = x_156;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_156);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_161, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_161, 1);
lean::inc(x_166);
if (lean::is_scalar(x_163)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_163;
}
lean::cnstr_set(x_168, 0, x_144);
lean::cnstr_set(x_168, 1, x_159);
x_169 = lean::cnstr_get(x_161, 2);
lean::inc(x_169);
if (lean::is_scalar(x_11)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_11;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
x_172 = lean::cnstr_get(x_161, 3);
lean::inc(x_172);
lean::dec(x_161);
x_175 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_175, 0, x_164);
lean::cnstr_set(x_175, 1, x_166);
lean::cnstr_set(x_175, 2, x_171);
lean::cnstr_set(x_175, 3, x_172);
x_1 = x_9;
x_2 = x_175;
goto _start;
}
}
else
{
obj* x_177; obj* x_180; 
x_177 = lean::cnstr_get(x_139, 0);
lean::inc(x_177);
lean::dec(x_139);
x_180 = lean::cnstr_get(x_177, 1);
lean::inc(x_180);
lean::dec(x_177);
switch (lean::obj_tag(x_180)) {
case 0:
{
obj* x_184; obj* x_187; obj* x_190; 
lean::dec(x_180);
x_184 = lean::cnstr_get(x_12, 1);
lean::inc(x_184);
lean::dec(x_12);
x_187 = lean::cnstr_get(x_136, 0);
lean::inc(x_187);
lean::dec(x_136);
x_190 = l___private_init_lean_expander_1__pop__stx__arg(x_184, x_3);
lean::dec(x_184);
if (lean::obj_tag(x_190) == 0)
{
obj* x_195; obj* x_197; obj* x_198; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_187);
x_195 = lean::cnstr_get(x_190, 0);
if (lean::is_exclusive(x_190)) {
 x_197 = x_190;
} else {
 lean::inc(x_195);
 lean::dec(x_190);
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
obj* x_199; obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_209; obj* x_211; obj* x_212; obj* x_214; obj* x_215; obj* x_218; 
x_199 = lean::cnstr_get(x_190, 0);
lean::inc(x_199);
lean::dec(x_190);
x_202 = lean::cnstr_get(x_199, 0);
x_204 = lean::cnstr_get(x_199, 1);
if (lean::is_exclusive(x_199)) {
 x_206 = x_199;
} else {
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_199);
 x_206 = lean::box(0);
}
x_207 = lean::cnstr_get(x_204, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_204, 1);
lean::inc(x_209);
if (lean::is_scalar(x_206)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_206;
}
lean::cnstr_set(x_211, 0, x_187);
lean::cnstr_set(x_211, 1, x_202);
x_212 = lean::cnstr_get(x_204, 2);
lean::inc(x_212);
if (lean::is_scalar(x_11)) {
 x_214 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_214 = x_11;
}
lean::cnstr_set(x_214, 0, x_211);
lean::cnstr_set(x_214, 1, x_212);
x_215 = lean::cnstr_get(x_204, 3);
lean::inc(x_215);
lean::dec(x_204);
x_218 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_218, 0, x_207);
lean::cnstr_set(x_218, 1, x_209);
lean::cnstr_set(x_218, 2, x_214);
lean::cnstr_set(x_218, 3, x_215);
x_1 = x_9;
x_2 = x_218;
goto _start;
}
}
case 2:
{
obj* x_220; obj* x_223; obj* x_226; obj* x_229; 
x_220 = lean::cnstr_get(x_12, 1);
lean::inc(x_220);
lean::dec(x_12);
x_223 = lean::cnstr_get(x_136, 0);
lean::inc(x_223);
lean::dec(x_136);
x_226 = lean::cnstr_get(x_180, 0);
lean::inc(x_226);
lean::dec(x_180);
x_229 = l___private_init_lean_expander_1__pop__stx__arg(x_220, x_3);
lean::dec(x_220);
if (lean::obj_tag(x_229) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_226);
lean::dec(x_223);
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
obj* x_239; obj* x_242; obj* x_244; 
x_239 = lean::cnstr_get(x_229, 0);
lean::inc(x_239);
lean::dec(x_229);
x_242 = lean::cnstr_get(x_239, 1);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_242, 3);
lean::inc(x_244);
if (lean::obj_tag(x_244) == 0)
{
obj* x_250; obj* x_251; 
lean::dec(x_11);
lean::dec(x_226);
lean::dec(x_223);
lean::dec(x_239);
x_250 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_251 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_250, x_242, x_3);
lean::dec(x_242);
if (lean::obj_tag(x_251) == 0)
{
obj* x_254; obj* x_256; obj* x_257; 
lean::dec(x_9);
x_254 = lean::cnstr_get(x_251, 0);
if (lean::is_exclusive(x_251)) {
 x_256 = x_251;
} else {
 lean::inc(x_254);
 lean::dec(x_251);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_254);
return x_257;
}
else
{
obj* x_258; obj* x_261; 
x_258 = lean::cnstr_get(x_251, 0);
lean::inc(x_258);
lean::dec(x_251);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
lean::dec(x_258);
x_1 = x_9;
x_2 = x_261;
goto _start;
}
}
else
{
obj* x_265; obj* x_267; obj* x_268; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; obj* x_278; obj* x_281; obj* x_282; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_292; obj* x_293; obj* x_294; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; 
x_265 = lean::cnstr_get(x_239, 0);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 1);
 x_267 = x_239;
} else {
 lean::inc(x_265);
 lean::dec(x_239);
 x_267 = lean::box(0);
}
x_268 = lean::cnstr_get(x_242, 0);
x_270 = lean::cnstr_get(x_242, 1);
x_272 = lean::cnstr_get(x_242, 2);
if (lean::is_exclusive(x_242)) {
 lean::cnstr_release(x_242, 3);
 x_274 = x_242;
} else {
 lean::inc(x_268);
 lean::inc(x_270);
 lean::inc(x_272);
 lean::dec(x_242);
 x_274 = lean::box(0);
}
x_275 = lean::cnstr_get(x_244, 0);
lean::inc(x_275);
x_277 = l_lean_parser_term_lambda_has__view;
x_278 = lean::cnstr_get(x_277, 1);
lean::inc(x_278);
lean::dec(x_277);
x_281 = lean::box(0);
x_282 = lean::cnstr_get(x_226, 3);
lean::inc(x_282);
x_284 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_285 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_285 = x_11;
}
lean::cnstr_set(x_285, 0, x_282);
lean::cnstr_set(x_285, 1, x_284);
x_286 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_285);
x_287 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_281);
x_288 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_288, 0, x_287);
x_289 = lean::cnstr_get(x_226, 5);
lean::inc(x_289);
lean::dec(x_226);
x_292 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_293 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_294 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_294, 0, x_292);
lean::cnstr_set(x_294, 1, x_288);
lean::cnstr_set(x_294, 2, x_293);
lean::cnstr_set(x_294, 3, x_289);
lean::inc(x_278);
x_296 = lean::apply_1(x_278, x_294);
x_297 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_297, 0, x_292);
lean::cnstr_set(x_297, 1, x_275);
lean::cnstr_set(x_297, 2, x_293);
lean::cnstr_set(x_297, 3, x_265);
x_298 = lean::apply_1(x_278, x_297);
x_299 = l_lean_parser_term_app_has__view;
x_300 = lean::cnstr_get(x_299, 1);
lean::inc(x_300);
lean::dec(x_299);
x_303 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_303, 0, x_296);
lean::cnstr_set(x_303, 1, x_298);
x_304 = lean::apply_1(x_300, x_303);
if (lean::is_scalar(x_267)) {
 x_305 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_305 = x_267;
}
lean::cnstr_set(x_305, 0, x_223);
lean::cnstr_set(x_305, 1, x_304);
x_306 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_306, 0, x_305);
lean::cnstr_set(x_306, 1, x_272);
if (lean::is_scalar(x_274)) {
 x_307 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_307 = x_274;
}
lean::cnstr_set(x_307, 0, x_268);
lean::cnstr_set(x_307, 1, x_270);
lean::cnstr_set(x_307, 2, x_306);
lean::cnstr_set(x_307, 3, x_244);
x_1 = x_9;
x_2 = x_307;
goto _start;
}
}
}
default:
{
obj* x_312; obj* x_315; obj* x_316; 
lean::dec(x_11);
lean::dec(x_136);
lean::dec(x_180);
x_312 = lean::cnstr_get(x_12, 1);
lean::inc(x_312);
lean::dec(x_12);
x_315 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
x_316 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_315, x_312, x_3);
lean::dec(x_312);
if (lean::obj_tag(x_316) == 0)
{
obj* x_319; obj* x_321; obj* x_322; 
lean::dec(x_9);
x_319 = lean::cnstr_get(x_316, 0);
if (lean::is_exclusive(x_316)) {
 x_321 = x_316;
} else {
 lean::inc(x_319);
 lean::dec(x_316);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_319);
return x_322;
}
else
{
obj* x_323; obj* x_326; 
x_323 = lean::cnstr_get(x_316, 0);
lean::inc(x_323);
lean::dec(x_316);
x_326 = lean::cnstr_get(x_323, 1);
lean::inc(x_326);
lean::dec(x_323);
x_1 = x_9;
x_2 = x_326;
goto _start;
}
}
}
}
}
}
}
}
lbl_15:
{
obj* x_330; 
x_330 = lean::cnstr_get(x_7, 1);
lean::inc(x_330);
lean::dec(x_7);
if (lean::obj_tag(x_330) == 0)
{
obj* x_333; 
x_333 = lean::cnstr_get(x_14, 1);
lean::inc(x_333);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_333;
goto _start;
}
else
{
obj* x_337; obj* x_339; 
x_337 = lean::cnstr_get(x_330, 0);
if (lean::is_exclusive(x_330)) {
 lean::cnstr_set(x_330, 0, lean::box(0));
 x_339 = x_330;
} else {
 lean::inc(x_337);
 lean::dec(x_330);
 x_339 = lean::box(0);
}
switch (lean::obj_tag(x_337)) {
case 0:
{
obj* x_341; obj* x_344; 
lean::dec(x_337);
x_341 = lean::cnstr_get(x_14, 1);
lean::inc(x_341);
lean::dec(x_14);
x_344 = l___private_init_lean_expander_1__pop__stx__arg(x_341, x_3);
lean::dec(x_341);
if (lean::obj_tag(x_344) == 0)
{
obj* x_348; obj* x_350; obj* x_351; 
lean::dec(x_9);
lean::dec(x_339);
x_348 = lean::cnstr_get(x_344, 0);
if (lean::is_exclusive(x_344)) {
 x_350 = x_344;
} else {
 lean::inc(x_348);
 lean::dec(x_344);
 x_350 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_348);
return x_351;
}
else
{
obj* x_352; obj* x_355; obj* x_357; obj* x_360; obj* x_362; obj* x_364; obj* x_367; obj* x_368; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; 
x_352 = lean::cnstr_get(x_344, 0);
lean::inc(x_352);
lean::dec(x_344);
x_355 = lean::cnstr_get(x_352, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_352, 1);
lean::inc(x_357);
lean::dec(x_352);
x_360 = lean::cnstr_get(x_357, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_357, 1);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_357, 2);
lean::inc(x_364);
lean::dec(x_357);
x_367 = l_lean_parser_term_binder__ident_has__view;
x_368 = lean::cnstr_get(x_367, 0);
lean::inc(x_368);
lean::dec(x_367);
x_371 = lean::apply_1(x_368, x_355);
x_372 = lean::box(0);
x_373 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_373, 0, x_371);
lean::cnstr_set(x_373, 1, x_372);
x_374 = lean::box(0);
x_375 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_375, 0, x_373);
lean::cnstr_set(x_375, 1, x_374);
x_376 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_376, 0, x_375);
if (lean::is_scalar(x_339)) {
 x_377 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_377 = x_339;
}
lean::cnstr_set(x_377, 0, x_376);
x_378 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_378, 0, x_360);
lean::cnstr_set(x_378, 1, x_362);
lean::cnstr_set(x_378, 2, x_364);
lean::cnstr_set(x_378, 3, x_377);
x_1 = x_9;
x_2 = x_378;
goto _start;
}
}
case 1:
{
obj* x_381; obj* x_384; 
lean::dec(x_337);
x_381 = lean::cnstr_get(x_14, 1);
lean::inc(x_381);
lean::dec(x_14);
x_384 = l___private_init_lean_expander_1__pop__stx__arg(x_381, x_3);
lean::dec(x_381);
if (lean::obj_tag(x_384) == 0)
{
obj* x_388; obj* x_390; obj* x_391; 
lean::dec(x_9);
lean::dec(x_339);
x_388 = lean::cnstr_get(x_384, 0);
if (lean::is_exclusive(x_384)) {
 x_390 = x_384;
} else {
 lean::inc(x_388);
 lean::dec(x_384);
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
obj* x_392; obj* x_395; obj* x_397; obj* x_400; obj* x_402; obj* x_404; obj* x_407; obj* x_408; obj* x_411; obj* x_412; obj* x_413; 
x_392 = lean::cnstr_get(x_384, 0);
lean::inc(x_392);
lean::dec(x_384);
x_395 = lean::cnstr_get(x_392, 0);
lean::inc(x_395);
x_397 = lean::cnstr_get(x_392, 1);
lean::inc(x_397);
lean::dec(x_392);
x_400 = lean::cnstr_get(x_397, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_397, 1);
lean::inc(x_402);
x_404 = lean::cnstr_get(x_397, 2);
lean::inc(x_404);
lean::dec(x_397);
x_407 = l_lean_parser_term_binders_has__view;
x_408 = lean::cnstr_get(x_407, 0);
lean::inc(x_408);
lean::dec(x_407);
x_411 = lean::apply_1(x_408, x_395);
if (lean::is_scalar(x_339)) {
 x_412 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_412 = x_339;
}
lean::cnstr_set(x_412, 0, x_411);
x_413 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_413, 0, x_400);
lean::cnstr_set(x_413, 1, x_402);
lean::cnstr_set(x_413, 2, x_404);
lean::cnstr_set(x_413, 3, x_412);
x_1 = x_9;
x_2 = x_413;
goto _start;
}
}
default:
{
obj* x_416; obj* x_419; 
lean::dec(x_339);
x_416 = lean::cnstr_get(x_337, 0);
lean::inc(x_416);
lean::dec(x_337);
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
if (lean::obj_tag(x_419) == 0)
{
obj* x_421; obj* x_424; obj* x_427; 
x_421 = lean::cnstr_get(x_14, 1);
lean::inc(x_421);
lean::dec(x_14);
x_424 = lean::cnstr_get(x_416, 0);
lean::inc(x_424);
lean::dec(x_416);
x_427 = l___private_init_lean_expander_1__pop__stx__arg(x_421, x_3);
lean::dec(x_421);
if (lean::obj_tag(x_427) == 0)
{
obj* x_431; obj* x_433; obj* x_434; 
lean::dec(x_424);
lean::dec(x_9);
x_431 = lean::cnstr_get(x_427, 0);
if (lean::is_exclusive(x_427)) {
 x_433 = x_427;
} else {
 lean::inc(x_431);
 lean::dec(x_427);
 x_433 = lean::box(0);
}
if (lean::is_scalar(x_433)) {
 x_434 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_434 = x_433;
}
lean::cnstr_set(x_434, 0, x_431);
return x_434;
}
else
{
obj* x_435; obj* x_438; obj* x_440; obj* x_442; obj* x_443; obj* x_445; obj* x_447; obj* x_448; obj* x_450; obj* x_451; obj* x_454; 
x_435 = lean::cnstr_get(x_427, 0);
lean::inc(x_435);
lean::dec(x_427);
x_438 = lean::cnstr_get(x_435, 0);
x_440 = lean::cnstr_get(x_435, 1);
if (lean::is_exclusive(x_435)) {
 x_442 = x_435;
} else {
 lean::inc(x_438);
 lean::inc(x_440);
 lean::dec(x_435);
 x_442 = lean::box(0);
}
x_443 = lean::cnstr_get(x_440, 0);
lean::inc(x_443);
x_445 = lean::cnstr_get(x_440, 1);
lean::inc(x_445);
if (lean::is_scalar(x_442)) {
 x_447 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_447 = x_442;
}
lean::cnstr_set(x_447, 0, x_424);
lean::cnstr_set(x_447, 1, x_438);
x_448 = lean::cnstr_get(x_440, 2);
lean::inc(x_448);
x_450 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_450, 0, x_447);
lean::cnstr_set(x_450, 1, x_448);
x_451 = lean::cnstr_get(x_440, 3);
lean::inc(x_451);
lean::dec(x_440);
x_454 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_454, 0, x_443);
lean::cnstr_set(x_454, 1, x_445);
lean::cnstr_set(x_454, 2, x_450);
lean::cnstr_set(x_454, 3, x_451);
x_1 = x_9;
x_2 = x_454;
goto _start;
}
}
else
{
obj* x_456; obj* x_459; 
x_456 = lean::cnstr_get(x_419, 0);
lean::inc(x_456);
lean::dec(x_419);
x_459 = lean::cnstr_get(x_456, 1);
lean::inc(x_459);
lean::dec(x_456);
switch (lean::obj_tag(x_459)) {
case 0:
{
obj* x_463; obj* x_466; obj* x_469; 
lean::dec(x_459);
x_463 = lean::cnstr_get(x_14, 1);
lean::inc(x_463);
lean::dec(x_14);
x_466 = lean::cnstr_get(x_416, 0);
lean::inc(x_466);
lean::dec(x_416);
x_469 = l___private_init_lean_expander_1__pop__stx__arg(x_463, x_3);
lean::dec(x_463);
if (lean::obj_tag(x_469) == 0)
{
obj* x_473; obj* x_475; obj* x_476; 
lean::dec(x_466);
lean::dec(x_9);
x_473 = lean::cnstr_get(x_469, 0);
if (lean::is_exclusive(x_469)) {
 x_475 = x_469;
} else {
 lean::inc(x_473);
 lean::dec(x_469);
 x_475 = lean::box(0);
}
if (lean::is_scalar(x_475)) {
 x_476 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_476 = x_475;
}
lean::cnstr_set(x_476, 0, x_473);
return x_476;
}
else
{
obj* x_477; obj* x_480; obj* x_482; obj* x_484; obj* x_485; obj* x_487; obj* x_489; obj* x_490; obj* x_492; obj* x_493; obj* x_496; 
x_477 = lean::cnstr_get(x_469, 0);
lean::inc(x_477);
lean::dec(x_469);
x_480 = lean::cnstr_get(x_477, 0);
x_482 = lean::cnstr_get(x_477, 1);
if (lean::is_exclusive(x_477)) {
 x_484 = x_477;
} else {
 lean::inc(x_480);
 lean::inc(x_482);
 lean::dec(x_477);
 x_484 = lean::box(0);
}
x_485 = lean::cnstr_get(x_482, 0);
lean::inc(x_485);
x_487 = lean::cnstr_get(x_482, 1);
lean::inc(x_487);
if (lean::is_scalar(x_484)) {
 x_489 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_489 = x_484;
}
lean::cnstr_set(x_489, 0, x_466);
lean::cnstr_set(x_489, 1, x_480);
x_490 = lean::cnstr_get(x_482, 2);
lean::inc(x_490);
x_492 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_492, 0, x_489);
lean::cnstr_set(x_492, 1, x_490);
x_493 = lean::cnstr_get(x_482, 3);
lean::inc(x_493);
lean::dec(x_482);
x_496 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_496, 0, x_485);
lean::cnstr_set(x_496, 1, x_487);
lean::cnstr_set(x_496, 2, x_492);
lean::cnstr_set(x_496, 3, x_493);
x_1 = x_9;
x_2 = x_496;
goto _start;
}
}
case 2:
{
obj* x_498; obj* x_501; obj* x_504; obj* x_507; 
x_498 = lean::cnstr_get(x_14, 1);
lean::inc(x_498);
lean::dec(x_14);
x_501 = lean::cnstr_get(x_416, 0);
lean::inc(x_501);
lean::dec(x_416);
x_504 = lean::cnstr_get(x_459, 0);
lean::inc(x_504);
lean::dec(x_459);
x_507 = l___private_init_lean_expander_1__pop__stx__arg(x_498, x_3);
lean::dec(x_498);
if (lean::obj_tag(x_507) == 0)
{
obj* x_512; obj* x_514; obj* x_515; 
lean::dec(x_501);
lean::dec(x_504);
lean::dec(x_9);
x_512 = lean::cnstr_get(x_507, 0);
if (lean::is_exclusive(x_507)) {
 x_514 = x_507;
} else {
 lean::inc(x_512);
 lean::dec(x_507);
 x_514 = lean::box(0);
}
if (lean::is_scalar(x_514)) {
 x_515 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_515 = x_514;
}
lean::cnstr_set(x_515, 0, x_512);
return x_515;
}
else
{
obj* x_516; obj* x_519; obj* x_521; 
x_516 = lean::cnstr_get(x_507, 0);
lean::inc(x_516);
lean::dec(x_507);
x_519 = lean::cnstr_get(x_516, 1);
lean::inc(x_519);
x_521 = lean::cnstr_get(x_519, 3);
lean::inc(x_521);
if (lean::obj_tag(x_521) == 0)
{
obj* x_526; obj* x_527; 
lean::dec(x_501);
lean::dec(x_504);
lean::dec(x_516);
x_526 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_527 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_526, x_519, x_3);
lean::dec(x_519);
if (lean::obj_tag(x_527) == 0)
{
obj* x_530; obj* x_532; obj* x_533; 
lean::dec(x_9);
x_530 = lean::cnstr_get(x_527, 0);
if (lean::is_exclusive(x_527)) {
 x_532 = x_527;
} else {
 lean::inc(x_530);
 lean::dec(x_527);
 x_532 = lean::box(0);
}
if (lean::is_scalar(x_532)) {
 x_533 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_533 = x_532;
}
lean::cnstr_set(x_533, 0, x_530);
return x_533;
}
else
{
obj* x_534; obj* x_537; 
x_534 = lean::cnstr_get(x_527, 0);
lean::inc(x_534);
lean::dec(x_527);
x_537 = lean::cnstr_get(x_534, 1);
lean::inc(x_537);
lean::dec(x_534);
x_1 = x_9;
x_2 = x_537;
goto _start;
}
}
else
{
obj* x_541; obj* x_543; obj* x_544; obj* x_546; obj* x_548; obj* x_550; obj* x_551; obj* x_553; obj* x_554; obj* x_557; obj* x_558; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_568; obj* x_569; obj* x_570; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; 
x_541 = lean::cnstr_get(x_516, 0);
if (lean::is_exclusive(x_516)) {
 lean::cnstr_release(x_516, 1);
 x_543 = x_516;
} else {
 lean::inc(x_541);
 lean::dec(x_516);
 x_543 = lean::box(0);
}
x_544 = lean::cnstr_get(x_519, 0);
x_546 = lean::cnstr_get(x_519, 1);
x_548 = lean::cnstr_get(x_519, 2);
if (lean::is_exclusive(x_519)) {
 lean::cnstr_release(x_519, 3);
 x_550 = x_519;
} else {
 lean::inc(x_544);
 lean::inc(x_546);
 lean::inc(x_548);
 lean::dec(x_519);
 x_550 = lean::box(0);
}
x_551 = lean::cnstr_get(x_521, 0);
lean::inc(x_551);
x_553 = l_lean_parser_term_lambda_has__view;
x_554 = lean::cnstr_get(x_553, 1);
lean::inc(x_554);
lean::dec(x_553);
x_557 = lean::box(0);
x_558 = lean::cnstr_get(x_504, 3);
lean::inc(x_558);
x_560 = lean::box(0);
x_561 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_561, 0, x_558);
lean::cnstr_set(x_561, 1, x_560);
x_562 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_561);
x_563 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_563, 0, x_562);
lean::cnstr_set(x_563, 1, x_557);
x_564 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_564, 0, x_563);
x_565 = lean::cnstr_get(x_504, 5);
lean::inc(x_565);
lean::dec(x_504);
x_568 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_569 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_570 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_570, 0, x_568);
lean::cnstr_set(x_570, 1, x_564);
lean::cnstr_set(x_570, 2, x_569);
lean::cnstr_set(x_570, 3, x_565);
lean::inc(x_554);
x_572 = lean::apply_1(x_554, x_570);
x_573 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_573, 0, x_568);
lean::cnstr_set(x_573, 1, x_551);
lean::cnstr_set(x_573, 2, x_569);
lean::cnstr_set(x_573, 3, x_541);
x_574 = lean::apply_1(x_554, x_573);
x_575 = l_lean_parser_term_app_has__view;
x_576 = lean::cnstr_get(x_575, 1);
lean::inc(x_576);
lean::dec(x_575);
x_579 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_579, 0, x_572);
lean::cnstr_set(x_579, 1, x_574);
x_580 = lean::apply_1(x_576, x_579);
if (lean::is_scalar(x_543)) {
 x_581 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_581 = x_543;
}
lean::cnstr_set(x_581, 0, x_501);
lean::cnstr_set(x_581, 1, x_580);
x_582 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_582, 0, x_581);
lean::cnstr_set(x_582, 1, x_548);
if (lean::is_scalar(x_550)) {
 x_583 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_583 = x_550;
}
lean::cnstr_set(x_583, 0, x_544);
lean::cnstr_set(x_583, 1, x_546);
lean::cnstr_set(x_583, 2, x_582);
lean::cnstr_set(x_583, 3, x_521);
x_1 = x_9;
x_2 = x_583;
goto _start;
}
}
}
default:
{
obj* x_587; obj* x_590; obj* x_591; 
lean::dec(x_416);
lean::dec(x_459);
x_587 = lean::cnstr_get(x_14, 1);
lean::inc(x_587);
lean::dec(x_14);
x_590 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
x_591 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_590, x_587, x_3);
lean::dec(x_587);
if (lean::obj_tag(x_591) == 0)
{
obj* x_594; obj* x_596; obj* x_597; 
lean::dec(x_9);
x_594 = lean::cnstr_get(x_591, 0);
if (lean::is_exclusive(x_591)) {
 x_596 = x_591;
} else {
 lean::inc(x_594);
 lean::dec(x_591);
 x_596 = lean::box(0);
}
if (lean::is_scalar(x_596)) {
 x_597 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_597 = x_596;
}
lean::cnstr_set(x_597, 0, x_594);
return x_597;
}
else
{
obj* x_598; obj* x_601; 
x_598 = lean::cnstr_get(x_591, 0);
lean::inc(x_598);
lean::dec(x_591);
x_601 = lean::cnstr_get(x_598, 1);
lean::inc(x_601);
lean::dec(x_598);
x_1 = x_9;
x_2 = x_601;
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
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
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
x_9 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_11 = x_2;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_4);
x_13 = lean::cnstr_get(x_7, 2);
lean::inc(x_13);
lean::dec(x_7);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_9);
if (lean::is_scalar(x_6)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_6;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
}
}
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_lean_parser_ident__univs;
x_2 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_lean_parser_ident__univs_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_0);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean_name_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_0 = x_4;
goto _start;
}
else
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
}
}
}
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_12; obj* x_15; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_12);
lean::dec(x_12);
return x_15;
}
else
{
obj* x_19; 
lean::dec(x_7);
lean::dec(x_4);
x_19 = lean::box(0);
return x_19;
}
}
}
}
obj* l_lean_expander_mk__notation__transformer(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_7 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_1, x_6, x_2);
lean::dec(x_1);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_22; obj* x_24; obj* x_26; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::box(0);
lean::inc(x_1);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_12);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_16);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_18);
x_26 = x_29;
goto lbl_27;
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
lean::dec(x_24);
x_33 = l___private_init_lean_expander_1__pop__stx__arg(x_18, x_2);
lean::dec(x_18);
if (lean::obj_tag(x_33) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_30);
lean::dec(x_19);
lean::dec(x_22);
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
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
obj* x_44; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_65; 
x_44 = lean::cnstr_get(x_33, 0);
lean::inc(x_44);
lean::dec(x_33);
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
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
if (lean::is_scalar(x_51)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_51;
}
lean::cnstr_set(x_56, 0, x_30);
lean::cnstr_set(x_56, 1, x_47);
x_57 = lean::cnstr_get(x_49, 2);
lean::inc(x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::cnstr_get(x_49, 3);
lean::inc(x_60);
lean::dec(x_49);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_52);
lean::cnstr_set(x_63, 1, x_54);
lean::cnstr_set(x_63, 2, x_59);
lean::cnstr_set(x_63, 3, x_60);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_63);
x_26 = x_65;
goto lbl_27;
}
}
lbl_27:
{
obj* x_66; obj* x_69; obj* x_72; 
x_66 = lean::cnstr_get(x_26, 1);
lean::inc(x_66);
lean::dec(x_26);
x_69 = lean::cnstr_get(x_22, 1);
lean::inc(x_69);
lean::dec(x_22);
x_72 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_69, x_66, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_72) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_11);
lean::dec(x_19);
x_76 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_78 = x_72;
} else {
 lean::inc(x_76);
 lean::dec(x_72);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
return x_79;
}
else
{
obj* x_80; obj* x_82; obj* x_83; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_94; obj* x_95; obj* x_96; 
x_80 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_82 = x_72;
} else {
 lean::inc(x_80);
 lean::dec(x_72);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_86);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1___boxed), 2, 1);
lean::closure_set(x_90, 0, x_89);
x_91 = lean::cnstr_get(x_19, 4);
lean::inc(x_91);
lean::dec(x_19);
x_94 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_90, x_91);
if (lean::is_scalar(x_11)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_11;
}
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_82)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_82;
}
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
}
}
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_coe___at_lean_expander_mk__notation__transformer___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_mk__notation__transformer___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_mk__notation__transformer___lambda__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_expander_mk__notation__transformer___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_mk__notation__transformer(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__1() {
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
x_7 = l_lean_name_to__string__with__sep___main(x_5, x_4);
lean::dec(x_5);
x_9 = l_lean_parser_substring_of__string(x_7);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_4);
lean::cnstr_set(x_10, 3, x_1);
lean::cnstr_set(x_10, 4, x_1);
return x_10;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__2___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("b");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid `infixr` declaration, given precedence must greater than zero");
return x_0;
}
}
obj* l_lean_expander_mixfix__to__notation__spec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_9 = lean::box(0);
x_10 = lean::box(0);
x_11 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_12 = l_option_map___rarg(x_11, x_5);
x_13 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_14 = l_option_map___rarg(x_13, x_12);
x_15 = l_lean_expander_mixfix__to__notation__spec___closed__5;
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_10);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
case 3:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_23; 
x_23 = lean::box(0);
x_3 = x_23;
goto lbl_4;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; uint8 x_31; 
x_24 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_29 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_27);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_24);
x_33 = lean::mk_nat_obj(1u);
x_34 = lean::nat_sub(x_29, x_33);
lean::dec(x_29);
x_36 = l_lean_parser_number_view_of__nat(x_34);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
if (lean::is_scalar(x_26)) {
 x_42 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_42 = x_26;
}
lean::cnstr_set(x_42, 0, x_41);
x_3 = x_42;
goto lbl_4;
}
else
{
obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_26);
lean::dec(x_29);
x_45 = l_lean_parser_command_notation__spec_precedence_has__view;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
lean::dec(x_45);
x_49 = lean::apply_1(x_46, x_24);
x_50 = l_lean_expander_mixfix__to__notation__spec___closed__6;
x_51 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_49, x_50, x_2);
lean::dec(x_49);
if (lean::obj_tag(x_51) == 0)
{
obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_1);
x_54 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_56 = x_51;
} else {
 lean::inc(x_54);
 lean::dec(x_51);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_51, 0);
lean::inc(x_58);
lean::dec(x_51);
x_3 = x_58;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_5);
x_62 = lean::box(0);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_1);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_63);
x_66 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_65);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
return x_68;
}
default:
{
obj* x_69; 
x_69 = lean::box(0);
x_7 = x_69;
goto lbl_8;
}
}
lbl_4:
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::box(0);
x_71 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_3);
x_73 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_1);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_70);
x_77 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
lbl_8:
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_7);
x_81 = lean::box(0);
x_82 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_83 = l_option_map___rarg(x_82, x_5);
x_84 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_85 = l_option_map___rarg(x_84, x_83);
x_86 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_85);
x_88 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_1);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_81);
x_92 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_mixfix__to__notation__spec___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_mixfix__to__notation__spec___lambda__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_mixfix__to__notation__spec(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::mk_string("a");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string(".");
lean::inc(x_7);
x_10 = l_lean_name_to__string__with__sep___main(x_8, x_7);
lean::dec(x_8);
x_12 = l_lean_parser_substring_of__string(x_10);
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
obj* _init_l_lean_expander_mixfix_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::mk_string("b");
x_8 = lean_name_mk_string(x_6, x_7);
x_9 = lean::mk_string(".");
lean::inc(x_8);
x_11 = l_lean_name_to__string__with__sep___main(x_9, x_8);
lean::dec(x_9);
x_13 = l_lean_parser_substring_of__string(x_11);
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
obj* _init_l_lean_expander_mixfix_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("notation");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":=");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::mk_string("b");
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::mk_string(".");
lean::inc(x_7);
x_10 = l_lean_name_to__string__with__sep___main(x_8, x_7);
lean::dec(x_8);
x_12 = l_lean_parser_substring_of__string(x_10);
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
obj* _init_l_lean_expander_mixfix_transform___closed__6() {
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
obj* l_lean_expander_mixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_2 = l_lean_parser_command_mixfix_has__view;
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
x_20 = l_lean_expander_mixfix_transform___closed__6;
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
x_22 = l_lean_expander_mixfix__to__notation__spec(x_9, x_11, x_1);
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
x_32 = l_lean_parser_command_notation_has__view;
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
x_42 = l_lean_parser_term_app_has__view;
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_46 = lean::cnstr_get(x_6, 4);
lean::inc(x_46);
lean::dec(x_6);
x_49 = l_lean_expander_mixfix_transform___closed__5;
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::apply_1(x_43, x_50);
x_52 = l_lean_expander_mixfix_transform___closed__3;
x_53 = l_lean_expander_mixfix_transform___closed__4;
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
x_60 = l_lean_parser_term_app_has__view;
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::cnstr_get(x_6, 4);
lean::inc(x_64);
lean::dec(x_6);
x_67 = l_lean_expander_mixfix_transform___closed__1;
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::apply_1(x_61, x_68);
x_70 = l_lean_expander_mixfix_transform___closed__3;
x_71 = l_lean_expander_mixfix_transform___closed__4;
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
x_79 = l_lean_parser_term_app_has__view;
x_80 = lean::cnstr_get(x_79, 1);
lean::inc(x_80);
lean::dec(x_79);
x_83 = lean::cnstr_get(x_6, 4);
lean::inc(x_83);
lean::dec(x_6);
x_86 = l_lean_expander_mixfix_transform___closed__1;
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set(x_87, 1, x_86);
lean::inc(x_80);
x_89 = lean::apply_1(x_80, x_87);
x_90 = l_lean_expander_mixfix_transform___closed__2;
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::apply_1(x_80, x_91);
x_93 = l_lean_expander_mixfix_transform___closed__3;
x_94 = l_lean_expander_mixfix_transform___closed__4;
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
obj* l_lean_expander_mixfix_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_mixfix_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_reserve__mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reserve");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_reserve__mixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_12; 
x_2 = l_lean_parser_command_reserve__mixfix_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_lean_expander_mixfix__to__notation__spec(x_7, x_9, x_1);
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
x_21 = l_lean_parser_command_reserve__notation_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_25 = l_lean_expander_reserve__mixfix_transform___closed__1;
x_26 = l_lean_expander_mixfix_transform___closed__3;
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
obj* l_lean_expander_reserve__mixfix_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_reserve__mixfix_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("{");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("}");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x83");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x84");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("[");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("]");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_mk__simple__binder(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
switch (x_1) {
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_3 = l_lean_expander_mk__simple__binder___closed__2;
x_4 = l_lean_expander_mk__simple__binder___closed__1;
x_5 = l_lean_expander_mk__simple__binder___closed__3;
lean::inc(x_2);
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_4);
lean::cnstr_set(x_8, 3, x_2);
lean::cnstr_set(x_8, 4, x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
case 2:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_10 = l_lean_expander_mk__simple__binder___closed__4;
x_11 = l_lean_expander_mk__simple__binder___closed__1;
x_12 = l_lean_expander_mk__simple__binder___closed__5;
lean::inc(x_2);
lean::inc(x_0);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_11);
lean::cnstr_set(x_15, 3, x_2);
lean::cnstr_set(x_15, 4, x_12);
x_16 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
case 3:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_17 = l_lean_expander_mk__simple__binder___closed__6;
x_18 = l_lean_expander_mk__simple__binder___closed__1;
x_19 = l_lean_expander_mk__simple__binder___closed__7;
lean::inc(x_2);
lean::inc(x_0);
x_22 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_0);
lean::cnstr_set(x_22, 2, x_18);
lean::cnstr_set(x_22, 3, x_2);
lean::cnstr_set(x_22, 4, x_19);
x_23 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
default:
{
obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; 
x_24 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_25 = l_lean_expander_mk__simple__binder___closed__1;
x_26 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_2);
lean::inc(x_0);
x_29 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_0);
lean::cnstr_set(x_29, 2, x_25);
lean::cnstr_set(x_29, 3, x_2);
lean::cnstr_set(x_29, 4, x_26);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
}
obj* l_lean_expander_mk__simple__binder___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_expander_mk__simple__binder(x_0, x_3, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_expander_binder__ident__to__ident___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* l_lean_expander_binder__ident__to__ident___main(obj* x_0) {
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
x_3 = l_lean_expander_binder__ident__to__ident___main___closed__1;
return x_3;
}
}
}
obj* l_lean_expander_binder__ident__to__ident___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_binder__ident__to__ident___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_binder__ident__to__ident(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_binder__ident__to__ident___main(x_0);
return x_1;
}
}
obj* l_lean_expander_binder__ident__to__ident___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_binder__ident__to__ident(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_get__opt__type___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_lean_parser_term_hole_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = lean::mk_string("_");
x_6 = l_string_trim(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::apply_1(x_1, x_8);
return x_9;
}
}
obj* l_lean_expander_get__opt__type___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type___main___closed__1;
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
obj* l_lean_expander_get__opt__type___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_expander_get__opt__type(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type___main(x_0);
return x_1;
}
}
obj* l_lean_expander_get__opt__type___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_expander_get__opt__type___main(x_0);
return x_1;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
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
x_7 = l_lean_expander_binder__ident__to__ident___main(x_2);
lean::dec(x_2);
x_9 = 0;
x_10 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
x_11 = l_lean_expander_mk__simple__binder(x_7, x_9, x_10);
lean::dec(x_7);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_1, 1);
x_10 = l_lean_expander_get__opt__type___main(x_9);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_13 = l_lean_expander_mk__simple__binder(x_11, x_0, x_10);
lean::dec(x_10);
lean::dec(x_11);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_0, x_1, x_6);
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
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("opt_param");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_24; obj* x_25; 
x_5 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_1, 1);
x_11 = l_lean_expander_get__opt__type___main(x_10);
x_12 = lean::cnstr_get(x_2, 1);
x_13 = lean::box(0);
lean::inc(x_12);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
x_19 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_21 = l_lean_expander_mk__simple__binder(x_19, x_0, x_18);
lean::dec(x_18);
lean::dec(x_19);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_0, x_1, x_2, x_7);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("auto_param");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::box(0);
lean::inc(x_9);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = l_lean_expander_mk__simple__binder(x_15, x_0, x_14);
lean::dec(x_14);
lean::dec(x_15);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_0, x_1, x_6);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_11 = l_lean_expander_mk__simple__binder(x_9, x_0, x_1);
lean::dec(x_9);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_0, x_1, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = l_lean_expander_get__opt__type___main(x_8);
x_10 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_12 = 0;
x_13 = l_lean_expander_mk__simple__binder(x_10, x_12, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_20; obj* x_21; obj* x_24; obj* x_25; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 1);
x_10 = l_lean_expander_get__opt__type___main(x_9);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::box(0);
lean::inc(x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_16, x_15);
x_18 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_20 = 0;
x_21 = l_lean_expander_mk__simple__binder(x_18, x_20, x_17);
lean::dec(x_17);
lean::dec(x_18);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_6);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_16; obj* x_17; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = lean::box(0);
lean::inc(x_8);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_13 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_12, x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_16 = 0;
x_17 = l_lean_expander_mk__simple__binder(x_14, x_16, x_13);
lean::dec(x_13);
lean::dec(x_14);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_0, x_5);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_10 = 0;
x_11 = l_lean_expander_mk__simple__binder(x_8, x_10, x_0);
lean::dec(x_8);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = l_lean_expander_get__opt__type___main(x_8);
x_10 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_12 = 1;
x_13 = l_lean_expander_mk__simple__binder(x_10, x_12, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_20; obj* x_21; obj* x_24; obj* x_25; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 1);
x_10 = l_lean_expander_get__opt__type___main(x_9);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::box(0);
lean::inc(x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_16, x_15);
x_18 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_20 = 1;
x_21 = l_lean_expander_mk__simple__binder(x_18, x_20, x_17);
lean::dec(x_17);
lean::dec(x_18);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_6);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_16; obj* x_17; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = lean::box(0);
lean::inc(x_8);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_13 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_12, x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_16 = 1;
x_17 = l_lean_expander_mk__simple__binder(x_14, x_16, x_13);
lean::dec(x_13);
lean::dec(x_14);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_0, x_5);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_10 = 1;
x_11 = l_lean_expander_mk__simple__binder(x_8, x_10, x_0);
lean::dec(x_8);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = l_lean_expander_get__opt__type___main(x_8);
x_10 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_12 = 2;
x_13 = l_lean_expander_mk__simple__binder(x_10, x_12, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_20; obj* x_21; obj* x_24; obj* x_25; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 1);
x_10 = l_lean_expander_get__opt__type___main(x_9);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::box(0);
lean::inc(x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_16, x_15);
x_18 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_20 = 2;
x_21 = l_lean_expander_mk__simple__binder(x_18, x_20, x_17);
lean::dec(x_17);
lean::dec(x_18);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_6);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_16; obj* x_17; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 1);
x_9 = lean::box(0);
lean::inc(x_8);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_13 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_12, x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_16 = 2;
x_17 = l_lean_expander_mk__simple__binder(x_14, x_16, x_13);
lean::dec(x_13);
lean::dec(x_14);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_0, x_5);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_10 = 2;
x_11 = l_lean_expander_mk__simple__binder(x_8, x_10, x_0);
lean::dec(x_8);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_21; obj* x_22; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 2);
x_9 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_8);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = l_lean_expander_get__opt__type___main(x_12);
lean::dec(x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_17 = 3;
x_18 = l_lean_expander_mk__simple__binder(x_15, x_17, x_13);
lean::dec(x_13);
lean::dec(x_15);
x_21 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; uint8 x_16; obj* x_17; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = l_lean_expander_get__opt__type___main(x_11);
lean::dec(x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_3);
lean::dec(x_3);
x_16 = 3;
x_17 = l_lean_expander_mk__simple__binder(x_14, x_16, x_12);
lean::dec(x_12);
lean::dec(x_14);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_1, 1);
x_10 = l_lean_expander_get__opt__type___main(x_9);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_13 = l_lean_expander_mk__simple__binder(x_11, x_0, x_10);
lean::dec(x_10);
lean::dec(x_11);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_0, x_1, x_6);
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
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_24; obj* x_25; 
x_5 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_1, 1);
x_11 = l_lean_expander_get__opt__type___main(x_10);
x_12 = lean::cnstr_get(x_2, 1);
x_13 = lean::box(0);
lean::inc(x_12);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
x_19 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_21 = l_lean_expander_mk__simple__binder(x_19, x_0, x_18);
lean::dec(x_18);
lean::dec(x_19);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_0, x_1, x_2, x_7);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::box(0);
lean::inc(x_9);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = l_lean_expander_mk__simple__binder(x_15, x_0, x_14);
lean::dec(x_14);
lean::dec(x_15);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_0, x_1, x_6);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_11 = l_lean_expander_mk__simple__binder(x_9, x_0, x_1);
lean::dec(x_9);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_0, x_1, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected auto param after type annotation");
return x_0;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = l_lean_expander_expand__bracketed__binder___main___closed__1;
return x_0;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected anonymous constructor");
return x_0;
}
}
obj* l_lean_expander_expand__bracketed__binder___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_0);
x_11 = l_lean_expander_expand__bracketed__binder___main___closed__4;
return x_11;
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_15; 
lean::dec(x_6);
x_15 = l_lean_expander_expand__bracketed__binder___main___closed__5;
return x_15;
}
else
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_6, 0);
lean::inc(x_16);
lean::dec(x_6);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; obj* x_23; obj* x_25; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_16, x_21);
lean::dec(x_16);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_23);
return x_25;
}
else
{
obj* x_26; 
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
lean::dec(x_19);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::cnstr_get(x_16, 0);
lean::inc(x_32);
x_34 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_16, x_29, x_32);
lean::dec(x_29);
lean::dec(x_16);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::cnstr_get(x_16, 1);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_43; obj* x_46; obj* x_48; 
x_40 = lean::cnstr_get(x_26, 0);
lean::inc(x_40);
lean::dec(x_26);
x_43 = lean::cnstr_get(x_16, 0);
lean::inc(x_43);
lean::dec(x_16);
x_46 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_40, x_43);
lean::dec(x_40);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_46);
return x_48;
}
else
{
obj* x_50; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_38);
x_50 = l_lean_parser_term_binder__default_has__view;
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_26);
x_55 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_56 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_54, x_55, x_1);
lean::dec(x_54);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_16);
x_59 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_61 = x_56;
} else {
 lean::inc(x_59);
 lean::dec(x_56);
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
obj* x_63; obj* x_65; obj* x_66; obj* x_69; obj* x_71; 
x_63 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_65 = x_56;
} else {
 lean::inc(x_63);
 lean::dec(x_56);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_16, 0);
lean::inc(x_66);
lean::dec(x_16);
x_69 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_63, x_66);
lean::dec(x_63);
if (lean::is_scalar(x_65)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_65;
}
lean::cnstr_set(x_71, 0, x_69);
return x_71;
}
}
}
}
}
}
case 1:
{
obj* x_74; 
lean::dec(x_4);
lean::dec(x_0);
x_74 = lean::cnstr_get(x_6, 2);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_78; obj* x_80; 
x_76 = lean::cnstr_get(x_6, 0);
lean::inc(x_76);
x_78 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_76);
lean::dec(x_6);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_78);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_74, 0);
lean::inc(x_81);
lean::dec(x_74);
if (lean::obj_tag(x_81) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_92; 
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
lean::dec(x_81);
x_87 = lean::cnstr_get(x_6, 0);
lean::inc(x_87);
x_89 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_84, x_87);
lean::dec(x_84);
lean::dec(x_6);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_6, 1);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_98; obj* x_101; obj* x_103; 
x_95 = lean::cnstr_get(x_81, 0);
lean::inc(x_95);
lean::dec(x_81);
x_98 = lean::cnstr_get(x_6, 0);
lean::inc(x_98);
lean::dec(x_6);
x_101 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_95, x_98);
lean::dec(x_95);
x_103 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_103, 0, x_101);
return x_103;
}
else
{
obj* x_105; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_93);
x_105 = l_lean_parser_term_binder__default_has__view;
x_106 = lean::cnstr_get(x_105, 1);
lean::inc(x_106);
lean::dec(x_105);
x_109 = lean::apply_1(x_106, x_81);
x_110 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_111 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_109, x_110, x_1);
lean::dec(x_109);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_6);
x_114 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_116 = x_111;
} else {
 lean::inc(x_114);
 lean::dec(x_111);
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
obj* x_118; obj* x_120; obj* x_121; obj* x_124; obj* x_126; 
x_118 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_120 = x_111;
} else {
 lean::inc(x_118);
 lean::dec(x_111);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_6, 0);
lean::inc(x_121);
lean::dec(x_6);
x_124 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_118, x_121);
lean::dec(x_118);
if (lean::is_scalar(x_120)) {
 x_126 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_126 = x_120;
}
lean::cnstr_set(x_126, 0, x_124);
return x_126;
}
}
}
}
}
case 2:
{
obj* x_129; 
lean::dec(x_4);
lean::dec(x_0);
x_129 = lean::cnstr_get(x_6, 2);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
obj* x_131; obj* x_133; obj* x_135; 
x_131 = lean::cnstr_get(x_6, 0);
lean::inc(x_131);
x_133 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_131);
lean::dec(x_6);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_133);
return x_135;
}
else
{
obj* x_136; 
x_136 = lean::cnstr_get(x_129, 0);
lean::inc(x_136);
lean::dec(x_129);
if (lean::obj_tag(x_136) == 0)
{
obj* x_139; obj* x_142; obj* x_144; obj* x_147; 
x_139 = lean::cnstr_get(x_136, 0);
lean::inc(x_139);
lean::dec(x_136);
x_142 = lean::cnstr_get(x_6, 0);
lean::inc(x_142);
x_144 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_139, x_142);
lean::dec(x_139);
lean::dec(x_6);
x_147 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_147, 0, x_144);
return x_147;
}
else
{
obj* x_148; 
x_148 = lean::cnstr_get(x_6, 1);
lean::inc(x_148);
if (lean::obj_tag(x_148) == 0)
{
obj* x_150; obj* x_153; obj* x_156; obj* x_158; 
x_150 = lean::cnstr_get(x_136, 0);
lean::inc(x_150);
lean::dec(x_136);
x_153 = lean::cnstr_get(x_6, 0);
lean::inc(x_153);
lean::dec(x_6);
x_156 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_150, x_153);
lean::dec(x_150);
x_158 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_158, 0, x_156);
return x_158;
}
else
{
obj* x_160; obj* x_161; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_148);
x_160 = l_lean_parser_term_binder__default_has__view;
x_161 = lean::cnstr_get(x_160, 1);
lean::inc(x_161);
lean::dec(x_160);
x_164 = lean::apply_1(x_161, x_136);
x_165 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_166 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_164, x_165, x_1);
lean::dec(x_164);
if (lean::obj_tag(x_166) == 0)
{
obj* x_169; obj* x_171; obj* x_172; 
lean::dec(x_6);
x_169 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 x_171 = x_166;
} else {
 lean::inc(x_169);
 lean::dec(x_166);
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
obj* x_173; obj* x_175; obj* x_176; obj* x_179; obj* x_181; 
x_173 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 x_175 = x_166;
} else {
 lean::inc(x_173);
 lean::dec(x_166);
 x_175 = lean::box(0);
}
x_176 = lean::cnstr_get(x_6, 0);
lean::inc(x_176);
lean::dec(x_6);
x_179 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_173, x_176);
lean::dec(x_173);
if (lean::is_scalar(x_175)) {
 x_181 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_181 = x_175;
}
lean::cnstr_set(x_181, 0, x_179);
return x_181;
}
}
}
}
}
case 3:
{
lean::dec(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_184; obj* x_187; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_194; 
x_184 = lean::cnstr_get(x_6, 0);
lean::inc(x_184);
lean::dec(x_6);
x_187 = lean::cnstr_get(x_184, 0);
lean::inc(x_187);
x_189 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_189, 0, x_187);
x_190 = lean::box(0);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_189);
lean::cnstr_set(x_191, 1, x_190);
x_192 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_184, x_191);
lean::dec(x_184);
x_194 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_194, 0, x_192);
return x_194;
}
else
{
obj* x_195; obj* x_198; obj* x_199; obj* x_201; 
x_195 = lean::cnstr_get(x_6, 0);
lean::inc(x_195);
lean::dec(x_6);
x_198 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_199 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_195, x_198);
lean::dec(x_195);
x_201 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_201, 0, x_199);
return x_201;
}
}
default:
{
obj* x_204; obj* x_205; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_6);
lean::dec(x_0);
x_204 = l_lean_parser_term_anonymous__constructor_has__view;
x_205 = lean::cnstr_get(x_204, 1);
lean::inc(x_205);
lean::dec(x_204);
x_208 = lean::apply_1(x_205, x_4);
x_209 = l_lean_expander_expand__bracketed__binder___main___closed__7;
x_210 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_208, x_209, x_1);
lean::dec(x_208);
if (lean::obj_tag(x_210) == 0)
{
obj* x_212; obj* x_214; obj* x_215; 
x_212 = lean::cnstr_get(x_210, 0);
if (lean::is_exclusive(x_210)) {
 x_214 = x_210;
} else {
 lean::inc(x_212);
 lean::dec(x_210);
 x_214 = lean::box(0);
}
if (lean::is_scalar(x_214)) {
 x_215 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_215 = x_214;
}
lean::cnstr_set(x_215, 0, x_212);
return x_215;
}
else
{
obj* x_216; obj* x_218; obj* x_219; obj* x_221; 
x_216 = lean::cnstr_get(x_210, 0);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_set(x_210, 0, lean::box(0));
 x_218 = x_210;
} else {
 lean::inc(x_216);
 lean::dec(x_210);
 x_218 = lean::box(0);
}
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_219, 2);
lean::inc(x_221);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_226; uint8 x_228; obj* x_229; obj* x_231; 
x_223 = lean::cnstr_get(x_216, 0);
lean::inc(x_223);
lean::dec(x_216);
x_226 = lean::cnstr_get(x_219, 0);
lean::inc(x_226);
x_228 = lean::unbox(x_223);
x_229 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_228, x_219, x_226);
lean::dec(x_219);
if (lean::is_scalar(x_218)) {
 x_231 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_231 = x_218;
}
lean::cnstr_set(x_231, 0, x_229);
return x_231;
}
else
{
obj* x_232; 
x_232 = lean::cnstr_get(x_221, 0);
lean::inc(x_232);
lean::dec(x_221);
if (lean::obj_tag(x_232) == 0)
{
obj* x_235; obj* x_238; obj* x_241; uint8 x_243; obj* x_244; obj* x_247; 
x_235 = lean::cnstr_get(x_216, 0);
lean::inc(x_235);
lean::dec(x_216);
x_238 = lean::cnstr_get(x_232, 0);
lean::inc(x_238);
lean::dec(x_232);
x_241 = lean::cnstr_get(x_219, 0);
lean::inc(x_241);
x_243 = lean::unbox(x_235);
x_244 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_243, x_219, x_238, x_241);
lean::dec(x_238);
lean::dec(x_219);
if (lean::is_scalar(x_218)) {
 x_247 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_247 = x_218;
}
lean::cnstr_set(x_247, 0, x_244);
return x_247;
}
else
{
obj* x_248; 
x_248 = lean::cnstr_get(x_219, 1);
lean::inc(x_248);
if (lean::obj_tag(x_248) == 0)
{
obj* x_250; obj* x_253; obj* x_256; uint8 x_259; obj* x_260; obj* x_262; 
x_250 = lean::cnstr_get(x_216, 0);
lean::inc(x_250);
lean::dec(x_216);
x_253 = lean::cnstr_get(x_232, 0);
lean::inc(x_253);
lean::dec(x_232);
x_256 = lean::cnstr_get(x_219, 0);
lean::inc(x_256);
lean::dec(x_219);
x_259 = lean::unbox(x_250);
x_260 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_259, x_253, x_256);
lean::dec(x_253);
if (lean::is_scalar(x_218)) {
 x_262 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_262 = x_218;
}
lean::cnstr_set(x_262, 0, x_260);
return x_262;
}
else
{
obj* x_265; obj* x_268; obj* x_269; obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_218);
lean::dec(x_248);
x_265 = lean::cnstr_get(x_216, 0);
lean::inc(x_265);
lean::dec(x_216);
x_268 = l_lean_parser_term_binder__default_has__view;
x_269 = lean::cnstr_get(x_268, 1);
lean::inc(x_269);
lean::dec(x_268);
x_272 = lean::apply_1(x_269, x_232);
x_273 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_274 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_272, x_273, x_1);
lean::dec(x_272);
if (lean::obj_tag(x_274) == 0)
{
obj* x_278; obj* x_280; obj* x_281; 
lean::dec(x_219);
lean::dec(x_265);
x_278 = lean::cnstr_get(x_274, 0);
if (lean::is_exclusive(x_274)) {
 x_280 = x_274;
} else {
 lean::inc(x_278);
 lean::dec(x_274);
 x_280 = lean::box(0);
}
if (lean::is_scalar(x_280)) {
 x_281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_281 = x_280;
}
lean::cnstr_set(x_281, 0, x_278);
return x_281;
}
else
{
obj* x_282; obj* x_284; obj* x_285; uint8 x_288; obj* x_289; obj* x_291; 
x_282 = lean::cnstr_get(x_274, 0);
if (lean::is_exclusive(x_274)) {
 x_284 = x_274;
} else {
 lean::inc(x_282);
 lean::dec(x_274);
 x_284 = lean::box(0);
}
x_285 = lean::cnstr_get(x_219, 0);
lean::inc(x_285);
lean::dec(x_219);
x_288 = lean::unbox(x_265);
x_289 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_288, x_282, x_285);
lean::dec(x_282);
if (lean::is_scalar(x_284)) {
 x_291 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_291 = x_284;
}
lean::cnstr_set(x_291, 0, x_289);
return x_291;
}
}
}
}
}
}
}
}
}
default:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_292; obj* x_295; 
x_292 = lean::cnstr_get(x_0, 0);
lean::inc(x_292);
lean::dec(x_0);
x_295 = lean::cnstr_get(x_292, 1);
lean::inc(x_295);
lean::dec(x_292);
if (lean::obj_tag(x_295) == 0)
{
obj* x_299; 
lean::dec(x_295);
x_299 = l_lean_expander_expand__bracketed__binder___main___closed__3;
x_2 = x_299;
goto lbl_3;
}
else
{
obj* x_300; uint8 x_303; obj* x_304; obj* x_305; 
x_300 = lean::cnstr_get(x_295, 0);
lean::inc(x_300);
lean::dec(x_295);
x_303 = 0;
x_304 = lean::box(x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_300);
x_2 = x_305;
goto lbl_3;
}
}
case 1:
{
obj* x_306; obj* x_309; uint8 x_312; obj* x_313; obj* x_314; 
x_306 = lean::cnstr_get(x_0, 0);
lean::inc(x_306);
lean::dec(x_0);
x_309 = lean::cnstr_get(x_306, 1);
lean::inc(x_309);
lean::dec(x_306);
x_312 = 1;
x_313 = lean::box(x_312);
x_314 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_309);
x_2 = x_314;
goto lbl_3;
}
case 2:
{
obj* x_315; obj* x_318; uint8 x_321; obj* x_322; obj* x_323; 
x_315 = lean::cnstr_get(x_0, 0);
lean::inc(x_315);
lean::dec(x_0);
x_318 = lean::cnstr_get(x_315, 1);
lean::inc(x_318);
lean::dec(x_315);
x_321 = 2;
x_322 = lean::box(x_321);
x_323 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_323, 0, x_322);
lean::cnstr_set(x_323, 1, x_318);
x_2 = x_323;
goto lbl_3;
}
case 3:
{
obj* x_324; obj* x_327; 
x_324 = lean::cnstr_get(x_0, 0);
lean::inc(x_324);
lean::dec(x_0);
x_327 = lean::cnstr_get(x_324, 1);
lean::inc(x_327);
lean::dec(x_324);
if (lean::obj_tag(x_327) == 0)
{
obj* x_330; obj* x_333; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_342; obj* x_343; obj* x_344; obj* x_345; uint8 x_346; obj* x_347; obj* x_348; 
x_330 = lean::cnstr_get(x_327, 0);
lean::inc(x_330);
lean::dec(x_327);
x_333 = lean::cnstr_get(x_330, 0);
lean::inc(x_333);
x_335 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_335, 0, x_333);
x_336 = lean::box(0);
x_337 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_337, 0, x_335);
lean::cnstr_set(x_337, 1, x_336);
x_338 = lean::box(0);
x_339 = lean::cnstr_get(x_330, 2);
lean::inc(x_339);
lean::dec(x_330);
x_342 = l_lean_expander_mk__simple__binder___closed__1;
x_343 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_339);
x_344 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_344, 0, x_343);
x_345 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_345, 0, x_337);
lean::cnstr_set(x_345, 1, x_344);
lean::cnstr_set(x_345, 2, x_338);
x_346 = 3;
x_347 = lean::box(x_346);
x_348 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_348, 0, x_347);
lean::cnstr_set(x_348, 1, x_345);
x_2 = x_348;
goto lbl_3;
}
else
{
obj* x_349; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; uint8 x_358; obj* x_359; obj* x_360; 
x_349 = lean::cnstr_get(x_327, 0);
lean::inc(x_349);
lean::dec(x_327);
x_352 = lean::box(0);
x_353 = l_lean_expander_mk__simple__binder___closed__1;
x_354 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_354, 0, x_353);
lean::cnstr_set(x_354, 1, x_349);
x_355 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_355, 0, x_354);
x_356 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_357 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_357, 0, x_356);
lean::cnstr_set(x_357, 1, x_355);
lean::cnstr_set(x_357, 2, x_352);
x_358 = 3;
x_359 = lean::box(x_358);
x_360 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_357);
x_2 = x_360;
goto lbl_3;
}
}
default:
{
obj* x_361; obj* x_364; obj* x_365; obj* x_368; obj* x_369; obj* x_370; 
x_361 = lean::cnstr_get(x_0, 0);
lean::inc(x_361);
lean::dec(x_0);
x_364 = l_lean_parser_term_anonymous__constructor_has__view;
x_365 = lean::cnstr_get(x_364, 1);
lean::inc(x_365);
lean::dec(x_364);
x_368 = lean::apply_1(x_365, x_361);
x_369 = l_lean_expander_expand__bracketed__binder___main___closed__7;
x_370 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_368, x_369, x_1);
lean::dec(x_368);
if (lean::obj_tag(x_370) == 0)
{
obj* x_372; obj* x_374; obj* x_375; 
x_372 = lean::cnstr_get(x_370, 0);
if (lean::is_exclusive(x_370)) {
 x_374 = x_370;
} else {
 lean::inc(x_372);
 lean::dec(x_370);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_372);
return x_375;
}
else
{
obj* x_376; 
x_376 = lean::cnstr_get(x_370, 0);
lean::inc(x_376);
lean::dec(x_370);
x_2 = x_376;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_379; obj* x_381; 
x_379 = lean::cnstr_get(x_2, 1);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_379, 2);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_383; obj* x_386; uint8 x_388; obj* x_389; obj* x_391; 
x_383 = lean::cnstr_get(x_2, 0);
lean::inc(x_383);
lean::dec(x_2);
x_386 = lean::cnstr_get(x_379, 0);
lean::inc(x_386);
x_388 = lean::unbox(x_383);
x_389 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_388, x_379, x_386);
lean::dec(x_379);
x_391 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_391, 0, x_389);
return x_391;
}
else
{
obj* x_392; 
x_392 = lean::cnstr_get(x_381, 0);
lean::inc(x_392);
lean::dec(x_381);
if (lean::obj_tag(x_392) == 0)
{
obj* x_395; obj* x_398; obj* x_401; uint8 x_403; obj* x_404; obj* x_407; 
x_395 = lean::cnstr_get(x_2, 0);
lean::inc(x_395);
lean::dec(x_2);
x_398 = lean::cnstr_get(x_392, 0);
lean::inc(x_398);
lean::dec(x_392);
x_401 = lean::cnstr_get(x_379, 0);
lean::inc(x_401);
x_403 = lean::unbox(x_395);
x_404 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_403, x_379, x_398, x_401);
lean::dec(x_398);
lean::dec(x_379);
x_407 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_407, 0, x_404);
return x_407;
}
else
{
obj* x_408; 
x_408 = lean::cnstr_get(x_379, 1);
lean::inc(x_408);
if (lean::obj_tag(x_408) == 0)
{
obj* x_410; obj* x_413; obj* x_416; uint8 x_419; obj* x_420; obj* x_422; 
x_410 = lean::cnstr_get(x_2, 0);
lean::inc(x_410);
lean::dec(x_2);
x_413 = lean::cnstr_get(x_392, 0);
lean::inc(x_413);
lean::dec(x_392);
x_416 = lean::cnstr_get(x_379, 0);
lean::inc(x_416);
lean::dec(x_379);
x_419 = lean::unbox(x_410);
x_420 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_419, x_413, x_416);
lean::dec(x_413);
x_422 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_422, 0, x_420);
return x_422;
}
else
{
obj* x_424; obj* x_427; obj* x_428; obj* x_431; obj* x_432; obj* x_433; 
lean::dec(x_408);
x_424 = lean::cnstr_get(x_2, 0);
lean::inc(x_424);
lean::dec(x_2);
x_427 = l_lean_parser_term_binder__default_has__view;
x_428 = lean::cnstr_get(x_427, 1);
lean::inc(x_428);
lean::dec(x_427);
x_431 = lean::apply_1(x_428, x_392);
x_432 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_433 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_431, x_432, x_1);
lean::dec(x_431);
if (lean::obj_tag(x_433) == 0)
{
obj* x_437; obj* x_439; obj* x_440; 
lean::dec(x_379);
lean::dec(x_424);
x_437 = lean::cnstr_get(x_433, 0);
if (lean::is_exclusive(x_433)) {
 x_439 = x_433;
} else {
 lean::inc(x_437);
 lean::dec(x_433);
 x_439 = lean::box(0);
}
if (lean::is_scalar(x_439)) {
 x_440 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_440 = x_439;
}
lean::cnstr_set(x_440, 0, x_437);
return x_440;
}
else
{
obj* x_441; obj* x_443; obj* x_444; uint8 x_447; obj* x_448; obj* x_450; 
x_441 = lean::cnstr_get(x_433, 0);
if (lean::is_exclusive(x_433)) {
 x_443 = x_433;
} else {
 lean::inc(x_441);
 lean::dec(x_433);
 x_443 = lean::box(0);
}
x_444 = lean::cnstr_get(x_379, 0);
lean::inc(x_444);
lean::dec(x_379);
x_447 = lean::unbox(x_424);
x_448 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_447, x_441, x_444);
lean::dec(x_441);
if (lean::is_scalar(x_443)) {
 x_450 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_450 = x_443;
}
lean::cnstr_set(x_450, 0, x_448);
return x_450;
}
}
}
}
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_4, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_4, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_expander_expand__bracketed__binder___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder___main(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_expand__bracketed__binder(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_expander_expand__bracketed__binder___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
lean::dec(x_9);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_12);
x_15 = lean::apply_2(x_0, x_14, x_8);
return x_15;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_1, x_2, x_7);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_12 = 0;
x_13 = l_lean_expander_mk__simple__binder(x_11, x_12, x_8);
lean::dec(x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_13);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
lean::dec(x_9);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_12);
x_15 = lean::apply_2(x_0, x_14, x_8);
return x_15;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_1, x_2, x_7);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_12 = 0;
x_13 = l_lean_expander_mk__simple__binder(x_11, x_12, x_8);
lean::dec(x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_13);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_1, x_6);
lean::inc(x_5);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_5);
x_11 = lean::apply_2(x_0, x_10, x_8);
return x_11;
}
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = l_lean_parser_ident__univs_has__view;
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
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" with ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_24; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_9);
x_11 = l_lean_parser_term_hole_has__view;
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_15 = lean::mk_string("_");
x_16 = l_string_trim(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_1(x_12, x_18);
x_20 = 0;
x_21 = l_lean_expander_mk__simple__binder(x_10, x_20, x_19);
lean::dec(x_19);
lean::dec(x_10);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
}
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
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
lean::inc(x_0);
x_13 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_1, x_9, x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_11);
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
if (lean::obj_tag(x_7) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_27; 
x_21 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_23 = x_13;
} else {
 lean::inc(x_21);
 lean::dec(x_13);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_7, 0);
lean::inc(x_24);
lean::dec(x_7);
switch (lean::obj_tag(x_24)) {
case 4:
{
obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::box(0);
x_33 = lean::box(0);
x_34 = l_lean_parser_term_match_has__view;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_38 = l_lean_parser_term_anonymous__constructor_has__view;
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
lean::dec(x_38);
x_42 = lean::apply_1(x_39, x_29);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_32);
if (lean::is_scalar(x_11)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_11;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_33);
x_45 = l_lean_expander_mixfix_transform___closed__4;
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 2, x_21);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_32);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_33);
x_49 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_50 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
x_51 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
x_52 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_32);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set(x_52, 4, x_32);
lean::cnstr_set(x_52, 5, x_48);
x_53 = lean::apply_1(x_35, x_52);
x_54 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
x_55 = lean::apply_2(x_0, x_54, x_53);
if (lean::is_scalar(x_23)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_23;
}
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
default:
{
obj* x_59; 
lean::dec(x_11);
lean::dec(x_23);
x_59 = lean::box(0);
x_27 = x_59;
goto lbl_28;
}
}
lbl_28:
{
obj* x_61; 
lean::dec(x_27);
x_61 = l_lean_expander_expand__bracketed__binder___main(x_24, x_3);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_0);
lean::dec(x_21);
x_64 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
return x_67;
}
else
{
obj* x_68; obj* x_70; obj* x_71; obj* x_74; 
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
 x_70 = lean::box(0);
}
x_71 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_21, x_68);
lean::dec(x_68);
lean::dec(x_21);
if (lean::is_scalar(x_70)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_70;
}
lean::cnstr_set(x_74, 0, x_71);
return x_74;
}
}
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_82; uint8 x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_11);
x_76 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_78 = x_13;
} else {
 lean::inc(x_76);
 lean::dec(x_13);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_7, 0);
lean::inc(x_79);
lean::dec(x_7);
x_82 = l_lean_expander_binder__ident__to__ident___main(x_79);
lean::dec(x_79);
x_84 = 0;
x_85 = l_lean_expander_get__opt__type___main___closed__1;
x_86 = l_lean_expander_mk__simple__binder(x_82, x_84, x_85);
lean::dec(x_82);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_86);
x_89 = lean::apply_2(x_0, x_88, x_76);
if (lean::is_scalar(x_78)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_78;
}
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
lean::dec(x_9);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_12);
x_15 = lean::apply_2(x_0, x_14, x_8);
return x_15;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_1, x_2, x_7);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_12 = 0;
x_13 = l_lean_expander_mk__simple__binder(x_11, x_12, x_8);
lean::dec(x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_13);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
}
}
}
obj* l_lean_expander_expand__binders(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; 
x_14 = lean::box(0);
x_12 = x_14;
goto lbl_13;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_17 = x_7;
} else {
 lean::inc(x_15);
 lean::dec(x_7);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_2, x_18, x_9);
lean::dec(x_9);
lean::dec(x_18);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_28; 
lean::dec(x_15);
lean::dec(x_17);
x_28 = lean::box(0);
x_12 = x_28;
goto lbl_13;
}
}
lbl_13:
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_12);
x_30 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_2, x_9);
lean::dec(x_9);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_30);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_7, 0);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_4, 0);
lean::inc(x_36);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_42; 
lean::dec(x_34);
x_42 = lean::box(0);
x_39 = x_42;
goto lbl_40;
}
else
{
obj* x_43; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_43 = x_7;
} else {
 lean::dec(x_7);
 x_43 = lean::box(0);
}
if (lean::obj_tag(x_34) == 0)
{
obj* x_44; obj* x_47; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_34, 0);
lean::inc(x_44);
lean::dec(x_34);
x_47 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_2, x_44, x_36);
lean::dec(x_36);
lean::dec(x_44);
if (lean::is_scalar(x_43)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_43;
}
lean::cnstr_set(x_50, 0, x_47);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_54; 
lean::dec(x_34);
lean::dec(x_43);
x_54 = lean::box(0);
x_39 = x_54;
goto lbl_40;
}
}
lbl_40:
{
obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_39);
x_56 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_2, x_36);
lean::dec(x_36);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_56);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
else
{
obj* x_60; obj* x_64; 
x_60 = lean::cnstr_get(x_34, 0);
lean::inc(x_60);
lean::inc(x_60);
lean::inc(x_0);
x_64 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_2, x_60, x_3);
if (lean::obj_tag(x_64) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_60);
lean::dec(x_34);
x_70 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_72 = x_64;
} else {
 lean::inc(x_70);
 lean::dec(x_64);
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
obj* x_74; obj* x_76; obj* x_77; obj* x_80; 
x_74 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_set(x_64, 0, lean::box(0));
 x_76 = x_64;
} else {
 lean::inc(x_74);
 lean::dec(x_64);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_4, 0);
lean::inc(x_77);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_84; 
lean::dec(x_60);
lean::dec(x_34);
x_84 = lean::box(0);
x_80 = x_84;
goto lbl_81;
}
else
{
obj* x_85; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_85 = x_7;
} else {
 lean::dec(x_7);
 x_85 = lean::box(0);
}
if (lean::obj_tag(x_34) == 0)
{
obj* x_88; obj* x_92; obj* x_93; 
lean::dec(x_34);
lean::dec(x_76);
x_88 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_74, x_60, x_77);
lean::dec(x_77);
lean::dec(x_60);
lean::dec(x_74);
if (lean::is_scalar(x_85)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_85;
}
lean::cnstr_set(x_92, 0, x_88);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
else
{
obj* x_97; 
lean::dec(x_60);
lean::dec(x_34);
lean::dec(x_85);
x_97 = lean::box(0);
x_80 = x_97;
goto lbl_81;
}
}
lbl_81:
{
obj* x_99; obj* x_102; obj* x_103; 
lean::dec(x_80);
x_99 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_74, x_77);
lean::dec(x_77);
lean::dec(x_74);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_99);
if (lean::is_scalar(x_76)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_76;
}
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
}
}
}
else
{
obj* x_106; 
lean::dec(x_1);
lean::dec(x_0);
x_106 = l_lean_expander_no__expansion___closed__1;
return x_106;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_expander_expand__binders___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_expand__binders(x_0, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder___main___closed__4;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = l_lean_expander_expand__bracketed__binder___main(x_3, x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_7);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
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
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_5, x_1);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_7);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_21);
 lean::dec(x_18);
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
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_27 = x_18;
} else {
 lean::inc(x_25);
 lean::dec(x_18);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_28 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_28 = x_7;
}
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_25);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
obj* l_lean_expander_bracketed__binders_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = l_lean_parser_term_bracketed__binders_has__view;
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
x_9 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_6, x_1);
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
x_21 = l_list_join___main___rarg(x_15);
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
x_27 = l_lean_expander_no__expansion___closed__1;
return x_27;
}
}
}
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_bracketed__binders_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_bracketed__binders_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_lambda_transform___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_7 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_1);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_0);
lean::cnstr_set(x_10, 2, x_7);
lean::cnstr_set(x_10, 3, x_1);
x_11 = lean::apply_1(x_3, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_lambda_transform___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_expander_lambda_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 3);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_lean_expander_lambda_transform___closed__1;
x_13 = l_lean_expander_expand__binders(x_12, x_7, x_9, x_1);
lean::dec(x_9);
return x_13;
}
}
obj* l_lean_expander_lambda_transform___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_lambda_transform___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_lambda_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_lambda_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_pi_transform___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_12; obj* x_13; 
x_3 = l_lean_parser_term_pi_has__view;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
x_8 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_7);
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_8);
lean::cnstr_set(x_12, 3, x_2);
x_13 = lean::apply_1(x_4, x_12);
return x_13;
}
}
obj* l_lean_expander_pi_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
x_2 = l_lean_parser_term_pi_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform___lambda__1___boxed), 3, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 3);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_expander_expand__binders(x_8, x_9, x_11, x_1);
lean::dec(x_11);
return x_14;
}
}
obj* l_lean_expander_pi_transform___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_pi_transform___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_expander_pi_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_pi_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_arrow_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("a");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* _init_l_lean_expander_arrow_transform___closed__2() {
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
obj* l_lean_expander_arrow_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_2 = l_lean_parser_term_arrow_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_lean_parser_term_pi_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_14 = l_lean_expander_arrow_transform___closed__1;
x_15 = l_lean_expander_mk__simple__binder___closed__1;
x_16 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
x_23 = l_lean_expander_arrow_transform___closed__2;
x_24 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
obj* l_lean_expander_arrow_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_arrow_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_paren_transform___spec__1(obj* x_0) {
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
x_10 = l_list_map___main___at_lean_expander_paren_transform___spec__1(x_4);
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
obj* _init_l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("prod");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("mk");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_expander_glob__id(x_4);
return x_5;
}
}
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(obj* x_0, obj* x_1) {
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
x_11 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_2, lean::box(0));
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
x_16 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_16, x_15);
return x_17;
}
}
}
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_list_map___main___at_lean_expander_paren_transform___spec__1(x_2);
lean::inc(x_0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_7, lean::box(0));
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
obj* _init_l_lean_expander_paren_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("unit");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("star");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_expander_glob__id(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* _init_l_lean_expander_paren_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("typed_expr");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_paren_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; 
x_2 = l_lean_parser_term_paren_has__view;
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
x_10 = l_lean_expander_paren_transform___closed__1;
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
obj* x_26; obj* x_29; obj* x_32; obj* x_34; 
lean::dec(x_24);
x_26 = lean::cnstr_get(x_11, 0);
lean::inc(x_26);
lean::dec(x_11);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
x_32 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_26, x_29);
lean::dec(x_26);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_32);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_35 = lean::cnstr_get(x_11, 0);
lean::inc(x_35);
lean::dec(x_11);
x_38 = lean::cnstr_get(x_22, 0);
lean::inc(x_38);
lean::dec(x_22);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_35);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_expander_paren_transform___closed__2;
x_48 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_47, x_46);
if (lean::is_scalar(x_24)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_24;
}
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_expander_paren_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_paren_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("this");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
lean::dec(x_4);
x_8 = l_lean_parser_substring_of__string(x_6);
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
obj* l_lean_expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_9; 
x_2 = l_lean_parser_term_assume_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = l_lean_parser_term_lambda_has__view;
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
x_22 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_23 = l_lean_expander_assume_transform___closed__1;
x_24 = l_lean_expander_mk__simple__binder___closed__1;
x_25 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
x_29 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_30 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
x_44 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_45 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
obj* l_lean_expander_assume_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_assume_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_if_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ite");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_if_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("not");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_if_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("dite");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_if_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; 
x_2 = l_lean_parser_term_if_has__view;
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
x_20 = l_lean_expander_if_transform___closed__1;
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
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
x_29 = l_lean_parser_term_lambda_has__view;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
lean::dec(x_29);
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_36 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_37 = l_lean_expander_mk__simple__binder___closed__1;
x_38 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
x_46 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_47 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
x_54 = l_lean_expander_if_transform___closed__2;
x_55 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_54, x_53);
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
x_67 = l_lean_expander_if_transform___closed__3;
x_68 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_67, x_66);
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
obj* l_lean_expander_if_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_if_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_4);
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
obj* _init_l_lean_expander_let_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_lean_parser_term_hole_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::mk_string("_");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_6, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* l_lean_expander_let_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_term_let_has__view;
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
x_23 = l_lean_expander_let_transform___closed__1;
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
x_43 = l_lean_expander_no__expansion___closed__1;
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
x_50 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_11);
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
x_60 = l_lean_parser_term_pi_has__view;
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
lean::dec(x_60);
x_64 = l_lean_expander_get__opt__type___main(x_46);
lean::dec(x_46);
x_66 = l_lean_expander_arrow_transform___closed__2;
x_67 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_54);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_54);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_64);
x_70 = lean::apply_1(x_61, x_69);
x_71 = l_lean_expander_mk__simple__binder___closed__1;
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
x_78 = l_lean_parser_term_lambda_has__view;
x_79 = lean::cnstr_get(x_78, 1);
lean::inc(x_79);
lean::dec(x_78);
x_82 = lean::cnstr_get(x_5, 3);
lean::inc(x_82);
x_84 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
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
x_99 = l_lean_parser_term_match_has__view;
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
x_114 = l_lean_expander_mixfix_transform___closed__4;
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
x_118 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_119 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
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
obj* l_lean_expander_let_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_let_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_constant_transform___spec__1(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_expander_constant_transform___spec__1(x_4);
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
obj* _init_l_lean_expander_constant_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_constant_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = l_lean_parser_command_constant_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::box(0);
x_17 = l_list_map___main___at_lean_expander_constant_transform___spec__1(x_13);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 2);
 x_29 = x_5;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_5);
 x_29 = lean::box(0);
}
x_30 = l_lean_parser_term_pi_has__view;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::cnstr_get(x_10, 1);
lean::inc(x_34);
lean::dec(x_10);
x_37 = l_lean_expander_arrow_transform___closed__2;
x_38 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_21);
lean::cnstr_set(x_39, 2, x_38);
lean::cnstr_set(x_39, 3, x_34);
x_40 = lean::apply_1(x_31, x_39);
x_41 = l_lean_expander_mk__simple__binder___closed__1;
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_lean_expander_constant_transform___closed__1;
if (lean::is_scalar(x_12)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_12;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
if (lean::is_scalar(x_29)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_29;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_27);
lean::cnstr_set(x_45, 2, x_44);
x_46 = lean::apply_1(x_22, x_45);
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
x_52 = l_lean_expander_no__expansion___closed__1;
return x_52;
}
}
}
obj* l_lean_expander_constant_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_constant_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@[");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::mk_string("]");
x_7 = l_string_trim(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_5);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("class");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_7 = l_lean_name_to__string__with__sep___main(x_5, x_4);
lean::dec(x_5);
x_9 = l_lean_parser_substring_of__string(x_7);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_4);
lean::cnstr_set(x_10, 3, x_1);
lean::cnstr_set(x_10, 4, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
return x_12;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_expander_declaration_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_command_declaration_has__view;
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
x_16 = l_lean_expander_no__expansion___closed__1;
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
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
x_36 = lean::box(0);
x_37 = l_lean_expander_declaration_transform___closed__1;
x_38 = l_option_get__or__else___main___rarg(x_34, x_37);
lean::dec(x_34);
x_40 = lean::cnstr_get(x_2, 1);
lean::inc(x_40);
lean::dec(x_2);
x_43 = lean::cnstr_get(x_31, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_38, 1);
lean::inc(x_47);
x_49 = l_lean_expander_declaration_transform___closed__2;
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
x_51 = lean::cnstr_get(x_38, 2);
lean::inc(x_51);
lean::dec(x_38);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_45);
lean::cnstr_set(x_54, 1, x_50);
lean::cnstr_set(x_54, 2, x_51);
if (lean::is_scalar(x_17)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_17;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::cnstr_get(x_31, 2);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_31, 3);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_31, 4);
lean::inc(x_60);
lean::dec(x_31);
x_63 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_63, 0, x_43);
lean::cnstr_set(x_63, 1, x_55);
lean::cnstr_set(x_63, 2, x_56);
lean::cnstr_set(x_63, 3, x_58);
lean::cnstr_set(x_63, 4, x_60);
if (lean::is_scalar(x_30)) {
 x_64 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_64 = x_30;
}
lean::cnstr_set(x_64, 0, x_36);
lean::cnstr_set(x_64, 1, x_18);
lean::cnstr_set(x_64, 2, x_20);
lean::cnstr_set(x_64, 3, x_22);
lean::cnstr_set(x_64, 4, x_24);
lean::cnstr_set(x_64, 5, x_26);
lean::cnstr_set(x_64, 6, x_28);
if (lean::is_scalar(x_10)) {
 x_65 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_65 = x_10;
}
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_63);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::apply_1(x_40, x_66);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
case 5:
{
obj* x_70; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_72 = x_6;
} else {
 lean::inc(x_70);
 lean::dec(x_6);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_79; 
lean::dec(x_5);
lean::dec(x_72);
lean::dec(x_70);
lean::dec(x_73);
x_79 = l_lean_expander_no__expansion___closed__1;
return x_79;
}
else
{
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_114; obj* x_115; obj* x_118; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_73);
x_81 = lean::cnstr_get(x_70, 1);
x_83 = lean::cnstr_get(x_70, 2);
x_85 = lean::cnstr_get(x_70, 3);
x_87 = lean::cnstr_get(x_70, 4);
x_89 = lean::cnstr_get(x_70, 5);
x_91 = lean::cnstr_get(x_70, 6);
x_93 = lean::cnstr_get(x_70, 7);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_95 = x_70;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_70);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_5, 0);
lean::inc(x_96);
lean::dec(x_5);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
x_101 = l_lean_expander_declaration_transform___closed__1;
x_102 = l_option_get__or__else___main___rarg(x_99, x_101);
lean::dec(x_99);
x_104 = lean::cnstr_get(x_2, 1);
lean::inc(x_104);
lean::dec(x_2);
x_107 = lean::cnstr_get(x_96, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_102, 1);
lean::inc(x_111);
x_113 = l_lean_expander_declaration_transform___closed__2;
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_111);
x_115 = lean::cnstr_get(x_102, 2);
lean::inc(x_115);
lean::dec(x_102);
x_118 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_118, 0, x_109);
lean::cnstr_set(x_118, 1, x_114);
lean::cnstr_set(x_118, 2, x_115);
x_119 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_119, 0, x_118);
x_120 = lean::cnstr_get(x_96, 2);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_96, 3);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_96, 4);
lean::inc(x_124);
lean::dec(x_96);
x_127 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_127, 0, x_107);
lean::cnstr_set(x_127, 1, x_119);
lean::cnstr_set(x_127, 2, x_120);
lean::cnstr_set(x_127, 3, x_122);
lean::cnstr_set(x_127, 4, x_124);
x_128 = l_lean_expander_declaration_transform___closed__3;
if (lean::is_scalar(x_95)) {
 x_129 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_129 = x_95;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_81);
lean::cnstr_set(x_129, 2, x_83);
lean::cnstr_set(x_129, 3, x_85);
lean::cnstr_set(x_129, 4, x_87);
lean::cnstr_set(x_129, 5, x_89);
lean::cnstr_set(x_129, 6, x_91);
lean::cnstr_set(x_129, 7, x_93);
if (lean::is_scalar(x_72)) {
 x_130 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_130 = x_72;
}
lean::cnstr_set(x_130, 0, x_129);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::apply_1(x_104, x_131);
x_133 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_133, 0, x_132);
x_134 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_134, 0, x_133);
return x_134;
}
}
default:
{
obj* x_137; 
lean::dec(x_6);
lean::dec(x_5);
x_137 = l_lean_expander_no__expansion___closed__1;
return x_137;
}
}
}
}
obj* l_lean_expander_declaration_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_declaration_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_4);
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
obj* l_lean_expander_intro__rule_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = l_lean_parser_command_intro__rule_has__view;
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
x_16 = l_lean_expander_no__expansion___closed__1;
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
x_24 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_17);
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
x_39 = l_lean_parser_term_pi_has__view;
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
lean::dec(x_39);
x_43 = lean::cnstr_get(x_20, 1);
lean::inc(x_43);
lean::dec(x_20);
x_46 = l_lean_expander_arrow_transform___closed__2;
x_47 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_28);
lean::cnstr_set(x_48, 2, x_47);
lean::cnstr_set(x_48, 3, x_43);
x_49 = lean::apply_1(x_40, x_48);
x_50 = l_lean_expander_mk__simple__binder___closed__1;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_49);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = l_lean_expander_constant_transform___closed__1;
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
x_62 = l_lean_expander_no__expansion___closed__1;
return x_62;
}
}
}
obj* l_lean_expander_intro__rule_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_intro__rule_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_variable_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("variables");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_variable_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_14; 
x_2 = l_lean_parser_command_variable_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_lean_parser_command_variables_has__view;
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
x_20 = l_lean_expander_variable_transform___closed__1;
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
x_29 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_30 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
x_35 = l_lean_expander_variable_transform___closed__1;
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
obj* l_lean_expander_variable_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_variable_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_binding__annotation__update() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("expander");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("binding_annotation_update");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
x_2 = l_option_map___rarg(x_1, x_0);
x_3 = lean::box(3);
x_4 = l_option_get__or__else___main___rarg(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_expander_binding__annotation__update;
x_9 = l_lean_parser_syntax_mk__node(x_8, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* _init_l_lean_expander_binding__annotation__update_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_expander_binding__annotation__update_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_expander_binding__annotation__update_has__view_x_27;
return x_0;
}
}
obj* _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::mk_string("dummy");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_term__parser__m_monad;
x_9 = l_lean_parser_term__parser__m_monad__except;
x_10 = l_lean_parser_term__parser__m_lean_parser_monad__parsec;
x_11 = l_lean_parser_term__parser__m_alternative;
x_12 = l_lean_expander_binding__annotation__update;
x_13 = l_lean_expander_binding__annotation__update_has__view;
x_14 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_lean_expander_binding__annotation__update_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("dummy");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_lean_expander_binding__annotation__update_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_expander_binding__annotation__update;
x_6 = l_lean_expander_binding__annotation__update_parser___closed__1;
x_7 = l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = l_lean_expander_binding__annotation__update_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::mk_string("dummy");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_6, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder___main___closed__4;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; 
lean::dec(x_10);
lean::dec(x_12);
x_16 = l_lean_expander_expand__bracketed__binder___main(x_3, x_1);
x_8 = x_16;
goto lbl_9;
}
else
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; 
x_22 = lean::cnstr_get(x_17, 2);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_24 = x_3;
} else {
 lean::dec(x_3);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_10, 0);
x_27 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 1);
 x_29 = x_10;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_10);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 1);
 lean::cnstr_release(x_17, 2);
 x_32 = x_17;
} else {
 lean::inc(x_30);
 lean::dec(x_17);
 x_32 = lean::box(0);
}
x_33 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set(x_34, 2, x_22);
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_34);
if (lean::is_scalar(x_29)) {
 x_36 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_36 = x_29;
}
lean::cnstr_set(x_36, 0, x_25);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set(x_36, 2, x_27);
if (lean::is_scalar(x_24)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_24;
}
lean::cnstr_set(x_37, 0, x_36);
x_38 = l_lean_expander_expand__bracketed__binder___main(x_37, x_1);
x_8 = x_38;
goto lbl_9;
}
else
{
obj* x_43; 
lean::dec(x_22);
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_19);
x_43 = l_lean_expander_expand__bracketed__binder___main(x_3, x_1);
x_8 = x_43;
goto lbl_9;
}
}
else
{
obj* x_48; 
lean::dec(x_10);
lean::dec(x_17);
lean::dec(x_19);
lean::dec(x_20);
x_48 = l_lean_expander_expand__bracketed__binder___main(x_3, x_1);
x_8 = x_48;
goto lbl_9;
}
}
}
default:
{
obj* x_49; 
x_49 = l_lean_expander_expand__bracketed__binder___main(x_3, x_1);
x_8 = x_49;
goto lbl_9;
}
}
lbl_9:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_52; obj* x_54; obj* x_55; 
lean::dec(x_7);
lean::dec(x_5);
x_52 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_54 = x_8;
} else {
 lean::inc(x_52);
 lean::dec(x_8);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
return x_55;
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_8, 0);
lean::inc(x_56);
lean::dec(x_8);
x_59 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_5, x_1);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_7);
lean::dec(x_56);
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
obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_68 = x_59;
} else {
 lean::inc(x_66);
 lean::dec(x_59);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_7;
}
lean::cnstr_set(x_69, 0, x_56);
lean::cnstr_set(x_69, 1, x_66);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
}
}
}
obj* l_lean_expander_variables_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_command_variables_has__view;
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
x_12 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_9, x_1);
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
x_24 = l_list_join___main___rarg(x_18);
if (lean::is_scalar(x_11)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_lean_expander_variable_transform___closed__1;
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
x_32 = l_lean_expander_no__expansion___closed__1;
return x_32;
}
}
}
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_variables_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_variables_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_level_leading_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = l_lean_parser_level_leading_has__view;
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
x_16 = l_lean_expander_no__expansion___closed__1;
return x_16;
}
}
}
}
obj* l_lean_expander_level_leading_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_level_leading_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_subtype_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("subtype");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_subtype_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_2 = l_lean_parser_term_subtype_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = l_lean_parser_term_lambda_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
x_15 = l_lean_expander_get__opt__type___main(x_13);
lean::dec(x_13);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_11, x_17, x_15);
lean::dec(x_15);
lean::dec(x_11);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::cnstr_get(x_6, 4);
lean::inc(x_22);
lean::dec(x_6);
x_25 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_26 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_21);
lean::cnstr_set(x_27, 2, x_26);
lean::cnstr_set(x_27, 3, x_22);
x_28 = lean::apply_1(x_8, x_27);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_lean_expander_subtype_transform___closed__1;
x_32 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_31, x_30);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
obj* l_lean_expander_subtype_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_subtype_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("universe");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1(obj* x_0) {
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
x_7 = l_lean_parser_command_universe_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_2);
x_13 = lean::apply_1(x_8, x_12);
x_14 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_4);
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
obj* l_lean_expander_universes_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_2 = l_lean_parser_command_universes_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::apply_1(x_3, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_7);
x_11 = l_lean_parser_no__kind;
x_12 = l_lean_parser_syntax_mk__node(x_11, x_10);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_12);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* l_lean_expander_universes_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_universes_transform(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_expander_sorry_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = lean::box(0);
x_1 = lean::mk_string("sorry_ax");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
x_4 = l_lean_parser_term_hole_has__view;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::box(0);
x_9 = lean::mk_string("_");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_5, x_12);
x_14 = lean::mk_string("bool");
x_15 = lean_name_mk_string(x_0, x_14);
x_16 = lean::mk_string("ff");
x_17 = lean_name_mk_string(x_15, x_16);
x_18 = l_lean_expander_glob__id(x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_3, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
obj* l_lean_expander_sorry_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_sorry_transform___closed__1;
return x_2;
}
}
obj* l_lean_expander_sorry_transform___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_sorry_transform(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_4, x_5);
x_0 = x_6;
x_1 = x_3;
goto _start;
}
}
}
obj* _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_0 = l_lean_parser_command_mixfix;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix_transform___boxed), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_lean_parser_command_reserve__mixfix;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_reserve__mixfix_transform___boxed), 2, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_lean_parser_term_bracketed__binders;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_bracketed__binders_transform___boxed), 2, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_term_lambda;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform___boxed), 2, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_term_pi;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform___boxed), 2, 0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_term_arrow;
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_arrow_transform___boxed), 2, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_term_paren;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_paren_transform___boxed), 2, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_term_assume;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_assume_transform___boxed), 2, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_term_if;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_if_transform___boxed), 2, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_term_let;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_let_transform___boxed), 2, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_constant;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_constant_transform___boxed), 2, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_declaration;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_declaration_transform___boxed), 2, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_intro__rule;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_intro__rule_transform___boxed), 2, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_variable;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variable_transform___boxed), 2, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command_variables;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variables_transform___boxed), 2, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_level_leading;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_level_leading_transform___boxed), 2, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_lean_parser_term_subtype;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_subtype_transform___boxed), 2, 0);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_lean_parser_command_universes;
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_universes_transform___boxed), 2, 0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_lean_parser_term_sorry;
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_sorry_transform___boxed), 2, 0);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_53);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_50);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_47);
lean::cnstr_set(x_61, 1, x_60);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_44);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_41);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_38);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_35);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_32);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_29);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_26);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_23);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_69);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_17);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_14);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_11);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_8);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_5);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_2);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::box(0);
x_78 = l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(x_77, x_76);
lean::dec(x_76);
return x_78;
}
}
obj* _init_l_lean_expander_builtin__transformers() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
return x_0;
}
}
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_expander__config_has__lift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_expander_expander__config_has__lift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_expander__config_has__lift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_expander__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_expander_expander__state_new() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(0u);
return x_0;
}
}
obj* l_lean_expander_mk__scope(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_0, x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_lean_expander_mk__scope___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_mk__scope(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; uint8 x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 2);
x_7 = l_lean_parser_syntax_get__pos(x_0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = l_lean_file__map_to__position(x_6, x_9);
lean::dec(x_9);
x_13 = lean::box(0);
x_14 = 2;
x_15 = l_string_join___closed__1;
lean::inc(x_1);
lean::inc(x_5);
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_18, 3, x_15);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_14);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_16 = l___private_init_lean_expander_2__expand__core___main(x_0, x_9, x_2, x_3);
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
x_33 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(x_0, x_11, x_30, x_3);
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
obj* l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_lean_parser_syntax_flip__scopes___main(x_10, x_3);
x_12 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_0, x_5);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_16 = l___private_init_lean_expander_2__expand__core___main(x_0, x_9, x_2, x_3);
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
x_33 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_0, x_11, x_30, x_3);
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
obj* _init_l___private_init_lean_expander_2__expand__core___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("macro expansion limit exceeded");
return x_0;
}
}
obj* l___private_init_lean_expander_2__expand__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_7; 
lean::inc(x_1);
x_7 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_0, x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
x_23 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_19, x_21);
lean::dec(x_19);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_13, 1);
lean::inc(x_25);
lean::dec(x_13);
x_28 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(x_17, x_25, x_2, x_3);
if (lean::obj_tag(x_28) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_21);
x_30 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_32 = x_28;
} else {
 lean::inc(x_30);
 lean::dec(x_28);
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_45; obj* x_46; 
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
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
x_42 = l_lean_parser_syntax_mk__node(x_21, x_37);
lean::dec(x_37);
lean::dec(x_21);
if (lean::is_scalar(x_41)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_41;
}
lean::cnstr_set(x_45, 0, x_42);
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
else
{
obj* x_47; obj* x_50; 
x_47 = lean::cnstr_get(x_23, 0);
lean::inc(x_47);
lean::dec(x_23);
x_50 = l_lean_expander_mk__scope(x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_50) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_47);
lean::dec(x_17);
lean::dec(x_21);
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
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
obj* x_61; obj* x_64; obj* x_66; obj* x_69; obj* x_73; obj* x_74; obj* x_76; obj* x_78; 
x_61 = lean::cnstr_get(x_50, 0);
lean::inc(x_61);
lean::dec(x_50);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_13, 1);
lean::inc(x_69);
lean::dec(x_13);
lean::inc(x_69);
x_73 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_64, x_69);
x_74 = l_lean_parser_syntax_mk__node(x_21, x_73);
lean::dec(x_73);
x_76 = lean::cnstr_get(x_3, 0);
lean::inc(x_76);
x_78 = lean::apply_2(x_47, x_74, x_76);
if (lean::obj_tag(x_78) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_3);
lean::dec(x_64);
lean::dec(x_66);
lean::dec(x_69);
lean::dec(x_17);
lean::dec(x_21);
x_85 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_87 = x_78;
} else {
 lean::inc(x_85);
 lean::dec(x_78);
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
obj* x_89; 
x_89 = lean::cnstr_get(x_78, 0);
lean::inc(x_89);
lean::dec(x_78);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; 
lean::dec(x_64);
x_93 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_17, x_69, x_66, x_3);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_21);
x_95 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_97 = x_93;
} else {
 lean::inc(x_95);
 lean::dec(x_93);
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
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_110; obj* x_111; 
x_99 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_101 = x_93;
} else {
 lean::inc(x_99);
 lean::dec(x_93);
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
x_107 = l_lean_parser_syntax_mk__node(x_21, x_102);
lean::dec(x_102);
lean::dec(x_21);
if (lean::is_scalar(x_106)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_106;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_104);
if (lean::is_scalar(x_101)) {
 x_111 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_111 = x_101;
}
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
}
else
{
obj* x_114; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_69);
lean::dec(x_21);
x_114 = lean::cnstr_get(x_89, 0);
lean::inc(x_114);
lean::dec(x_89);
x_117 = lean::box(0);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_64);
lean::cnstr_set(x_118, 1, x_117);
x_119 = l_lean_parser_syntax_flip__scopes___main(x_118, x_114);
x_0 = x_17;
x_1 = x_119;
x_2 = x_66;
goto _start;
}
}
}
}
}
}
else
{
obj* x_122; obj* x_123; 
lean::dec(x_0);
x_122 = l___private_init_lean_expander_2__expand__core___main___closed__1;
x_123 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_1, x_122, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_123;
}
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_expander_2__expand__core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_expander_2__expand__core___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_expander_expand(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1000u);
x_3 = l_lean_expander_expander__state_new;
x_4 = l___private_init_lean_expander_2__expand__core___main(x_2, x_0, x_3, x_1);
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
void initialize_init_lean_parser_module();
void initialize_init_lean_expr();
static bool _G_initialized = false;
void initialize_init_lean_expander() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_module();
 initialize_init_lean_expr();
 l_lean_expander_transform__m_monad = _init_l_lean_expander_transform__m_monad();
lean::mark_persistent(l_lean_expander_transform__m_monad);
 l_lean_expander_transform__m_monad__reader = _init_l_lean_expander_transform__m_monad__reader();
lean::mark_persistent(l_lean_expander_transform__m_monad__reader);
 l_lean_expander_transform__m_monad__except = _init_l_lean_expander_transform__m_monad__except();
lean::mark_persistent(l_lean_expander_transform__m_monad__except);
 l_lean_expander_transform__m = _init_l_lean_expander_transform__m();
lean::mark_persistent(l_lean_expander_transform__m);
 l_lean_expander_transformer = _init_l_lean_expander_transformer();
lean::mark_persistent(l_lean_expander_transformer);
 l_lean_expander_no__expansion___closed__1 = _init_l_lean_expander_no__expansion___closed__1();
lean::mark_persistent(l_lean_expander_no__expansion___closed__1);
 l_lean_expander_coe__binder__bracketed__binder___closed__1 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__1();
lean::mark_persistent(l_lean_expander_coe__binder__bracketed__binder___closed__1);
 l_lean_expander_coe__binder__bracketed__binder___closed__2 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__2();
lean::mark_persistent(l_lean_expander_coe__binder__bracketed__binder___closed__2);
 l___private_init_lean_expander_1__pop__stx__arg___closed__1 = _init_l___private_init_lean_expander_1__pop__stx__arg___closed__1();
lean::mark_persistent(l___private_init_lean_expander_1__pop__stx__arg___closed__1);
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1);
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2);
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3);
 l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1 = _init_l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1);
 l_lean_expander_mixfix__to__notation__spec___closed__1 = _init_l_lean_expander_mixfix__to__notation__spec___closed__1();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__1);
 l_lean_expander_mixfix__to__notation__spec___closed__2 = _init_l_lean_expander_mixfix__to__notation__spec___closed__2();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__2);
 l_lean_expander_mixfix__to__notation__spec___closed__3 = _init_l_lean_expander_mixfix__to__notation__spec___closed__3();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__3);
 l_lean_expander_mixfix__to__notation__spec___closed__4 = _init_l_lean_expander_mixfix__to__notation__spec___closed__4();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__4);
 l_lean_expander_mixfix__to__notation__spec___closed__5 = _init_l_lean_expander_mixfix__to__notation__spec___closed__5();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__5);
 l_lean_expander_mixfix__to__notation__spec___closed__6 = _init_l_lean_expander_mixfix__to__notation__spec___closed__6();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__6);
 l_lean_expander_mixfix_transform___closed__1 = _init_l_lean_expander_mixfix_transform___closed__1();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__1);
 l_lean_expander_mixfix_transform___closed__2 = _init_l_lean_expander_mixfix_transform___closed__2();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__2);
 l_lean_expander_mixfix_transform___closed__3 = _init_l_lean_expander_mixfix_transform___closed__3();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__3);
 l_lean_expander_mixfix_transform___closed__4 = _init_l_lean_expander_mixfix_transform___closed__4();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__4);
 l_lean_expander_mixfix_transform___closed__5 = _init_l_lean_expander_mixfix_transform___closed__5();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__5);
 l_lean_expander_mixfix_transform___closed__6 = _init_l_lean_expander_mixfix_transform___closed__6();
lean::mark_persistent(l_lean_expander_mixfix_transform___closed__6);
 l_lean_expander_reserve__mixfix_transform___closed__1 = _init_l_lean_expander_reserve__mixfix_transform___closed__1();
lean::mark_persistent(l_lean_expander_reserve__mixfix_transform___closed__1);
 l_lean_expander_mk__simple__binder___closed__1 = _init_l_lean_expander_mk__simple__binder___closed__1();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__1);
 l_lean_expander_mk__simple__binder___closed__2 = _init_l_lean_expander_mk__simple__binder___closed__2();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__2);
 l_lean_expander_mk__simple__binder___closed__3 = _init_l_lean_expander_mk__simple__binder___closed__3();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__3);
 l_lean_expander_mk__simple__binder___closed__4 = _init_l_lean_expander_mk__simple__binder___closed__4();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__4);
 l_lean_expander_mk__simple__binder___closed__5 = _init_l_lean_expander_mk__simple__binder___closed__5();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__5);
 l_lean_expander_mk__simple__binder___closed__6 = _init_l_lean_expander_mk__simple__binder___closed__6();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__6);
 l_lean_expander_mk__simple__binder___closed__7 = _init_l_lean_expander_mk__simple__binder___closed__7();
lean::mark_persistent(l_lean_expander_mk__simple__binder___closed__7);
 l_lean_expander_binder__ident__to__ident___main___closed__1 = _init_l_lean_expander_binder__ident__to__ident___main___closed__1();
lean::mark_persistent(l_lean_expander_binder__ident__to__ident___main___closed__1);
 l_lean_expander_get__opt__type___main___closed__1 = _init_l_lean_expander_get__opt__type___main___closed__1();
lean::mark_persistent(l_lean_expander_get__opt__type___main___closed__1);
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1();
lean::mark_persistent(l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1);
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1();
lean::mark_persistent(l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1);
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1();
lean::mark_persistent(l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1);
 l_lean_expander_expand__bracketed__binder___main___closed__1 = _init_l_lean_expander_expand__bracketed__binder___main___closed__1();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__1);
 l_lean_expander_expand__bracketed__binder___main___closed__2 = _init_l_lean_expander_expand__bracketed__binder___main___closed__2();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__2);
 l_lean_expander_expand__bracketed__binder___main___closed__3 = _init_l_lean_expander_expand__bracketed__binder___main___closed__3();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__3);
 l_lean_expander_expand__bracketed__binder___main___closed__4 = _init_l_lean_expander_expand__bracketed__binder___main___closed__4();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__4);
 l_lean_expander_expand__bracketed__binder___main___closed__5 = _init_l_lean_expander_expand__bracketed__binder___main___closed__5();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__5);
 l_lean_expander_expand__bracketed__binder___main___closed__6 = _init_l_lean_expander_expand__bracketed__binder___main___closed__6();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__6);
 l_lean_expander_expand__bracketed__binder___main___closed__7 = _init_l_lean_expander_expand__bracketed__binder___main___closed__7();
lean::mark_persistent(l_lean_expander_expand__bracketed__binder___main___closed__7);
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1();
lean::mark_persistent(l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1);
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2();
lean::mark_persistent(l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2);
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3();
lean::mark_persistent(l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3);
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4();
lean::mark_persistent(l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4);
 l_lean_expander_lambda_transform___closed__1 = _init_l_lean_expander_lambda_transform___closed__1();
lean::mark_persistent(l_lean_expander_lambda_transform___closed__1);
 l_lean_expander_arrow_transform___closed__1 = _init_l_lean_expander_arrow_transform___closed__1();
lean::mark_persistent(l_lean_expander_arrow_transform___closed__1);
 l_lean_expander_arrow_transform___closed__2 = _init_l_lean_expander_arrow_transform___closed__2();
lean::mark_persistent(l_lean_expander_arrow_transform___closed__2);
 l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1 = _init_l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1();
lean::mark_persistent(l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1);
 l_lean_expander_paren_transform___closed__1 = _init_l_lean_expander_paren_transform___closed__1();
lean::mark_persistent(l_lean_expander_paren_transform___closed__1);
 l_lean_expander_paren_transform___closed__2 = _init_l_lean_expander_paren_transform___closed__2();
lean::mark_persistent(l_lean_expander_paren_transform___closed__2);
 l_lean_expander_assume_transform___closed__1 = _init_l_lean_expander_assume_transform___closed__1();
lean::mark_persistent(l_lean_expander_assume_transform___closed__1);
 l_lean_expander_if_transform___closed__1 = _init_l_lean_expander_if_transform___closed__1();
lean::mark_persistent(l_lean_expander_if_transform___closed__1);
 l_lean_expander_if_transform___closed__2 = _init_l_lean_expander_if_transform___closed__2();
lean::mark_persistent(l_lean_expander_if_transform___closed__2);
 l_lean_expander_if_transform___closed__3 = _init_l_lean_expander_if_transform___closed__3();
lean::mark_persistent(l_lean_expander_if_transform___closed__3);
 l_lean_expander_let_transform___closed__1 = _init_l_lean_expander_let_transform___closed__1();
lean::mark_persistent(l_lean_expander_let_transform___closed__1);
 l_lean_expander_constant_transform___closed__1 = _init_l_lean_expander_constant_transform___closed__1();
lean::mark_persistent(l_lean_expander_constant_transform___closed__1);
 l_lean_expander_declaration_transform___closed__1 = _init_l_lean_expander_declaration_transform___closed__1();
lean::mark_persistent(l_lean_expander_declaration_transform___closed__1);
 l_lean_expander_declaration_transform___closed__2 = _init_l_lean_expander_declaration_transform___closed__2();
lean::mark_persistent(l_lean_expander_declaration_transform___closed__2);
 l_lean_expander_declaration_transform___closed__3 = _init_l_lean_expander_declaration_transform___closed__3();
lean::mark_persistent(l_lean_expander_declaration_transform___closed__3);
 l_lean_expander_variable_transform___closed__1 = _init_l_lean_expander_variable_transform___closed__1();
lean::mark_persistent(l_lean_expander_variable_transform___closed__1);
 l_lean_expander_binding__annotation__update = _init_l_lean_expander_binding__annotation__update();
lean::mark_persistent(l_lean_expander_binding__annotation__update);
 l_lean_expander_binding__annotation__update_has__view_x_27 = _init_l_lean_expander_binding__annotation__update_has__view_x_27();
lean::mark_persistent(l_lean_expander_binding__annotation__update_has__view_x_27);
 l_lean_expander_binding__annotation__update_has__view = _init_l_lean_expander_binding__annotation__update_has__view();
lean::mark_persistent(l_lean_expander_binding__annotation__update_has__view);
 l_lean_expander_binding__annotation__update_parser_lean_parser_has__view = _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_expander_binding__annotation__update_parser_lean_parser_has__view);
 l_lean_expander_binding__annotation__update_parser___closed__1 = _init_l_lean_expander_binding__annotation__update_parser___closed__1();
lean::mark_persistent(l_lean_expander_binding__annotation__update_parser___closed__1);
 l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1();
lean::mark_persistent(l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1);
 l_lean_expander_subtype_transform___closed__1 = _init_l_lean_expander_subtype_transform___closed__1();
lean::mark_persistent(l_lean_expander_subtype_transform___closed__1);
 l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1();
lean::mark_persistent(l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1);
 l_lean_expander_sorry_transform___closed__1 = _init_l_lean_expander_sorry_transform___closed__1();
lean::mark_persistent(l_lean_expander_sorry_transform___closed__1);
 l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1 = _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1();
lean::mark_persistent(l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1);
 l_lean_expander_builtin__transformers = _init_l_lean_expander_builtin__transformers();
lean::mark_persistent(l_lean_expander_builtin__transformers);
 l_lean_expander_expander__m = _init_l_lean_expander_expander__m();
lean::mark_persistent(l_lean_expander_expander__m);
 l_lean_expander_expander__state_new = _init_l_lean_expander_expander__state_new();
lean::mark_persistent(l_lean_expander_expander__state_new);
 l___private_init_lean_expander_2__expand__core___main___closed__1 = _init_l___private_init_lean_expander_2__expand__core___main___closed__1();
lean::mark_persistent(l___private_init_lean_expander_2__expand__core___main___closed__1);
}
