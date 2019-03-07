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
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
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
extern obj* l_lean_parser_command_universe_has__view;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj*);
extern obj* l_lean_parser_ident__univs;
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj*);
extern obj* l_lean_parser_term_sorry;
obj* l___private_init_lean_expander_1__pop__stx__arg(obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform___closed__1;
extern obj* l_lean_parser_command_intro__rule_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14___boxed(obj*, obj*);
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj*, obj*);
obj* l_lean_expander_bracketed__binders_transform(obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
obj* l_lean_expander_sorry_transform___boxed(obj*, obj*);
extern obj* l_lean_parser_command_variables_has__view;
obj* l_lean_expander_mk__simple__binder___closed__7;
obj* l_lean_expander_binding__annotation__update_parser___closed__1;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___boxed(obj*, obj*, obj*, obj*);
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
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_lean_expander_sorry_transform(obj*, obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___boxed(obj*, obj*);
obj* l_lean_expander_arrow_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj*, obj*);
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
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__2;
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_expander_binder__ident__to__ident(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main(obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_expander_declaration_transform___closed__3;
obj* l_lean_expander_error___boxed(obj*, obj*);
obj* l_except__t_monad___rarg(obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_lean_expander_expander__config_has__lift(obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1(obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj*, obj*);
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj*, obj*);
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj*, obj*);
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_subtype_transform___boxed(obj*, obj*);
obj* l_lean_expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_expander_mk__simple__binder___closed__6;
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj*);
extern obj* l_lean_parser_term_assume_has__view;
extern obj* l_lean_parser_command_intro__rule;
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj*);
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
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___boxed(obj*);
obj* l_lean_name_quick__lt(obj*, obj*);
obj* l_lean_expander_coe__binders__ext__binders(obj*);
obj* l_lean_expander_mixfix_transform(obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__7;
obj* l_lean_expander_paren_transform___closed__1;
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
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_lean_expander_constant_transform___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__4;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder(obj*);
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj*, obj*);
obj* l_lean_expander_no__expansion___closed__1;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
extern obj* l_lean_parser_term__parser__m_monad__except;
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6___boxed(obj*, obj*);
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
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_expander_constant_transform(obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___boxed(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
extern obj* l_lean_parser_term__parser__m_alternative;
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
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_19 = lean::box(0);
x_20 = 2;
x_21 = l_string_join___closed__1;
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_19);
lean::cnstr_set(x_22, 3, x_21);
lean::cnstr_set(x_22, 4, x_3);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_20);
x_23 = x_22;
x_24 = lean::apply_2(x_5, lean::box(0), x_23);
return x_24;
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
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_expander_coe__ident__binder__id(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
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
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_coe__simple__binder__binders(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
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
x_8 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_9 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_parser_syntax_get__pos(x_0);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_option_get__or__else___main___rarg(x_9, x_10);
lean::dec(x_9);
x_13 = l_lean_file__map_to__position(x_6, x_11);
x_14 = lean::box(0);
x_15 = 2;
x_16 = l_string_join___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_13);
lean::cnstr_set(x_17, 2, x_14);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set(x_17, 4, x_1);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_15);
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
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
x_7 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_4, x_6, x_0, x_1);
lean::dec(x_0);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 3);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_18);
lean::cnstr_set(x_23, 3, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
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
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_parser_syntax_get__pos(x_0);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
lean::dec(x_8);
x_12 = l_lean_file__map_to__position(x_5, x_10);
x_13 = lean::box(0);
x_14 = 2;
x_15 = l_string_join___closed__1;
x_16 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_13);
lean::cnstr_set(x_16, 3, x_15);
lean::cnstr_set(x_16, 4, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*5, x_14);
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
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
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
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_12 = x_1;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_24; 
x_22 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
x_24 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_22, x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_12);
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
obj* x_34; 
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
lean::dec(x_24);
x_13 = x_34;
goto lbl_14;
}
}
else
{
obj* x_40; 
lean::dec(x_12);
lean::dec(x_19);
lean::inc(x_3);
x_40 = l___private_init_lean_expander_1__pop__stx__arg(x_2, x_3);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_10);
x_44 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_46 = x_40;
} else {
 lean::inc(x_44);
 lean::dec(x_40);
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
obj* x_48; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_15 = x_48;
goto lbl_16;
}
}
lbl_14:
{
obj* x_51; 
x_51 = lean::cnstr_get(x_8, 1);
lean::inc(x_51);
lean::dec(x_8);
if (lean::obj_tag(x_51) == 0)
{
obj* x_55; 
lean::dec(x_12);
x_55 = lean::cnstr_get(x_13, 1);
lean::inc(x_55);
lean::dec(x_13);
x_1 = x_10;
x_2 = x_55;
goto _start;
}
else
{
obj* x_59; obj* x_61; 
x_59 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 x_61 = x_51;
} else {
 lean::inc(x_59);
 lean::dec(x_51);
 x_61 = lean::box(0);
}
switch (lean::obj_tag(x_59)) {
case 0:
{
obj* x_63; obj* x_67; 
lean::dec(x_59);
x_63 = lean::cnstr_get(x_13, 1);
lean::inc(x_63);
lean::dec(x_13);
lean::inc(x_3);
x_67 = l___private_init_lean_expander_1__pop__stx__arg(x_63, x_3);
if (lean::obj_tag(x_67) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_61);
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_12);
x_72 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_72);
 lean::dec(x_67);
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
obj* x_76; obj* x_79; obj* x_81; obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_76 = lean::cnstr_get(x_67, 0);
lean::inc(x_76);
lean::dec(x_67);
x_79 = lean::cnstr_get(x_76, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_76, 1);
lean::inc(x_81);
lean::dec(x_76);
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_81, 2);
lean::inc(x_88);
lean::dec(x_81);
x_91 = l_lean_parser_term_binder__ident_has__view;
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
lean::dec(x_91);
x_95 = lean::apply_1(x_92, x_79);
x_96 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_12;
}
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_96);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
if (lean::is_scalar(x_61)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_61;
}
lean::cnstr_set(x_101, 0, x_100);
x_102 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_102, 0, x_84);
lean::cnstr_set(x_102, 1, x_86);
lean::cnstr_set(x_102, 2, x_88);
lean::cnstr_set(x_102, 3, x_101);
x_1 = x_10;
x_2 = x_102;
goto _start;
}
}
case 1:
{
obj* x_106; obj* x_110; 
lean::dec(x_12);
lean::dec(x_59);
x_106 = lean::cnstr_get(x_13, 1);
lean::inc(x_106);
lean::dec(x_13);
lean::inc(x_3);
x_110 = l___private_init_lean_expander_1__pop__stx__arg(x_106, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_61);
lean::dec(x_3);
lean::dec(x_10);
x_114 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_116 = x_110;
} else {
 lean::inc(x_114);
 lean::dec(x_110);
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
obj* x_118; obj* x_121; obj* x_123; obj* x_126; obj* x_128; obj* x_130; obj* x_133; obj* x_134; obj* x_137; obj* x_138; obj* x_139; 
x_118 = lean::cnstr_get(x_110, 0);
lean::inc(x_118);
lean::dec(x_110);
x_121 = lean::cnstr_get(x_118, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_118, 1);
lean::inc(x_123);
lean::dec(x_118);
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_123, 2);
lean::inc(x_130);
lean::dec(x_123);
x_133 = l_lean_parser_term_binders_has__view;
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
lean::dec(x_133);
x_137 = lean::apply_1(x_134, x_121);
if (lean::is_scalar(x_61)) {
 x_138 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_138 = x_61;
}
lean::cnstr_set(x_138, 0, x_137);
x_139 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_139, 0, x_126);
lean::cnstr_set(x_139, 1, x_128);
lean::cnstr_set(x_139, 2, x_130);
lean::cnstr_set(x_139, 3, x_138);
x_1 = x_10;
x_2 = x_139;
goto _start;
}
}
default:
{
obj* x_142; obj* x_145; 
lean::dec(x_61);
x_142 = lean::cnstr_get(x_59, 0);
lean::inc(x_142);
lean::dec(x_59);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
if (lean::obj_tag(x_145) == 0)
{
obj* x_147; obj* x_150; obj* x_154; 
x_147 = lean::cnstr_get(x_13, 1);
lean::inc(x_147);
lean::dec(x_13);
x_150 = lean::cnstr_get(x_142, 0);
lean::inc(x_150);
lean::dec(x_142);
lean::inc(x_3);
x_154 = l___private_init_lean_expander_1__pop__stx__arg(x_147, x_3);
if (lean::obj_tag(x_154) == 0)
{
obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_150);
x_159 = lean::cnstr_get(x_154, 0);
if (lean::is_exclusive(x_154)) {
 x_161 = x_154;
} else {
 lean::inc(x_159);
 lean::dec(x_154);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
return x_162;
}
else
{
obj* x_163; obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_173; obj* x_175; obj* x_176; obj* x_178; obj* x_179; obj* x_182; 
x_163 = lean::cnstr_get(x_154, 0);
lean::inc(x_163);
lean::dec(x_154);
x_166 = lean::cnstr_get(x_163, 0);
x_168 = lean::cnstr_get(x_163, 1);
if (lean::is_exclusive(x_163)) {
 x_170 = x_163;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_163);
 x_170 = lean::box(0);
}
x_171 = lean::cnstr_get(x_168, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_168, 1);
lean::inc(x_173);
if (lean::is_scalar(x_170)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_170;
}
lean::cnstr_set(x_175, 0, x_150);
lean::cnstr_set(x_175, 1, x_166);
x_176 = lean::cnstr_get(x_168, 2);
lean::inc(x_176);
if (lean::is_scalar(x_12)) {
 x_178 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_178 = x_12;
}
lean::cnstr_set(x_178, 0, x_175);
lean::cnstr_set(x_178, 1, x_176);
x_179 = lean::cnstr_get(x_168, 3);
lean::inc(x_179);
lean::dec(x_168);
x_182 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_182, 0, x_171);
lean::cnstr_set(x_182, 1, x_173);
lean::cnstr_set(x_182, 2, x_178);
lean::cnstr_set(x_182, 3, x_179);
x_1 = x_10;
x_2 = x_182;
goto _start;
}
}
else
{
obj* x_184; obj* x_187; 
x_184 = lean::cnstr_get(x_145, 0);
lean::inc(x_184);
lean::dec(x_145);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
lean::dec(x_184);
switch (lean::obj_tag(x_187)) {
case 0:
{
obj* x_191; obj* x_194; obj* x_198; 
lean::dec(x_187);
x_191 = lean::cnstr_get(x_13, 1);
lean::inc(x_191);
lean::dec(x_13);
x_194 = lean::cnstr_get(x_142, 0);
lean::inc(x_194);
lean::dec(x_142);
lean::inc(x_3);
x_198 = l___private_init_lean_expander_1__pop__stx__arg(x_191, x_3);
if (lean::obj_tag(x_198) == 0)
{
obj* x_203; obj* x_205; obj* x_206; 
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_194);
x_203 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 x_205 = x_198;
} else {
 lean::inc(x_203);
 lean::dec(x_198);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_203);
return x_206;
}
else
{
obj* x_207; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_223; obj* x_226; 
x_207 = lean::cnstr_get(x_198, 0);
lean::inc(x_207);
lean::dec(x_198);
x_210 = lean::cnstr_get(x_207, 0);
x_212 = lean::cnstr_get(x_207, 1);
if (lean::is_exclusive(x_207)) {
 x_214 = x_207;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::dec(x_207);
 x_214 = lean::box(0);
}
x_215 = lean::cnstr_get(x_212, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 1);
lean::inc(x_217);
if (lean::is_scalar(x_214)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_214;
}
lean::cnstr_set(x_219, 0, x_194);
lean::cnstr_set(x_219, 1, x_210);
x_220 = lean::cnstr_get(x_212, 2);
lean::inc(x_220);
if (lean::is_scalar(x_12)) {
 x_222 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_222 = x_12;
}
lean::cnstr_set(x_222, 0, x_219);
lean::cnstr_set(x_222, 1, x_220);
x_223 = lean::cnstr_get(x_212, 3);
lean::inc(x_223);
lean::dec(x_212);
x_226 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_226, 0, x_215);
lean::cnstr_set(x_226, 1, x_217);
lean::cnstr_set(x_226, 2, x_222);
lean::cnstr_set(x_226, 3, x_223);
x_1 = x_10;
x_2 = x_226;
goto _start;
}
}
case 2:
{
obj* x_228; obj* x_231; obj* x_234; obj* x_238; 
x_228 = lean::cnstr_get(x_13, 1);
lean::inc(x_228);
lean::dec(x_13);
x_231 = lean::cnstr_get(x_142, 0);
lean::inc(x_231);
lean::dec(x_142);
x_234 = lean::cnstr_get(x_187, 0);
lean::inc(x_234);
lean::dec(x_187);
lean::inc(x_3);
x_238 = l___private_init_lean_expander_1__pop__stx__arg(x_228, x_3);
if (lean::obj_tag(x_238) == 0)
{
obj* x_244; obj* x_246; obj* x_247; 
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_231);
lean::dec(x_234);
x_244 = lean::cnstr_get(x_238, 0);
if (lean::is_exclusive(x_238)) {
 x_246 = x_238;
} else {
 lean::inc(x_244);
 lean::dec(x_238);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_244);
return x_247;
}
else
{
obj* x_248; obj* x_251; obj* x_253; 
x_248 = lean::cnstr_get(x_238, 0);
lean::inc(x_248);
lean::dec(x_238);
x_251 = lean::cnstr_get(x_248, 1);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_251, 3);
lean::inc(x_253);
if (lean::obj_tag(x_253) == 0)
{
obj* x_259; obj* x_261; 
lean::dec(x_12);
lean::dec(x_231);
lean::dec(x_234);
lean::dec(x_248);
x_259 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
x_261 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_259, x_251, x_3);
lean::dec(x_251);
if (lean::obj_tag(x_261) == 0)
{
obj* x_265; obj* x_267; obj* x_268; 
lean::dec(x_3);
lean::dec(x_10);
x_265 = lean::cnstr_get(x_261, 0);
if (lean::is_exclusive(x_261)) {
 x_267 = x_261;
} else {
 lean::inc(x_265);
 lean::dec(x_261);
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
obj* x_269; obj* x_272; 
x_269 = lean::cnstr_get(x_261, 0);
lean::inc(x_269);
lean::dec(x_261);
x_272 = lean::cnstr_get(x_269, 1);
lean::inc(x_272);
lean::dec(x_269);
x_1 = x_10;
x_2 = x_272;
goto _start;
}
}
else
{
obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_286; obj* x_288; obj* x_289; obj* x_292; obj* x_293; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_303; obj* x_304; obj* x_305; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; 
x_276 = lean::cnstr_get(x_248, 0);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 1);
 x_278 = x_248;
} else {
 lean::inc(x_276);
 lean::dec(x_248);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_251, 0);
x_281 = lean::cnstr_get(x_251, 1);
x_283 = lean::cnstr_get(x_251, 2);
if (lean::is_exclusive(x_251)) {
 lean::cnstr_release(x_251, 3);
 x_285 = x_251;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::dec(x_251);
 x_285 = lean::box(0);
}
x_286 = lean::cnstr_get(x_253, 0);
lean::inc(x_286);
x_288 = l_lean_parser_term_lambda_has__view;
x_289 = lean::cnstr_get(x_288, 1);
lean::inc(x_289);
lean::dec(x_288);
x_292 = lean::box(0);
x_293 = lean::cnstr_get(x_234, 3);
lean::inc(x_293);
x_295 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_296 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_296 = x_12;
}
lean::cnstr_set(x_296, 0, x_293);
lean::cnstr_set(x_296, 1, x_295);
x_297 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_296);
x_298 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_292);
x_299 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_299, 0, x_298);
x_300 = lean::cnstr_get(x_234, 5);
lean::inc(x_300);
lean::dec(x_234);
x_303 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_304 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
x_310 = l_lean_parser_term_app_has__view;
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
lean::cnstr_set(x_316, 0, x_231);
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
lean::cnstr_set(x_318, 3, x_253);
x_1 = x_10;
x_2 = x_318;
goto _start;
}
}
}
default:
{
obj* x_323; obj* x_326; obj* x_328; 
lean::dec(x_12);
lean::dec(x_142);
lean::dec(x_187);
x_323 = lean::cnstr_get(x_13, 1);
lean::inc(x_323);
lean::dec(x_13);
x_326 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
x_328 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_326, x_323, x_3);
lean::dec(x_323);
if (lean::obj_tag(x_328) == 0)
{
obj* x_332; obj* x_334; obj* x_335; 
lean::dec(x_3);
lean::dec(x_10);
x_332 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_334 = x_328;
} else {
 lean::inc(x_332);
 lean::dec(x_328);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_332);
return x_335;
}
else
{
obj* x_336; obj* x_339; 
x_336 = lean::cnstr_get(x_328, 0);
lean::inc(x_336);
lean::dec(x_328);
x_339 = lean::cnstr_get(x_336, 1);
lean::inc(x_339);
lean::dec(x_336);
x_1 = x_10;
x_2 = x_339;
goto _start;
}
}
}
}
}
}
}
}
lbl_16:
{
obj* x_343; 
x_343 = lean::cnstr_get(x_8, 1);
lean::inc(x_343);
lean::dec(x_8);
if (lean::obj_tag(x_343) == 0)
{
obj* x_346; 
x_346 = lean::cnstr_get(x_15, 1);
lean::inc(x_346);
lean::dec(x_15);
x_1 = x_10;
x_2 = x_346;
goto _start;
}
else
{
obj* x_350; obj* x_352; 
x_350 = lean::cnstr_get(x_343, 0);
if (lean::is_exclusive(x_343)) {
 lean::cnstr_set(x_343, 0, lean::box(0));
 x_352 = x_343;
} else {
 lean::inc(x_350);
 lean::dec(x_343);
 x_352 = lean::box(0);
}
switch (lean::obj_tag(x_350)) {
case 0:
{
obj* x_354; obj* x_358; 
lean::dec(x_350);
x_354 = lean::cnstr_get(x_15, 1);
lean::inc(x_354);
lean::dec(x_15);
lean::inc(x_3);
x_358 = l___private_init_lean_expander_1__pop__stx__arg(x_354, x_3);
if (lean::obj_tag(x_358) == 0)
{
obj* x_362; obj* x_364; obj* x_365; 
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_352);
x_362 = lean::cnstr_get(x_358, 0);
if (lean::is_exclusive(x_358)) {
 x_364 = x_358;
} else {
 lean::inc(x_362);
 lean::dec(x_358);
 x_364 = lean::box(0);
}
if (lean::is_scalar(x_364)) {
 x_365 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_365 = x_364;
}
lean::cnstr_set(x_365, 0, x_362);
return x_365;
}
else
{
obj* x_366; obj* x_369; obj* x_371; obj* x_374; obj* x_376; obj* x_378; obj* x_381; obj* x_382; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
x_366 = lean::cnstr_get(x_358, 0);
lean::inc(x_366);
lean::dec(x_358);
x_369 = lean::cnstr_get(x_366, 0);
lean::inc(x_369);
x_371 = lean::cnstr_get(x_366, 1);
lean::inc(x_371);
lean::dec(x_366);
x_374 = lean::cnstr_get(x_371, 0);
lean::inc(x_374);
x_376 = lean::cnstr_get(x_371, 1);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_371, 2);
lean::inc(x_378);
lean::dec(x_371);
x_381 = l_lean_parser_term_binder__ident_has__view;
x_382 = lean::cnstr_get(x_381, 0);
lean::inc(x_382);
lean::dec(x_381);
x_385 = lean::apply_1(x_382, x_369);
x_386 = lean::box(0);
x_387 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_387, 0, x_385);
lean::cnstr_set(x_387, 1, x_386);
x_388 = lean::box(0);
x_389 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_389, 0, x_387);
lean::cnstr_set(x_389, 1, x_388);
x_390 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_390, 0, x_389);
if (lean::is_scalar(x_352)) {
 x_391 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_391 = x_352;
}
lean::cnstr_set(x_391, 0, x_390);
x_392 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_392, 0, x_374);
lean::cnstr_set(x_392, 1, x_376);
lean::cnstr_set(x_392, 2, x_378);
lean::cnstr_set(x_392, 3, x_391);
x_1 = x_10;
x_2 = x_392;
goto _start;
}
}
case 1:
{
obj* x_395; obj* x_399; 
lean::dec(x_350);
x_395 = lean::cnstr_get(x_15, 1);
lean::inc(x_395);
lean::dec(x_15);
lean::inc(x_3);
x_399 = l___private_init_lean_expander_1__pop__stx__arg(x_395, x_3);
if (lean::obj_tag(x_399) == 0)
{
obj* x_403; obj* x_405; obj* x_406; 
lean::dec(x_3);
lean::dec(x_10);
lean::dec(x_352);
x_403 = lean::cnstr_get(x_399, 0);
if (lean::is_exclusive(x_399)) {
 x_405 = x_399;
} else {
 lean::inc(x_403);
 lean::dec(x_399);
 x_405 = lean::box(0);
}
if (lean::is_scalar(x_405)) {
 x_406 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_406 = x_405;
}
lean::cnstr_set(x_406, 0, x_403);
return x_406;
}
else
{
obj* x_407; obj* x_410; obj* x_412; obj* x_415; obj* x_417; obj* x_419; obj* x_422; obj* x_423; obj* x_426; obj* x_427; obj* x_428; 
x_407 = lean::cnstr_get(x_399, 0);
lean::inc(x_407);
lean::dec(x_399);
x_410 = lean::cnstr_get(x_407, 0);
lean::inc(x_410);
x_412 = lean::cnstr_get(x_407, 1);
lean::inc(x_412);
lean::dec(x_407);
x_415 = lean::cnstr_get(x_412, 0);
lean::inc(x_415);
x_417 = lean::cnstr_get(x_412, 1);
lean::inc(x_417);
x_419 = lean::cnstr_get(x_412, 2);
lean::inc(x_419);
lean::dec(x_412);
x_422 = l_lean_parser_term_binders_has__view;
x_423 = lean::cnstr_get(x_422, 0);
lean::inc(x_423);
lean::dec(x_422);
x_426 = lean::apply_1(x_423, x_410);
if (lean::is_scalar(x_352)) {
 x_427 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_427 = x_352;
}
lean::cnstr_set(x_427, 0, x_426);
x_428 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_428, 0, x_415);
lean::cnstr_set(x_428, 1, x_417);
lean::cnstr_set(x_428, 2, x_419);
lean::cnstr_set(x_428, 3, x_427);
x_1 = x_10;
x_2 = x_428;
goto _start;
}
}
default:
{
obj* x_431; obj* x_434; 
lean::dec(x_352);
x_431 = lean::cnstr_get(x_350, 0);
lean::inc(x_431);
lean::dec(x_350);
x_434 = lean::cnstr_get(x_431, 1);
lean::inc(x_434);
if (lean::obj_tag(x_434) == 0)
{
obj* x_436; obj* x_439; obj* x_443; 
x_436 = lean::cnstr_get(x_15, 1);
lean::inc(x_436);
lean::dec(x_15);
x_439 = lean::cnstr_get(x_431, 0);
lean::inc(x_439);
lean::dec(x_431);
lean::inc(x_3);
x_443 = l___private_init_lean_expander_1__pop__stx__arg(x_436, x_3);
if (lean::obj_tag(x_443) == 0)
{
obj* x_447; obj* x_449; obj* x_450; 
lean::dec(x_439);
lean::dec(x_3);
lean::dec(x_10);
x_447 = lean::cnstr_get(x_443, 0);
if (lean::is_exclusive(x_443)) {
 x_449 = x_443;
} else {
 lean::inc(x_447);
 lean::dec(x_443);
 x_449 = lean::box(0);
}
if (lean::is_scalar(x_449)) {
 x_450 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_450 = x_449;
}
lean::cnstr_set(x_450, 0, x_447);
return x_450;
}
else
{
obj* x_451; obj* x_454; obj* x_456; obj* x_458; obj* x_459; obj* x_461; obj* x_463; obj* x_464; obj* x_466; obj* x_467; obj* x_470; 
x_451 = lean::cnstr_get(x_443, 0);
lean::inc(x_451);
lean::dec(x_443);
x_454 = lean::cnstr_get(x_451, 0);
x_456 = lean::cnstr_get(x_451, 1);
if (lean::is_exclusive(x_451)) {
 x_458 = x_451;
} else {
 lean::inc(x_454);
 lean::inc(x_456);
 lean::dec(x_451);
 x_458 = lean::box(0);
}
x_459 = lean::cnstr_get(x_456, 0);
lean::inc(x_459);
x_461 = lean::cnstr_get(x_456, 1);
lean::inc(x_461);
if (lean::is_scalar(x_458)) {
 x_463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_463 = x_458;
}
lean::cnstr_set(x_463, 0, x_439);
lean::cnstr_set(x_463, 1, x_454);
x_464 = lean::cnstr_get(x_456, 2);
lean::inc(x_464);
x_466 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_466, 0, x_463);
lean::cnstr_set(x_466, 1, x_464);
x_467 = lean::cnstr_get(x_456, 3);
lean::inc(x_467);
lean::dec(x_456);
x_470 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_470, 0, x_459);
lean::cnstr_set(x_470, 1, x_461);
lean::cnstr_set(x_470, 2, x_466);
lean::cnstr_set(x_470, 3, x_467);
x_1 = x_10;
x_2 = x_470;
goto _start;
}
}
else
{
obj* x_472; obj* x_475; 
x_472 = lean::cnstr_get(x_434, 0);
lean::inc(x_472);
lean::dec(x_434);
x_475 = lean::cnstr_get(x_472, 1);
lean::inc(x_475);
lean::dec(x_472);
switch (lean::obj_tag(x_475)) {
case 0:
{
obj* x_479; obj* x_482; obj* x_486; 
lean::dec(x_475);
x_479 = lean::cnstr_get(x_15, 1);
lean::inc(x_479);
lean::dec(x_15);
x_482 = lean::cnstr_get(x_431, 0);
lean::inc(x_482);
lean::dec(x_431);
lean::inc(x_3);
x_486 = l___private_init_lean_expander_1__pop__stx__arg(x_479, x_3);
if (lean::obj_tag(x_486) == 0)
{
obj* x_490; obj* x_492; obj* x_493; 
lean::dec(x_482);
lean::dec(x_3);
lean::dec(x_10);
x_490 = lean::cnstr_get(x_486, 0);
if (lean::is_exclusive(x_486)) {
 x_492 = x_486;
} else {
 lean::inc(x_490);
 lean::dec(x_486);
 x_492 = lean::box(0);
}
if (lean::is_scalar(x_492)) {
 x_493 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_493 = x_492;
}
lean::cnstr_set(x_493, 0, x_490);
return x_493;
}
else
{
obj* x_494; obj* x_497; obj* x_499; obj* x_501; obj* x_502; obj* x_504; obj* x_506; obj* x_507; obj* x_509; obj* x_510; obj* x_513; 
x_494 = lean::cnstr_get(x_486, 0);
lean::inc(x_494);
lean::dec(x_486);
x_497 = lean::cnstr_get(x_494, 0);
x_499 = lean::cnstr_get(x_494, 1);
if (lean::is_exclusive(x_494)) {
 x_501 = x_494;
} else {
 lean::inc(x_497);
 lean::inc(x_499);
 lean::dec(x_494);
 x_501 = lean::box(0);
}
x_502 = lean::cnstr_get(x_499, 0);
lean::inc(x_502);
x_504 = lean::cnstr_get(x_499, 1);
lean::inc(x_504);
if (lean::is_scalar(x_501)) {
 x_506 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_506 = x_501;
}
lean::cnstr_set(x_506, 0, x_482);
lean::cnstr_set(x_506, 1, x_497);
x_507 = lean::cnstr_get(x_499, 2);
lean::inc(x_507);
x_509 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_509, 0, x_506);
lean::cnstr_set(x_509, 1, x_507);
x_510 = lean::cnstr_get(x_499, 3);
lean::inc(x_510);
lean::dec(x_499);
x_513 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_513, 0, x_502);
lean::cnstr_set(x_513, 1, x_504);
lean::cnstr_set(x_513, 2, x_509);
lean::cnstr_set(x_513, 3, x_510);
x_1 = x_10;
x_2 = x_513;
goto _start;
}
}
case 2:
{
obj* x_515; obj* x_518; obj* x_521; obj* x_525; 
x_515 = lean::cnstr_get(x_15, 1);
lean::inc(x_515);
lean::dec(x_15);
x_518 = lean::cnstr_get(x_431, 0);
lean::inc(x_518);
lean::dec(x_431);
x_521 = lean::cnstr_get(x_475, 0);
lean::inc(x_521);
lean::dec(x_475);
lean::inc(x_3);
x_525 = l___private_init_lean_expander_1__pop__stx__arg(x_515, x_3);
if (lean::obj_tag(x_525) == 0)
{
obj* x_530; obj* x_532; obj* x_533; 
lean::dec(x_518);
lean::dec(x_521);
lean::dec(x_3);
lean::dec(x_10);
x_530 = lean::cnstr_get(x_525, 0);
if (lean::is_exclusive(x_525)) {
 x_532 = x_525;
} else {
 lean::inc(x_530);
 lean::dec(x_525);
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
obj* x_534; obj* x_537; obj* x_539; 
x_534 = lean::cnstr_get(x_525, 0);
lean::inc(x_534);
lean::dec(x_525);
x_537 = lean::cnstr_get(x_534, 1);
lean::inc(x_537);
x_539 = lean::cnstr_get(x_537, 3);
lean::inc(x_539);
if (lean::obj_tag(x_539) == 0)
{
obj* x_544; obj* x_546; 
lean::dec(x_518);
lean::dec(x_521);
lean::dec(x_534);
x_544 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
x_546 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_544, x_537, x_3);
lean::dec(x_537);
if (lean::obj_tag(x_546) == 0)
{
obj* x_550; obj* x_552; obj* x_553; 
lean::dec(x_3);
lean::dec(x_10);
x_550 = lean::cnstr_get(x_546, 0);
if (lean::is_exclusive(x_546)) {
 x_552 = x_546;
} else {
 lean::inc(x_550);
 lean::dec(x_546);
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
x_554 = lean::cnstr_get(x_546, 0);
lean::inc(x_554);
lean::dec(x_546);
x_557 = lean::cnstr_get(x_554, 1);
lean::inc(x_557);
lean::dec(x_554);
x_1 = x_10;
x_2 = x_557;
goto _start;
}
}
else
{
obj* x_561; obj* x_563; obj* x_564; obj* x_566; obj* x_568; obj* x_570; obj* x_571; obj* x_573; obj* x_574; obj* x_577; obj* x_578; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; obj* x_585; obj* x_588; obj* x_589; obj* x_590; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; 
x_561 = lean::cnstr_get(x_534, 0);
if (lean::is_exclusive(x_534)) {
 lean::cnstr_release(x_534, 1);
 x_563 = x_534;
} else {
 lean::inc(x_561);
 lean::dec(x_534);
 x_563 = lean::box(0);
}
x_564 = lean::cnstr_get(x_537, 0);
x_566 = lean::cnstr_get(x_537, 1);
x_568 = lean::cnstr_get(x_537, 2);
if (lean::is_exclusive(x_537)) {
 lean::cnstr_release(x_537, 3);
 x_570 = x_537;
} else {
 lean::inc(x_564);
 lean::inc(x_566);
 lean::inc(x_568);
 lean::dec(x_537);
 x_570 = lean::box(0);
}
x_571 = lean::cnstr_get(x_539, 0);
lean::inc(x_571);
x_573 = l_lean_parser_term_lambda_has__view;
x_574 = lean::cnstr_get(x_573, 1);
lean::inc(x_574);
lean::dec(x_573);
x_577 = lean::box(0);
x_578 = lean::cnstr_get(x_521, 3);
lean::inc(x_578);
x_580 = lean::box(0);
x_581 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_581, 0, x_578);
lean::cnstr_set(x_581, 1, x_580);
x_582 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_581);
x_583 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_583, 0, x_582);
lean::cnstr_set(x_583, 1, x_577);
x_584 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_584, 0, x_583);
x_585 = lean::cnstr_get(x_521, 5);
lean::inc(x_585);
lean::dec(x_521);
x_588 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_589 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_590 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_590, 0, x_588);
lean::cnstr_set(x_590, 1, x_584);
lean::cnstr_set(x_590, 2, x_589);
lean::cnstr_set(x_590, 3, x_585);
lean::inc(x_574);
x_592 = lean::apply_1(x_574, x_590);
x_593 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_593, 0, x_588);
lean::cnstr_set(x_593, 1, x_571);
lean::cnstr_set(x_593, 2, x_589);
lean::cnstr_set(x_593, 3, x_561);
x_594 = lean::apply_1(x_574, x_593);
x_595 = l_lean_parser_term_app_has__view;
x_596 = lean::cnstr_get(x_595, 1);
lean::inc(x_596);
lean::dec(x_595);
x_599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_599, 0, x_592);
lean::cnstr_set(x_599, 1, x_594);
x_600 = lean::apply_1(x_596, x_599);
if (lean::is_scalar(x_563)) {
 x_601 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_601 = x_563;
}
lean::cnstr_set(x_601, 0, x_518);
lean::cnstr_set(x_601, 1, x_600);
x_602 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_602, 0, x_601);
lean::cnstr_set(x_602, 1, x_568);
if (lean::is_scalar(x_570)) {
 x_603 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_603 = x_570;
}
lean::cnstr_set(x_603, 0, x_564);
lean::cnstr_set(x_603, 1, x_566);
lean::cnstr_set(x_603, 2, x_602);
lean::cnstr_set(x_603, 3, x_539);
x_1 = x_10;
x_2 = x_603;
goto _start;
}
}
}
default:
{
obj* x_607; obj* x_610; obj* x_612; 
lean::dec(x_475);
lean::dec(x_431);
x_607 = lean::cnstr_get(x_15, 1);
lean::inc(x_607);
lean::dec(x_15);
x_610 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
x_612 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_610, x_607, x_3);
lean::dec(x_607);
if (lean::obj_tag(x_612) == 0)
{
obj* x_616; obj* x_618; obj* x_619; 
lean::dec(x_3);
lean::dec(x_10);
x_616 = lean::cnstr_get(x_612, 0);
if (lean::is_exclusive(x_612)) {
 x_618 = x_612;
} else {
 lean::inc(x_616);
 lean::dec(x_612);
 x_618 = lean::box(0);
}
if (lean::is_scalar(x_618)) {
 x_619 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_619 = x_618;
}
lean::cnstr_set(x_619, 0, x_616);
return x_619;
}
else
{
obj* x_620; obj* x_623; 
x_620 = lean::cnstr_get(x_612, 0);
lean::inc(x_620);
lean::dec(x_612);
x_623 = lean::cnstr_get(x_620, 1);
lean::inc(x_623);
lean::dec(x_620);
x_1 = x_10;
x_2 = x_623;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean_name_dec_eq(x_8, x_1);
lean::dec(x_8);
if (x_13 == 0)
{
lean::dec(x_10);
x_0 = x_5;
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
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_10, 2);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_13);
lean::dec(x_13);
return x_16;
}
else
{
obj* x_21; 
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_0);
x_21 = lean::box(0);
return x_21;
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
obj* x_30; obj* x_34; 
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
lean::dec(x_24);
lean::inc(x_2);
x_34 = l___private_init_lean_expander_1__pop__stx__arg(x_18, x_2);
if (lean::obj_tag(x_34) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_19);
lean::dec(x_22);
x_41 = lean::cnstr_get(x_34, 0);
if (lean::is_exclusive(x_34)) {
 x_43 = x_34;
} else {
 lean::inc(x_41);
 lean::dec(x_34);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; 
x_45 = lean::cnstr_get(x_34, 0);
lean::inc(x_45);
lean::dec(x_34);
x_48 = lean::cnstr_get(x_45, 0);
x_50 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 x_52 = x_45;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_45);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
if (lean::is_scalar(x_52)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_52;
}
lean::cnstr_set(x_57, 0, x_30);
lean::cnstr_set(x_57, 1, x_48);
x_58 = lean::cnstr_get(x_50, 2);
lean::inc(x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_58);
x_61 = lean::cnstr_get(x_50, 3);
lean::inc(x_61);
lean::dec(x_50);
x_64 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_64, 0, x_53);
lean::cnstr_set(x_64, 1, x_55);
lean::cnstr_set(x_64, 2, x_60);
lean::cnstr_set(x_64, 3, x_61);
x_65 = lean::box(0);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
x_26 = x_66;
goto lbl_27;
}
}
lbl_27:
{
obj* x_67; obj* x_70; obj* x_73; 
x_67 = lean::cnstr_get(x_26, 1);
lean::inc(x_67);
lean::dec(x_26);
x_70 = lean::cnstr_get(x_22, 1);
lean::inc(x_70);
lean::dec(x_22);
x_73 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_70, x_67, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_73) == 0)
{
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_11);
lean::dec(x_19);
x_77 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_79 = x_73;
} else {
 lean::inc(x_77);
 lean::dec(x_73);
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
obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; 
x_81 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_83 = x_73;
} else {
 lean::inc(x_81);
 lean::dec(x_73);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
lean::dec(x_81);
x_87 = lean::cnstr_get(x_84, 2);
lean::inc(x_87);
lean::dec(x_84);
x_90 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_87);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1), 2, 1);
lean::closure_set(x_91, 0, x_90);
x_92 = lean::cnstr_get(x_19, 4);
lean::inc(x_92);
lean::dec(x_19);
x_95 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_91, x_92);
if (lean::is_scalar(x_11)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_11;
}
lean::cnstr_set(x_96, 0, x_95);
if (lean::is_scalar(x_83)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_83;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
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
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_1);
lean::dec(x_1);
return x_2;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__4() {
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__6() {
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
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__7() {
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
obj* x_10; obj* x_11; 
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = l_lean_expander_mixfix__to__notation__spec___closed__5;
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
x_24 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = l_lean_expander_mixfix__to__notation__spec___closed__6;
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
x_42 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_40);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_2);
lean::dec(x_37);
x_47 = lean::mk_nat_obj(1u);
x_48 = lean::nat_sub(x_42, x_47);
lean::dec(x_42);
x_50 = l_lean_parser_number_view_of__nat(x_48);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = l_lean_expander_mixfix__to__notation__spec___closed__4;
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
obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_42);
lean::dec(x_39);
x_59 = l_lean_parser_command_notation__spec_precedence_has__view;
x_60 = lean::cnstr_get(x_59, 1);
lean::inc(x_60);
lean::dec(x_59);
x_63 = lean::apply_1(x_60, x_37);
x_64 = l_lean_expander_mixfix__to__notation__spec___closed__7;
x_65 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_63, x_64, x_2);
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
x_81 = l_lean_expander_mixfix__to__notation__spec___closed__2;
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
x_87 = l_lean_expander_mixfix__to__notation__spec___closed__1;
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
x_93 = l_lean_expander_mixfix__to__notation__spec___closed__2;
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
x_98 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_97);
x_101 = l_lean_expander_mixfix__to__notation__spec___closed__2;
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
x_111 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_110);
if (lean::is_scalar(x_106)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_106;
}
lean::cnstr_set(x_113, 0, x_112);
x_114 = l_lean_expander_mixfix__to__notation__spec___closed__1;
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
x_120 = l_lean_expander_mixfix__to__notation__spec___closed__2;
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
obj* l_lean_expander_mixfix__to__notation__spec___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_mixfix__to__notation__spec(x_0, x_1, x_2);
lean::dec(x_0);
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_lean_expander_mk__simple__binder___closed__2;
x_4 = l_lean_expander_mk__simple__binder___closed__1;
x_5 = l_lean_expander_mk__simple__binder___closed__3;
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
x_8 = l_lean_expander_mk__simple__binder___closed__4;
x_9 = l_lean_expander_mk__simple__binder___closed__1;
x_10 = l_lean_expander_mk__simple__binder___closed__5;
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
x_13 = l_lean_expander_mk__simple__binder___closed__6;
x_14 = l_lean_expander_mk__simple__binder___closed__1;
x_15 = l_lean_expander_mk__simple__binder___closed__7;
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
x_18 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_19 = l_lean_expander_mk__simple__binder___closed__1;
x_20 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
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
obj* l_lean_expander_mk__simple__binder___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_expander_mk__simple__binder(x_0, x_3, x_2);
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
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
x_12 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_0, x_1, x_6);
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
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_1, 1);
x_12 = l_lean_expander_get__opt__type___main(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
x_15 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_19 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_18, x_17);
x_20 = l_lean_expander_binder__ident__to__ident___main(x_6);
lean::dec(x_6);
x_22 = l_lean_expander_mk__simple__binder(x_20, x_0, x_19);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_0, x_1, x_2, x_8);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
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
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
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
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_18 = l_lean_expander_mk__simple__binder(x_16, x_0, x_15);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_0, x_1, x_7);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(uint8 x_0, obj* x_1, obj* x_2) {
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
x_10 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_lean_expander_mk__simple__binder(x_10, x_0, x_1);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_0, x_1, x_7);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_10 = lean::cnstr_get(x_0, 1);
x_11 = l_lean_expander_get__opt__type___main(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
x_19 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_21 = 0;
x_22 = l_lean_expander_mk__simple__binder(x_19, x_21, x_18);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_7);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_15, x_17, x_14);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_0, x_6);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj* x_0, obj* x_1) {
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
x_9 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_11 = 0;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_9, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_0, x_6);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_10 = lean::cnstr_get(x_0, 1);
x_11 = l_lean_expander_get__opt__type___main(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
x_19 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_21 = 1;
x_22 = l_lean_expander_mk__simple__binder(x_19, x_21, x_18);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_7);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = 1;
x_18 = l_lean_expander_mk__simple__binder(x_15, x_17, x_14);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_0, x_6);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(obj* x_0, obj* x_1) {
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
x_9 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_11 = 1;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_9, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_0, x_6);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
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
x_10 = lean::cnstr_get(x_0, 1);
x_11 = l_lean_expander_get__opt__type___main(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
x_19 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_21 = 2;
x_22 = l_lean_expander_mk__simple__binder(x_19, x_21, x_18);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_7);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = 2;
x_18 = l_lean_expander_mk__simple__binder(x_15, x_17, x_14);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_0, x_6);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(obj* x_0, obj* x_1) {
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
x_9 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_11 = 2;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_9, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_0, x_6);
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
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
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
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = l_lean_expander_mk__simple__binder___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_lean_expander_get__opt__type___main(x_13);
lean::dec(x_13);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_18 = 3;
x_19 = l_lean_expander_mk__simple__binder(x_16, x_18, x_14);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_9 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = l_lean_expander_get__opt__type___main(x_12);
lean::dec(x_12);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
lean::dec(x_4);
x_17 = 3;
x_18 = l_lean_expander_mk__simple__binder(x_15, x_17, x_13);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
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
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_0, x_1, x_6);
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
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_1, 1);
x_12 = l_lean_expander_get__opt__type___main(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
x_15 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_19 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_18, x_17);
x_20 = l_lean_expander_binder__ident__to__ident___main(x_6);
lean::dec(x_6);
x_22 = l_lean_expander_mk__simple__binder(x_20, x_0, x_19);
x_23 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_0, x_1, x_2, x_8);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
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
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
x_18 = l_lean_expander_mk__simple__binder(x_16, x_0, x_15);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_0, x_1, x_7);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8 x_0, obj* x_1, obj* x_2) {
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
x_10 = l_lean_expander_binder__ident__to__ident___main(x_5);
lean::dec(x_5);
lean::inc(x_1);
x_13 = l_lean_expander_mk__simple__binder(x_10, x_0, x_1);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_0, x_1, x_7);
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
obj* x_12; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_12 = l_lean_expander_expand__bracketed__binder___main___closed__4;
return x_12;
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
obj* x_17; 
lean::dec(x_6);
lean::dec(x_1);
x_17 = l_lean_expander_expand__bracketed__binder___main___closed__5;
return x_17;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
lean::dec(x_6);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_26; obj* x_28; 
lean::dec(x_1);
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_18, x_24);
lean::dec(x_18);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_26);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; obj* x_36; obj* x_38; obj* x_40; 
lean::dec(x_1);
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
lean::dec(x_29);
x_36 = lean::cnstr_get(x_18, 0);
lean::inc(x_36);
x_38 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_18, x_33, x_36);
lean::dec(x_18);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_38);
return x_40;
}
else
{
obj* x_41; 
x_41 = lean::cnstr_get(x_18, 1);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_44; obj* x_47; obj* x_50; obj* x_51; 
lean::dec(x_1);
x_44 = lean::cnstr_get(x_29, 0);
lean::inc(x_44);
lean::dec(x_29);
x_47 = lean::cnstr_get(x_18, 0);
lean::inc(x_47);
lean::dec(x_18);
x_50 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_44, x_47);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_41);
x_53 = l_lean_parser_term_binder__default_has__view;
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
lean::dec(x_53);
x_57 = lean::apply_1(x_54, x_29);
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_59 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_57, x_58, x_1);
lean::dec(x_57);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_18);
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
obj* x_66; obj* x_68; obj* x_69; obj* x_72; obj* x_73; 
x_66 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_68 = x_59;
} else {
 lean::inc(x_66);
 lean::dec(x_59);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_18, 0);
lean::inc(x_69);
lean::dec(x_18);
x_72 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_66, x_69);
if (lean::is_scalar(x_68)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_68;
}
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
}
}
}
}
}
case 1:
{
obj* x_76; 
lean::dec(x_4);
lean::dec(x_0);
x_76 = lean::cnstr_get(x_6, 2);
lean::inc(x_76);
if (lean::obj_tag(x_76) == 0)
{
obj* x_79; obj* x_81; obj* x_83; 
lean::dec(x_1);
x_79 = lean::cnstr_get(x_6, 0);
lean::inc(x_79);
x_81 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_79);
lean::dec(x_6);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_81);
return x_83;
}
else
{
obj* x_84; 
x_84 = lean::cnstr_get(x_76, 0);
lean::inc(x_84);
lean::dec(x_76);
if (lean::obj_tag(x_84) == 0)
{
obj* x_88; obj* x_91; obj* x_93; obj* x_95; 
lean::dec(x_1);
x_88 = lean::cnstr_get(x_84, 0);
lean::inc(x_88);
lean::dec(x_84);
x_91 = lean::cnstr_get(x_6, 0);
lean::inc(x_91);
x_93 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_88, x_91);
lean::dec(x_6);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_93);
return x_95;
}
else
{
obj* x_96; 
x_96 = lean::cnstr_get(x_6, 1);
lean::inc(x_96);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_102; obj* x_105; obj* x_106; 
lean::dec(x_1);
x_99 = lean::cnstr_get(x_84, 0);
lean::inc(x_99);
lean::dec(x_84);
x_102 = lean::cnstr_get(x_6, 0);
lean::inc(x_102);
lean::dec(x_6);
x_105 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_99, x_102);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
return x_106;
}
else
{
obj* x_108; obj* x_109; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_96);
x_108 = l_lean_parser_term_binder__default_has__view;
x_109 = lean::cnstr_get(x_108, 1);
lean::inc(x_109);
lean::dec(x_108);
x_112 = lean::apply_1(x_109, x_84);
x_113 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_114 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_112, x_113, x_1);
lean::dec(x_112);
if (lean::obj_tag(x_114) == 0)
{
obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_6);
x_117 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_119 = x_114;
} else {
 lean::inc(x_117);
 lean::dec(x_114);
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
obj* x_121; obj* x_123; obj* x_124; obj* x_127; obj* x_128; 
x_121 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_123 = x_114;
} else {
 lean::inc(x_121);
 lean::dec(x_114);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_6, 0);
lean::inc(x_124);
lean::dec(x_6);
x_127 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_121, x_124);
if (lean::is_scalar(x_123)) {
 x_128 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_128 = x_123;
}
lean::cnstr_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
case 2:
{
obj* x_131; 
lean::dec(x_4);
lean::dec(x_0);
x_131 = lean::cnstr_get(x_6, 2);
lean::inc(x_131);
if (lean::obj_tag(x_131) == 0)
{
obj* x_134; obj* x_136; obj* x_138; 
lean::dec(x_1);
x_134 = lean::cnstr_get(x_6, 0);
lean::inc(x_134);
x_136 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_134);
lean::dec(x_6);
x_138 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_138, 0, x_136);
return x_138;
}
else
{
obj* x_139; 
x_139 = lean::cnstr_get(x_131, 0);
lean::inc(x_139);
lean::dec(x_131);
if (lean::obj_tag(x_139) == 0)
{
obj* x_143; obj* x_146; obj* x_148; obj* x_150; 
lean::dec(x_1);
x_143 = lean::cnstr_get(x_139, 0);
lean::inc(x_143);
lean::dec(x_139);
x_146 = lean::cnstr_get(x_6, 0);
lean::inc(x_146);
x_148 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_143, x_146);
lean::dec(x_6);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_148);
return x_150;
}
else
{
obj* x_151; 
x_151 = lean::cnstr_get(x_6, 1);
lean::inc(x_151);
if (lean::obj_tag(x_151) == 0)
{
obj* x_154; obj* x_157; obj* x_160; obj* x_161; 
lean::dec(x_1);
x_154 = lean::cnstr_get(x_139, 0);
lean::inc(x_154);
lean::dec(x_139);
x_157 = lean::cnstr_get(x_6, 0);
lean::inc(x_157);
lean::dec(x_6);
x_160 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_154, x_157);
x_161 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_161, 0, x_160);
return x_161;
}
else
{
obj* x_163; obj* x_164; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_151);
x_163 = l_lean_parser_term_binder__default_has__view;
x_164 = lean::cnstr_get(x_163, 1);
lean::inc(x_164);
lean::dec(x_163);
x_167 = lean::apply_1(x_164, x_139);
x_168 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_169 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_167, x_168, x_1);
lean::dec(x_167);
if (lean::obj_tag(x_169) == 0)
{
obj* x_172; obj* x_174; obj* x_175; 
lean::dec(x_6);
x_172 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_174 = x_169;
} else {
 lean::inc(x_172);
 lean::dec(x_169);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
return x_175;
}
else
{
obj* x_176; obj* x_178; obj* x_179; obj* x_182; obj* x_183; 
x_176 = lean::cnstr_get(x_169, 0);
if (lean::is_exclusive(x_169)) {
 x_178 = x_169;
} else {
 lean::inc(x_176);
 lean::dec(x_169);
 x_178 = lean::box(0);
}
x_179 = lean::cnstr_get(x_6, 0);
lean::inc(x_179);
lean::dec(x_6);
x_182 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_176, x_179);
if (lean::is_scalar(x_178)) {
 x_183 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_183 = x_178;
}
lean::cnstr_set(x_183, 0, x_182);
return x_183;
}
}
}
}
}
case 3:
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_187; obj* x_190; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_187 = lean::cnstr_get(x_6, 0);
lean::inc(x_187);
lean::dec(x_6);
x_190 = lean::cnstr_get(x_187, 0);
lean::inc(x_190);
x_192 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_192, 0, x_190);
x_193 = lean::box(0);
x_194 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_194, 0, x_192);
lean::cnstr_set(x_194, 1, x_193);
x_195 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_187, x_194);
x_196 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_196, 0, x_195);
return x_196;
}
else
{
obj* x_197; obj* x_200; obj* x_201; obj* x_202; 
x_197 = lean::cnstr_get(x_6, 0);
lean::inc(x_197);
lean::dec(x_6);
x_200 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_201 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_197, x_200);
x_202 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_202, 0, x_201);
return x_202;
}
}
default:
{
obj* x_205; obj* x_206; obj* x_209; obj* x_210; obj* x_212; 
lean::dec(x_6);
lean::dec(x_0);
x_205 = l_lean_parser_term_anonymous__constructor_has__view;
x_206 = lean::cnstr_get(x_205, 1);
lean::inc(x_206);
lean::dec(x_205);
x_209 = lean::apply_1(x_206, x_4);
x_210 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_212 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_209, x_210, x_1);
lean::dec(x_209);
if (lean::obj_tag(x_212) == 0)
{
obj* x_215; obj* x_217; obj* x_218; 
lean::dec(x_1);
x_215 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_217 = x_212;
} else {
 lean::inc(x_215);
 lean::dec(x_212);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_215);
return x_218;
}
else
{
obj* x_219; obj* x_221; obj* x_222; obj* x_224; 
x_219 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 lean::cnstr_set(x_212, 0, lean::box(0));
 x_221 = x_212;
} else {
 lean::inc(x_219);
 lean::dec(x_212);
 x_221 = lean::box(0);
}
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_222, 2);
lean::inc(x_224);
if (lean::obj_tag(x_224) == 0)
{
obj* x_227; obj* x_230; uint8 x_232; obj* x_233; obj* x_235; 
lean::dec(x_1);
x_227 = lean::cnstr_get(x_219, 0);
lean::inc(x_227);
lean::dec(x_219);
x_230 = lean::cnstr_get(x_222, 0);
lean::inc(x_230);
x_232 = lean::unbox(x_227);
x_233 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_232, x_222, x_230);
lean::dec(x_222);
if (lean::is_scalar(x_221)) {
 x_235 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_235 = x_221;
}
lean::cnstr_set(x_235, 0, x_233);
return x_235;
}
else
{
obj* x_236; 
x_236 = lean::cnstr_get(x_224, 0);
lean::inc(x_236);
lean::dec(x_224);
if (lean::obj_tag(x_236) == 0)
{
obj* x_240; obj* x_243; obj* x_246; uint8 x_248; obj* x_249; obj* x_251; 
lean::dec(x_1);
x_240 = lean::cnstr_get(x_219, 0);
lean::inc(x_240);
lean::dec(x_219);
x_243 = lean::cnstr_get(x_236, 0);
lean::inc(x_243);
lean::dec(x_236);
x_246 = lean::cnstr_get(x_222, 0);
lean::inc(x_246);
x_248 = lean::unbox(x_240);
x_249 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_248, x_222, x_243, x_246);
lean::dec(x_222);
if (lean::is_scalar(x_221)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_221;
}
lean::cnstr_set(x_251, 0, x_249);
return x_251;
}
else
{
obj* x_252; 
x_252 = lean::cnstr_get(x_222, 1);
lean::inc(x_252);
if (lean::obj_tag(x_252) == 0)
{
obj* x_255; obj* x_258; obj* x_261; uint8 x_264; obj* x_265; obj* x_266; 
lean::dec(x_1);
x_255 = lean::cnstr_get(x_219, 0);
lean::inc(x_255);
lean::dec(x_219);
x_258 = lean::cnstr_get(x_236, 0);
lean::inc(x_258);
lean::dec(x_236);
x_261 = lean::cnstr_get(x_222, 0);
lean::inc(x_261);
lean::dec(x_222);
x_264 = lean::unbox(x_255);
x_265 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_264, x_258, x_261);
if (lean::is_scalar(x_221)) {
 x_266 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_266 = x_221;
}
lean::cnstr_set(x_266, 0, x_265);
return x_266;
}
else
{
obj* x_269; obj* x_272; obj* x_273; obj* x_276; obj* x_277; obj* x_278; 
lean::dec(x_221);
lean::dec(x_252);
x_269 = lean::cnstr_get(x_219, 0);
lean::inc(x_269);
lean::dec(x_219);
x_272 = l_lean_parser_term_binder__default_has__view;
x_273 = lean::cnstr_get(x_272, 1);
lean::inc(x_273);
lean::dec(x_272);
x_276 = lean::apply_1(x_273, x_236);
x_277 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_278 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_276, x_277, x_1);
lean::dec(x_276);
if (lean::obj_tag(x_278) == 0)
{
obj* x_282; obj* x_284; obj* x_285; 
lean::dec(x_222);
lean::dec(x_269);
x_282 = lean::cnstr_get(x_278, 0);
if (lean::is_exclusive(x_278)) {
 x_284 = x_278;
} else {
 lean::inc(x_282);
 lean::dec(x_278);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_282);
return x_285;
}
else
{
obj* x_286; obj* x_288; obj* x_289; uint8 x_292; obj* x_293; obj* x_294; 
x_286 = lean::cnstr_get(x_278, 0);
if (lean::is_exclusive(x_278)) {
 x_288 = x_278;
} else {
 lean::inc(x_286);
 lean::dec(x_278);
 x_288 = lean::box(0);
}
x_289 = lean::cnstr_get(x_222, 0);
lean::inc(x_289);
lean::dec(x_222);
x_292 = lean::unbox(x_269);
x_293 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_292, x_286, x_289);
if (lean::is_scalar(x_288)) {
 x_294 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_294 = x_288;
}
lean::cnstr_set(x_294, 0, x_293);
return x_294;
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
obj* x_295; obj* x_298; 
x_295 = lean::cnstr_get(x_0, 0);
lean::inc(x_295);
lean::dec(x_0);
x_298 = lean::cnstr_get(x_295, 1);
lean::inc(x_298);
lean::dec(x_295);
if (lean::obj_tag(x_298) == 0)
{
obj* x_302; 
lean::dec(x_298);
x_302 = l_lean_expander_expand__bracketed__binder___main___closed__3;
x_2 = x_302;
goto lbl_3;
}
else
{
obj* x_303; uint8 x_306; obj* x_307; obj* x_308; 
x_303 = lean::cnstr_get(x_298, 0);
lean::inc(x_303);
lean::dec(x_298);
x_306 = 0;
x_307 = lean::box(x_306);
x_308 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_308, 0, x_307);
lean::cnstr_set(x_308, 1, x_303);
x_2 = x_308;
goto lbl_3;
}
}
case 1:
{
obj* x_309; obj* x_312; uint8 x_315; obj* x_316; obj* x_317; 
x_309 = lean::cnstr_get(x_0, 0);
lean::inc(x_309);
lean::dec(x_0);
x_312 = lean::cnstr_get(x_309, 1);
lean::inc(x_312);
lean::dec(x_309);
x_315 = 1;
x_316 = lean::box(x_315);
x_317 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_312);
x_2 = x_317;
goto lbl_3;
}
case 2:
{
obj* x_318; obj* x_321; uint8 x_324; obj* x_325; obj* x_326; 
x_318 = lean::cnstr_get(x_0, 0);
lean::inc(x_318);
lean::dec(x_0);
x_321 = lean::cnstr_get(x_318, 1);
lean::inc(x_321);
lean::dec(x_318);
x_324 = 2;
x_325 = lean::box(x_324);
x_326 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_326, 0, x_325);
lean::cnstr_set(x_326, 1, x_321);
x_2 = x_326;
goto lbl_3;
}
case 3:
{
obj* x_327; obj* x_330; 
x_327 = lean::cnstr_get(x_0, 0);
lean::inc(x_327);
lean::dec(x_0);
x_330 = lean::cnstr_get(x_327, 1);
lean::inc(x_330);
lean::dec(x_327);
if (lean::obj_tag(x_330) == 0)
{
obj* x_333; obj* x_336; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_345; obj* x_346; obj* x_347; obj* x_348; uint8 x_349; obj* x_350; obj* x_351; 
x_333 = lean::cnstr_get(x_330, 0);
lean::inc(x_333);
lean::dec(x_330);
x_336 = lean::cnstr_get(x_333, 0);
lean::inc(x_336);
x_338 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_338, 0, x_336);
x_339 = lean::box(0);
x_340 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_340, 0, x_338);
lean::cnstr_set(x_340, 1, x_339);
x_341 = lean::box(0);
x_342 = lean::cnstr_get(x_333, 2);
lean::inc(x_342);
lean::dec(x_333);
x_345 = l_lean_expander_mk__simple__binder___closed__1;
x_346 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_346, 0, x_345);
lean::cnstr_set(x_346, 1, x_342);
x_347 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_347, 0, x_346);
x_348 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_348, 0, x_340);
lean::cnstr_set(x_348, 1, x_347);
lean::cnstr_set(x_348, 2, x_341);
x_349 = 3;
x_350 = lean::box(x_349);
x_351 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_351, 0, x_350);
lean::cnstr_set(x_351, 1, x_348);
x_2 = x_351;
goto lbl_3;
}
else
{
obj* x_352; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; uint8 x_361; obj* x_362; obj* x_363; 
x_352 = lean::cnstr_get(x_330, 0);
lean::inc(x_352);
lean::dec(x_330);
x_355 = lean::box(0);
x_356 = l_lean_expander_mk__simple__binder___closed__1;
x_357 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_357, 0, x_356);
lean::cnstr_set(x_357, 1, x_352);
x_358 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_358, 0, x_357);
x_359 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_360 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_358);
lean::cnstr_set(x_360, 2, x_355);
x_361 = 3;
x_362 = lean::box(x_361);
x_363 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_360);
x_2 = x_363;
goto lbl_3;
}
}
default:
{
obj* x_364; obj* x_367; obj* x_368; obj* x_371; obj* x_372; obj* x_374; 
x_364 = lean::cnstr_get(x_0, 0);
lean::inc(x_364);
lean::dec(x_0);
x_367 = l_lean_parser_term_anonymous__constructor_has__view;
x_368 = lean::cnstr_get(x_367, 1);
lean::inc(x_368);
lean::dec(x_367);
x_371 = lean::apply_1(x_368, x_364);
x_372 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_374 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_371, x_372, x_1);
lean::dec(x_371);
if (lean::obj_tag(x_374) == 0)
{
obj* x_377; obj* x_379; obj* x_380; 
lean::dec(x_1);
x_377 = lean::cnstr_get(x_374, 0);
if (lean::is_exclusive(x_374)) {
 x_379 = x_374;
} else {
 lean::inc(x_377);
 lean::dec(x_374);
 x_379 = lean::box(0);
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_377);
return x_380;
}
else
{
obj* x_381; 
x_381 = lean::cnstr_get(x_374, 0);
lean::inc(x_381);
lean::dec(x_374);
x_2 = x_381;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_384; obj* x_386; 
x_384 = lean::cnstr_get(x_2, 1);
lean::inc(x_384);
x_386 = lean::cnstr_get(x_384, 2);
lean::inc(x_386);
if (lean::obj_tag(x_386) == 0)
{
obj* x_389; obj* x_392; uint8 x_394; obj* x_395; obj* x_397; 
lean::dec(x_1);
x_389 = lean::cnstr_get(x_2, 0);
lean::inc(x_389);
lean::dec(x_2);
x_392 = lean::cnstr_get(x_384, 0);
lean::inc(x_392);
x_394 = lean::unbox(x_389);
x_395 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_394, x_384, x_392);
lean::dec(x_384);
x_397 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_397, 0, x_395);
return x_397;
}
else
{
obj* x_398; 
x_398 = lean::cnstr_get(x_386, 0);
lean::inc(x_398);
lean::dec(x_386);
if (lean::obj_tag(x_398) == 0)
{
obj* x_402; obj* x_405; obj* x_408; uint8 x_410; obj* x_411; obj* x_413; 
lean::dec(x_1);
x_402 = lean::cnstr_get(x_2, 0);
lean::inc(x_402);
lean::dec(x_2);
x_405 = lean::cnstr_get(x_398, 0);
lean::inc(x_405);
lean::dec(x_398);
x_408 = lean::cnstr_get(x_384, 0);
lean::inc(x_408);
x_410 = lean::unbox(x_402);
x_411 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_410, x_384, x_405, x_408);
lean::dec(x_384);
x_413 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_413, 0, x_411);
return x_413;
}
else
{
obj* x_414; 
x_414 = lean::cnstr_get(x_384, 1);
lean::inc(x_414);
if (lean::obj_tag(x_414) == 0)
{
obj* x_417; obj* x_420; obj* x_423; uint8 x_426; obj* x_427; obj* x_428; 
lean::dec(x_1);
x_417 = lean::cnstr_get(x_2, 0);
lean::inc(x_417);
lean::dec(x_2);
x_420 = lean::cnstr_get(x_398, 0);
lean::inc(x_420);
lean::dec(x_398);
x_423 = lean::cnstr_get(x_384, 0);
lean::inc(x_423);
lean::dec(x_384);
x_426 = lean::unbox(x_417);
x_427 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_426, x_420, x_423);
x_428 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_428, 0, x_427);
return x_428;
}
else
{
obj* x_430; obj* x_433; obj* x_434; obj* x_437; obj* x_438; obj* x_439; 
lean::dec(x_414);
x_430 = lean::cnstr_get(x_2, 0);
lean::inc(x_430);
lean::dec(x_2);
x_433 = l_lean_parser_term_binder__default_has__view;
x_434 = lean::cnstr_get(x_433, 1);
lean::inc(x_434);
lean::dec(x_433);
x_437 = lean::apply_1(x_434, x_398);
x_438 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_439 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_437, x_438, x_1);
lean::dec(x_437);
if (lean::obj_tag(x_439) == 0)
{
obj* x_443; obj* x_445; obj* x_446; 
lean::dec(x_430);
lean::dec(x_384);
x_443 = lean::cnstr_get(x_439, 0);
if (lean::is_exclusive(x_439)) {
 x_445 = x_439;
} else {
 lean::inc(x_443);
 lean::dec(x_439);
 x_445 = lean::box(0);
}
if (lean::is_scalar(x_445)) {
 x_446 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_446 = x_445;
}
lean::cnstr_set(x_446, 0, x_443);
return x_446;
}
else
{
obj* x_447; obj* x_449; obj* x_450; uint8 x_453; obj* x_454; obj* x_455; 
x_447 = lean::cnstr_get(x_439, 0);
if (lean::is_exclusive(x_439)) {
 x_449 = x_439;
} else {
 lean::inc(x_447);
 lean::dec(x_439);
 x_449 = lean::box(0);
}
x_450 = lean::cnstr_get(x_384, 0);
lean::inc(x_450);
lean::dec(x_384);
x_453 = lean::unbox(x_430);
x_454 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_453, x_447, x_450);
if (lean::is_scalar(x_449)) {
 x_455 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_455 = x_449;
}
lean::cnstr_set(x_455, 0, x_454);
return x_455;
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
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_3, x_1, x_2);
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
return x_3;
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
return x_3;
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
return x_3;
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
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_3, x_1, x_2);
return x_4;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::apply_2(x_0, x_13, x_8);
return x_14;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::inc(x_0);
x_12 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_1, x_2, x_8);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_14 = 0;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_9);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_12);
return x_17;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::apply_2(x_0, x_13, x_8);
return x_14;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::inc(x_0);
x_12 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_1, x_2, x_8);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_14 = 0;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_9);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_12);
return x_17;
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
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_1, x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
x_13 = lean::apply_2(x_0, x_12, x_11);
return x_13;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
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
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_14 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_1, x_9, x_3);
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
x_37 = l_lean_parser_term_match_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_41 = l_lean_parser_term_anonymous__constructor_has__view;
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
x_48 = l_lean_expander_mixfix_transform___closed__4;
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
x_52 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_53 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
x_54 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
x_55 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_35);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set(x_55, 4, x_35);
lean::cnstr_set(x_55, 5, x_51);
x_56 = lean::apply_1(x_38, x_55);
x_57 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
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
x_64 = l_lean_expander_expand__bracketed__binder___main(x_26, x_3);
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
x_74 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_23, x_71);
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
x_85 = l_lean_expander_binder__ident__to__ident___main(x_82);
lean::dec(x_82);
x_87 = 0;
x_88 = l_lean_expander_get__opt__type___main___closed__1;
x_89 = l_lean_expander_mk__simple__binder(x_85, x_87, x_88);
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_8 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_1, x_6);
x_9 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_10 = 0;
x_11 = l_lean_expander_get__opt__type___main___closed__1;
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::apply_2(x_0, x_13, x_8);
return x_14;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::inc(x_0);
x_12 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_1, x_2, x_8);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_14 = 0;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_9);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_12);
return x_17;
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
obj* x_10; obj* x_13; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_15; 
x_15 = lean::box(0);
x_13 = x_15;
goto lbl_14;
}
else
{
obj* x_16; obj* x_18; 
x_16 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_22; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_2, x_19, x_10);
lean::dec(x_10);
lean::dec(x_2);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_22);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_16);
lean::dec(x_18);
x_29 = lean::box(0);
x_13 = x_29;
goto lbl_14;
}
}
lbl_14:
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_13);
x_31 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_7, 0);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_42; 
lean::dec(x_3);
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_45; 
lean::dec(x_36);
x_45 = lean::box(0);
x_42 = x_45;
goto lbl_43;
}
else
{
obj* x_46; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_46 = x_7;
} else {
 lean::dec(x_7);
 x_46 = lean::box(0);
}
if (lean::obj_tag(x_36) == 0)
{
obj* x_47; obj* x_50; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get(x_36, 0);
lean::inc(x_47);
lean::dec(x_36);
x_50 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_2, x_47, x_39);
lean::dec(x_39);
lean::dec(x_2);
if (lean::is_scalar(x_46)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_46;
}
lean::cnstr_set(x_53, 0, x_50);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
else
{
obj* x_57; 
lean::dec(x_46);
lean::dec(x_36);
x_57 = lean::box(0);
x_42 = x_57;
goto lbl_43;
}
}
lbl_43:
{
obj* x_59; obj* x_62; obj* x_63; 
lean::dec(x_42);
x_59 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_2, x_39);
lean::dec(x_39);
lean::dec(x_2);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_59);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
}
else
{
obj* x_64; obj* x_68; 
x_64 = lean::cnstr_get(x_36, 0);
lean::inc(x_64);
lean::inc(x_64);
lean::inc(x_0);
x_68 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_2, x_64, x_3);
if (lean::obj_tag(x_68) == 0)
{
obj* x_74; obj* x_76; obj* x_77; 
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_64);
lean::dec(x_36);
x_74 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 x_76 = x_68;
} else {
 lean::inc(x_74);
 lean::dec(x_68);
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
obj* x_78; obj* x_80; obj* x_81; obj* x_84; 
x_78 = lean::cnstr_get(x_68, 0);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_set(x_68, 0, lean::box(0));
 x_80 = x_68;
} else {
 lean::inc(x_78);
 lean::dec(x_68);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_4, 0);
lean::inc(x_81);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_88; 
lean::dec(x_64);
lean::dec(x_36);
x_88 = lean::box(0);
x_84 = x_88;
goto lbl_85;
}
else
{
obj* x_89; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_89 = x_7;
} else {
 lean::dec(x_7);
 x_89 = lean::box(0);
}
if (lean::obj_tag(x_36) == 0)
{
obj* x_92; obj* x_95; obj* x_96; 
lean::dec(x_36);
lean::dec(x_80);
x_92 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_78, x_64, x_81);
lean::dec(x_81);
lean::dec(x_78);
if (lean::is_scalar(x_89)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_89;
}
lean::cnstr_set(x_95, 0, x_92);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
else
{
obj* x_100; 
lean::dec(x_64);
lean::dec(x_36);
lean::dec(x_89);
x_100 = lean::box(0);
x_84 = x_100;
goto lbl_85;
}
}
lbl_85:
{
obj* x_102; obj* x_105; obj* x_106; 
lean::dec(x_84);
x_102 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_78, x_81);
lean::dec(x_81);
lean::dec(x_78);
x_105 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_105, 0, x_102);
if (lean::is_scalar(x_80)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_80;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
obj* x_111; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_111 = l_lean_expander_no__expansion___closed__1;
return x_111;
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
return x_3;
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
lean::dec(x_3);
return x_4;
}
}
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_expander_expand__bracketed__binder___main___closed__4;
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
x_10 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
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
x_21 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_6, x_1);
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
obj* x_28; 
lean::dec(x_5);
lean::dec(x_1);
x_28 = l_lean_expander_no__expansion___closed__1;
return x_28;
}
}
}
obj* l_lean_expander_lambda_transform___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_7 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_7);
lean::cnstr_set(x_8, 3, x_1);
x_9 = lean::apply_1(x_3, x_8);
return x_9;
}
}
obj* _init_l_lean_expander_lambda_transform___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform___lambda__1), 2, 0);
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
return x_13;
}
}
obj* l_lean_expander_pi_transform___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_lean_parser_term_pi_has__view;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_10);
lean::cnstr_set(x_11, 3, x_2);
x_12 = lean::apply_1(x_4, x_11);
return x_12;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform___lambda__1), 3, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 3);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_expander_expand__binders(x_8, x_9, x_11, x_1);
return x_14;
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
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_list_map___main___at_lean_expander_paren_transform___spec__1(x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_6, lean::box(0));
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
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
obj* x_26; obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_24);
x_26 = lean::cnstr_get(x_11, 0);
lean::inc(x_26);
lean::dec(x_11);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
x_32 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_26, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_37 = lean::cnstr_get(x_22, 0);
lean::inc(x_37);
lean::dec(x_22);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_lean_expander_paren_transform___closed__2;
x_47 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_46, x_45);
if (lean::is_scalar(x_24)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_24;
}
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
obj* _init_l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_option_get__or__else___main___rarg(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
x_5 = l_lean_expander_binding__annotation__update;
x_6 = l_lean_parser_syntax_mk__node(x_5, x_4);
return x_6;
}
}
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_5);
x_12 = l_lean_expander_binding__annotation__update;
x_13 = l_lean_parser_syntax_mk__node(x_12, x_11);
return x_13;
}
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
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
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
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
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_expander_expand__bracketed__binder___main___closed__4;
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
x_18 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
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
x_35 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
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
x_41 = l_lean_expander_expand__bracketed__binder___main(x_39, x_1);
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
x_47 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
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
x_53 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
x_9 = x_53;
goto lbl_10;
}
}
}
default:
{
obj* x_55; 
lean::inc(x_1);
x_55 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
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
x_66 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_6, x_1);
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
obj* x_33; 
lean::dec(x_6);
lean::dec(x_1);
x_33 = l_lean_expander_no__expansion___closed__1;
return x_33;
}
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
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
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
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_6, 4);
lean::inc(x_20);
lean::dec(x_6);
x_23 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_24 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
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
x_29 = l_lean_expander_subtype_transform___closed__1;
x_30 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
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
obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
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
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
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
x_12 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_7, x_9);
x_0 = x_12;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_0 = l_lean_parser_command_mixfix;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix_transform), 2, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = l_lean_parser_command_reserve__mixfix;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_reserve__mixfix_transform), 2, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_lean_parser_term_bracketed__binders;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_bracketed__binders_transform), 2, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_term_lambda;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform), 2, 0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_term_pi;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform), 2, 0);
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
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variables_transform), 2, 0);
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_0, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_expander_mk__scope___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_mk__scope(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_lean_parser_syntax_get__pos(x_0);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
lean::dec(x_12);
x_16 = l_lean_file__map_to__position(x_9, x_14);
x_17 = lean::box(0);
x_18 = 2;
x_19 = l_string_join___closed__1;
x_20 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_17);
lean::cnstr_set(x_20, 3, x_19);
lean::cnstr_set(x_20, 4, x_1);
lean::cnstr_set_scalar(x_20, sizeof(void*)*5, x_18);
x_21 = x_20;
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
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
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
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
x_12 = l_lean_parser_syntax_flip__scopes___main(x_11, x_4);
x_13 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_0, x_6);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
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
x_23 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_19, x_21);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_13, 1);
lean::inc(x_24);
lean::dec(x_13);
x_27 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(x_17, x_24, x_2, x_3);
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
x_41 = l_lean_parser_syntax_mk__node(x_21, x_36);
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
x_47 = l_lean_expander_mk__scope(x_2, x_3);
if (lean::obj_tag(x_47) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_44);
lean::dec(x_17);
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
obj* x_57; obj* x_60; obj* x_62; obj* x_65; obj* x_70; obj* x_72; obj* x_73; obj* x_75; 
x_57 = lean::cnstr_get(x_47, 0);
lean::inc(x_57);
lean::dec(x_47);
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
lean::dec(x_57);
x_65 = lean::cnstr_get(x_13, 1);
lean::inc(x_65);
lean::dec(x_13);
lean::inc(x_65);
lean::inc(x_60);
x_70 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_60, x_65);
lean::inc(x_21);
x_72 = l_lean_parser_syntax_mk__node(x_21, x_70);
x_73 = lean::cnstr_get(x_3, 0);
lean::inc(x_73);
x_75 = lean::apply_2(x_44, x_72, x_73);
if (lean::obj_tag(x_75) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_3);
lean::dec(x_65);
lean::dec(x_60);
lean::dec(x_62);
lean::dec(x_17);
lean::dec(x_21);
x_82 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_84 = x_75;
} else {
 lean::inc(x_82);
 lean::dec(x_75);
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
obj* x_86; 
x_86 = lean::cnstr_get(x_75, 0);
lean::inc(x_86);
lean::dec(x_75);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; 
lean::dec(x_60);
x_90 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_17, x_65, x_62, x_3);
if (lean::obj_tag(x_90) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_21);
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
x_104 = l_lean_parser_syntax_mk__node(x_21, x_99);
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
else
{
obj* x_109; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_65);
lean::dec(x_21);
x_109 = lean::cnstr_get(x_86, 0);
lean::inc(x_109);
lean::dec(x_86);
x_112 = lean::box(0);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_60);
lean::cnstr_set(x_113, 1, x_112);
x_114 = l_lean_parser_syntax_flip__scopes___main(x_113, x_109);
x_0 = x_17;
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
obj* x_117; obj* x_118; 
lean::dec(x_0);
x_117 = l___private_init_lean_expander_2__expand__core___main___closed__1;
x_118 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_1, x_117, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_118;
}
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
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
lean::dec(x_1);
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
 l_lean_expander_mixfix__to__notation__spec___closed__7 = _init_l_lean_expander_mixfix__to__notation__spec___closed__7();
lean::mark_persistent(l_lean_expander_mixfix__to__notation__spec___closed__7);
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
 l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1 = _init_l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1___closed__1);
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
