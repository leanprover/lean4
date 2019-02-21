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
extern obj* l_lean_parser_command_variables;
extern obj* l_lean_parser_term_arrow_has__view;
obj* l_lean_expander_let_transform___closed__1;
obj* l_lean_expander_binding__annotation__update_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__name__ident(obj*);
obj* l_lean_expander_expand__bracketed__binder(obj*, obj*);
obj* l_lean_expander_sorry_transform___closed__1;
obj* l_lean_expander_pi_transform___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_term_binder__ident_has__view;
obj* l_lean_expander_if_transform___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(uint8, obj*, obj*);
extern obj* l_lean_parser_command_constant_has__view;
obj* l_lean_expander_coe__simple__binder__binders(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_universes;
obj* l_lean_expander_expand(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__2;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_lean_expander_if_transform(obj*, obj*);
extern obj* l_lean_parser_command_declaration;
obj* l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(obj*);
obj* l_lean_expander_universes_transform(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8, obj*, obj*);
obj* l_lean_expander_variables_transform(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
obj* l_lean_expander_mixfix_transform___closed__2;
extern obj* l_lean_parser_command_variable;
extern obj* l_lean_parser_term_match_has__view;
obj* l_lean_expander_mixfix_transform___closed__1;
obj* l_lean_expander_coe__binders__ext___rarg(obj*, obj*);
obj* l_id_monad___lambda__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_if_has__view;
extern obj* l_lean_parser_term_bracketed__binders;
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_expander_if_transform___closed__2;
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj*, obj*);
obj* l_lean_expander_coe__binders__ext(obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(obj*, obj*);
obj* l_lean_parser_syntax_flip__scopes___main(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(obj*, obj*, obj*);
obj* l_lean_expander_assume_transform___closed__1;
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view;
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1(obj*);
extern obj* l_lean_parser_command_mixfix_has__view;
obj* l_lean_expander_intro__rule_transform(obj*, obj*);
extern obj* l_lean_parser_command_universes_has__view;
obj* l_lean_expander_expand__bracketed__binder___main___closed__6;
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(uint8, obj*, obj*, obj*);
obj* l_lean_expander_subtype_transform___closed__1;
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_expander_transform__m_monad;
obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
extern obj* l_lean_parser_command_variable_has__view;
obj* l_lean_expander_arrow_transform___closed__1;
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
extern obj* l_lean_parser_level_leading;
obj* l___private_init_lean_expander_1__pop__stx__arg___closed__1;
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__3;
obj* l_lean_expander_builtin__transformers;
obj* l_lean_expander_mk__simple__binder___closed__4;
obj* l_lean_expander_if_transform___closed__3;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
extern obj* l_lean_parser_term_pi_has__view;
extern obj* l_lean_parser_command_universe_has__view;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj*);
extern obj* l_lean_parser_ident__univs;
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj*);
extern obj* l_lean_parser_term_sorry;
obj* l___private_init_lean_expander_1__pop__stx__arg(obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform___closed__1;
extern obj* l_lean_parser_command_intro__rule_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj*, obj*);
obj* l_lean_expander_bracketed__binders_transform(obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_command_variables_has__view;
obj* l_lean_expander_mk__simple__binder___closed__7;
obj* l_lean_expander_binding__annotation__update_parser___closed__1;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1(obj*);
extern obj* l_lean_parser_term_binders_has__view;
extern obj* l_lean_parser_command_reserve__mixfix_has__view;
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__2;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_id_bind(obj*, obj*);
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_lean_expander_sorry_transform(obj*, obj*);
obj* l_lean_expander_arrow_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__3;
obj* l_list_map___main___at_lean_expander_paren_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__ident__binder__id(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view_x_27;
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder___closed__2;
obj* l_lean_expander_glob__id(obj*);
obj* l_lean_expander_mk__simple__binder(obj*, uint8, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__5;
obj* l_lean_expander_mk__scope(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__6;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8, obj*, obj*);
extern obj* l_lean_parser_term_bracketed__binders_has__view;
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(obj*, obj*, obj*);
obj* l_lean_expander_lambda_transform___closed__1;
extern obj* l_lean_parser_term_pi;
extern obj* l_lean_parser_term_paren_has__view;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
extern obj* l_lean_parser_term__parser__m_lean_parser_monad__parsec;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
obj* l_id(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8, obj*, obj*);
obj* l_lean_expander_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_term__parser__m_monad;
extern obj* l_lean_parser_term_let_has__view;
obj* l_lean_expander_transform__m_monad__reader;
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
obj* l_lean_expander_mixfix_transform___closed__4;
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
obj* l_lean_expander_lambda_transform(obj*, obj*);
obj* l_lean_expander_declaration_transform(obj*, obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_arrow_transform___closed__2;
obj* l_lean_expander_no__expansion(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__2;
obj* l_rbnode_balance2___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_expander_binder__ident__to__ident(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main(obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_expander_declaration_transform___closed__3;
obj* l_except__t_monad___rarg(obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_lean_expander_expander__config_has__lift(obj*);
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1(obj*);
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj*, obj*);
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj*, obj*);
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj*);
obj* l_id_monad___lambda__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_expander_mk__simple__binder___closed__6;
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj*);
extern obj* l_lean_parser_term_assume_has__view;
extern obj* l_lean_parser_command_intro__rule;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj*);
obj* l_lean_expander_binder__ident__to__ident___main___closed__1;
obj* l_lean_expander_transform__m_monad__except;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__3;
extern obj* l_lean_parser_term_paren;
obj* l_rbmap_find___main___at___private_init_lean_expander_2__expand__core___main___spec__2(obj*, obj*);
extern obj* l_lean_parser_term_hole_has__view;
obj* l_lean_expander_error(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
obj* l_lean_expander_coe__binder__bracketed__binder___closed__1;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__1;
obj* l_lean_expander_coe__binders__ext__binders(obj*);
obj* l_lean_expander_mixfix_transform(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__1;
obj* l_lean_expander_paren_transform___closed__1;
obj* l_rbnode_balance1___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__ident__ident__univs(obj*);
obj* l_lean_expander_paren_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj*, obj*, obj*);
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
obj* l_lean_expander_paren_transform___closed__2;
extern obj* l_lean_parser_term_if;
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
obj* l_lean_expander_expand__binders(obj*, obj*, obj*, obj*);
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
obj* l_id_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform(obj*, obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
obj* l_lean_expander_level_leading_transform(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_expander_binding__annotation__update_parser_lean_parser_has__view;
obj* l_lean_expander_expander__m;
obj* l_lean_file__map_to__position(obj*, obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_lean_expander_constant_transform___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__4;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder(obj*);
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_expander_no__expansion___closed__1;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
extern obj* l_lean_parser_term__parser__m_monad__except;
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1(obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_mk__simple__binder___closed__3;
obj* l_lean_expander_let_transform(obj*, obj*);
extern obj* l_lean_parser_term_let;
obj* l_lean_expander_expand__bracketed__binder___main___closed__7;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(obj*, obj*);
obj* l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_notation_has__view;
obj* l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(obj*, obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_expander_constant_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
extern obj* l_lean_parser_term__parser__m_alternative;
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_expander_transformer__config__coe__frontend__config(obj* x_0) {
_start:
{
return x_0;
}
}
obj* _init_l_lean_expander_transform__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_expander_no__expansion___closed__1;
return x_2;
}
}
obj* l_lean_expander_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
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
x_17 = l_lean_file__map_to__position(x_11, x_16);
x_18 = lean::box(0);
x_19 = 2;
x_20 = l_string_join___closed__1;
x_21 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_18);
lean::cnstr_set(x_21, 3, x_20);
lean::cnstr_set(x_21, 4, x_3);
lean::cnstr_set_scalar(x_21, sizeof(void*)*5, x_19);
x_22 = x_21;
x_23 = lean::apply_2(x_5, lean::box(0), x_22);
return x_23;
}
}
obj* l_lean_expander_error___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_11, 0, x_3);
lean::closure_set(x_11, 1, x_2);
lean::closure_set(x_11, 2, x_5);
lean::closure_set(x_11, 3, x_6);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_1, x_11);
return x_12;
}
}
obj* l_lean_expander_error(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg), 7, 0);
return x_4;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg), 2, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg), 2, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_coe__binders__ext___rarg), 2, 0);
return x_2;
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_3, 2);
lean::inc(x_7);
lean::dec(x_3);
x_10 = l_lean_parser_syntax_get__pos(x_0);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = l_lean_file__map_to__position(x_7, x_12);
x_14 = lean::box(0);
x_15 = 2;
x_16 = l_string_join___closed__1;
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_5);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg), 4, 0);
return x_2;
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
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 3);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_11);
lean::cnstr_set(x_21, 2, x_16);
lean::cnstr_set(x_21, 3, x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_parser_syntax_get__pos(x_0);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_file__map_to__position(x_5, x_10);
x_12 = lean::box(0);
x_13 = 2;
x_14 = l_string_join___closed__1;
x_15 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_15, 0, x_3);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_12);
lean::cnstr_set(x_15, 3, x_14);
lean::cnstr_set(x_15, 4, x_1);
lean::cnstr_set_scalar(x_15, sizeof(void*)*5, x_13);
x_16 = x_15;
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg), 3, 0);
return x_2;
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
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
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
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_26; 
x_23 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_26 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_23, x_2, x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
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
obj* x_36; 
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
lean::dec(x_26);
x_14 = x_36;
goto lbl_15;
}
}
else
{
obj* x_42; 
lean::dec(x_13);
lean::dec(x_20);
lean::inc(x_3);
x_42 = l___private_init_lean_expander_1__pop__stx__arg(x_2, x_3);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_47 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_49 = x_42;
} else {
 lean::inc(x_47);
 lean::dec(x_42);
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
obj* x_51; 
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
x_16 = x_51;
goto lbl_17;
}
}
lbl_15:
{
obj* x_54; 
x_54 = lean::cnstr_get(x_9, 1);
lean::inc(x_54);
lean::dec(x_9);
if (lean::obj_tag(x_54) == 0)
{
obj* x_58; 
lean::dec(x_13);
x_58 = lean::cnstr_get(x_14, 1);
lean::inc(x_58);
lean::dec(x_14);
x_1 = x_11;
x_2 = x_58;
goto _start;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_set(x_54, 0, lean::box(0));
 x_64 = x_54;
} else {
 lean::inc(x_62);
 lean::dec(x_54);
 x_64 = lean::box(0);
}
switch (lean::obj_tag(x_62)) {
case 0:
{
obj* x_66; obj* x_70; 
lean::dec(x_62);
x_66 = lean::cnstr_get(x_14, 1);
lean::inc(x_66);
lean::dec(x_14);
lean::inc(x_3);
x_70 = l___private_init_lean_expander_1__pop__stx__arg(x_66, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_64);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_76 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_78 = x_70;
} else {
 lean::inc(x_76);
 lean::dec(x_70);
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
obj* x_80; obj* x_83; obj* x_85; obj* x_88; obj* x_90; obj* x_92; obj* x_95; obj* x_96; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_80 = lean::cnstr_get(x_70, 0);
lean::inc(x_80);
lean::dec(x_70);
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_80, 1);
lean::inc(x_85);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_85, 2);
lean::inc(x_92);
lean::dec(x_85);
x_95 = l_lean_parser_term_binder__ident_has__view;
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
lean::dec(x_95);
x_99 = lean::apply_1(x_96, x_83);
x_100 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_100);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_101);
lean::cnstr_set(x_103, 1, x_102);
x_104 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
if (lean::is_scalar(x_64)) {
 x_105 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_105 = x_64;
}
lean::cnstr_set(x_105, 0, x_104);
x_106 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_106, 0, x_88);
lean::cnstr_set(x_106, 1, x_90);
lean::cnstr_set(x_106, 2, x_92);
lean::cnstr_set(x_106, 3, x_105);
x_1 = x_11;
x_2 = x_106;
goto _start;
}
}
case 1:
{
obj* x_110; obj* x_114; 
lean::dec(x_13);
lean::dec(x_62);
x_110 = lean::cnstr_get(x_14, 1);
lean::inc(x_110);
lean::dec(x_14);
lean::inc(x_3);
x_114 = l___private_init_lean_expander_1__pop__stx__arg(x_110, x_3);
if (lean::obj_tag(x_114) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_64);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_119 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_121 = x_114;
} else {
 lean::inc(x_119);
 lean::dec(x_114);
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
obj* x_123; obj* x_126; obj* x_128; obj* x_131; obj* x_133; obj* x_135; obj* x_138; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_123 = lean::cnstr_get(x_114, 0);
lean::inc(x_123);
lean::dec(x_114);
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
x_131 = lean::cnstr_get(x_128, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_128, 2);
lean::inc(x_135);
lean::dec(x_128);
x_138 = l_lean_parser_term_binders_has__view;
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
lean::dec(x_138);
x_142 = lean::apply_1(x_139, x_126);
if (lean::is_scalar(x_64)) {
 x_143 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_143 = x_64;
}
lean::cnstr_set(x_143, 0, x_142);
x_144 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_144, 0, x_131);
lean::cnstr_set(x_144, 1, x_133);
lean::cnstr_set(x_144, 2, x_135);
lean::cnstr_set(x_144, 3, x_143);
x_1 = x_11;
x_2 = x_144;
goto _start;
}
}
default:
{
obj* x_147; obj* x_150; 
lean::dec(x_64);
x_147 = lean::cnstr_get(x_62, 0);
lean::inc(x_147);
lean::dec(x_62);
x_150 = lean::cnstr_get(x_147, 1);
lean::inc(x_150);
if (lean::obj_tag(x_150) == 0)
{
obj* x_152; obj* x_155; obj* x_159; 
x_152 = lean::cnstr_get(x_14, 1);
lean::inc(x_152);
lean::dec(x_14);
x_155 = lean::cnstr_get(x_147, 0);
lean::inc(x_155);
lean::dec(x_147);
lean::inc(x_3);
x_159 = l___private_init_lean_expander_1__pop__stx__arg(x_152, x_3);
if (lean::obj_tag(x_159) == 0)
{
obj* x_165; obj* x_167; obj* x_168; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_155);
x_165 = lean::cnstr_get(x_159, 0);
if (lean::is_exclusive(x_159)) {
 x_167 = x_159;
} else {
 lean::inc(x_165);
 lean::dec(x_159);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
return x_168;
}
else
{
obj* x_169; obj* x_172; obj* x_174; obj* x_176; obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_184; obj* x_185; obj* x_188; 
x_169 = lean::cnstr_get(x_159, 0);
lean::inc(x_169);
lean::dec(x_159);
x_172 = lean::cnstr_get(x_169, 0);
x_174 = lean::cnstr_get(x_169, 1);
if (lean::is_exclusive(x_169)) {
 x_176 = x_169;
} else {
 lean::inc(x_172);
 lean::inc(x_174);
 lean::dec(x_169);
 x_176 = lean::box(0);
}
x_177 = lean::cnstr_get(x_174, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_174, 1);
lean::inc(x_179);
if (lean::is_scalar(x_176)) {
 x_181 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_181 = x_176;
}
lean::cnstr_set(x_181, 0, x_155);
lean::cnstr_set(x_181, 1, x_172);
x_182 = lean::cnstr_get(x_174, 2);
lean::inc(x_182);
if (lean::is_scalar(x_13)) {
 x_184 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_184 = x_13;
}
lean::cnstr_set(x_184, 0, x_181);
lean::cnstr_set(x_184, 1, x_182);
x_185 = lean::cnstr_get(x_174, 3);
lean::inc(x_185);
lean::dec(x_174);
x_188 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_188, 0, x_177);
lean::cnstr_set(x_188, 1, x_179);
lean::cnstr_set(x_188, 2, x_184);
lean::cnstr_set(x_188, 3, x_185);
x_1 = x_11;
x_2 = x_188;
goto _start;
}
}
else
{
obj* x_190; obj* x_193; 
x_190 = lean::cnstr_get(x_150, 0);
lean::inc(x_190);
lean::dec(x_150);
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
switch (lean::obj_tag(x_193)) {
case 0:
{
obj* x_197; obj* x_200; obj* x_204; 
lean::dec(x_193);
x_197 = lean::cnstr_get(x_14, 1);
lean::inc(x_197);
lean::dec(x_14);
x_200 = lean::cnstr_get(x_147, 0);
lean::inc(x_200);
lean::dec(x_147);
lean::inc(x_3);
x_204 = l___private_init_lean_expander_1__pop__stx__arg(x_197, x_3);
if (lean::obj_tag(x_204) == 0)
{
obj* x_210; obj* x_212; obj* x_213; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_200);
x_210 = lean::cnstr_get(x_204, 0);
if (lean::is_exclusive(x_204)) {
 x_212 = x_204;
} else {
 lean::inc(x_210);
 lean::dec(x_204);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
return x_213;
}
else
{
obj* x_214; obj* x_217; obj* x_219; obj* x_221; obj* x_222; obj* x_224; obj* x_226; obj* x_227; obj* x_229; obj* x_230; obj* x_233; 
x_214 = lean::cnstr_get(x_204, 0);
lean::inc(x_214);
lean::dec(x_204);
x_217 = lean::cnstr_get(x_214, 0);
x_219 = lean::cnstr_get(x_214, 1);
if (lean::is_exclusive(x_214)) {
 x_221 = x_214;
} else {
 lean::inc(x_217);
 lean::inc(x_219);
 lean::dec(x_214);
 x_221 = lean::box(0);
}
x_222 = lean::cnstr_get(x_219, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_219, 1);
lean::inc(x_224);
if (lean::is_scalar(x_221)) {
 x_226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_226 = x_221;
}
lean::cnstr_set(x_226, 0, x_200);
lean::cnstr_set(x_226, 1, x_217);
x_227 = lean::cnstr_get(x_219, 2);
lean::inc(x_227);
if (lean::is_scalar(x_13)) {
 x_229 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_229 = x_13;
}
lean::cnstr_set(x_229, 0, x_226);
lean::cnstr_set(x_229, 1, x_227);
x_230 = lean::cnstr_get(x_219, 3);
lean::inc(x_230);
lean::dec(x_219);
x_233 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_233, 0, x_222);
lean::cnstr_set(x_233, 1, x_224);
lean::cnstr_set(x_233, 2, x_229);
lean::cnstr_set(x_233, 3, x_230);
x_1 = x_11;
x_2 = x_233;
goto _start;
}
}
case 2:
{
obj* x_235; obj* x_238; obj* x_241; obj* x_245; 
x_235 = lean::cnstr_get(x_14, 1);
lean::inc(x_235);
lean::dec(x_14);
x_238 = lean::cnstr_get(x_147, 0);
lean::inc(x_238);
lean::dec(x_147);
x_241 = lean::cnstr_get(x_193, 0);
lean::inc(x_241);
lean::dec(x_193);
lean::inc(x_3);
x_245 = l___private_init_lean_expander_1__pop__stx__arg(x_235, x_3);
if (lean::obj_tag(x_245) == 0)
{
obj* x_252; obj* x_254; obj* x_255; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_238);
lean::dec(x_241);
x_252 = lean::cnstr_get(x_245, 0);
if (lean::is_exclusive(x_245)) {
 x_254 = x_245;
} else {
 lean::inc(x_252);
 lean::dec(x_245);
 x_254 = lean::box(0);
}
if (lean::is_scalar(x_254)) {
 x_255 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_255 = x_254;
}
lean::cnstr_set(x_255, 0, x_252);
return x_255;
}
else
{
obj* x_256; obj* x_259; obj* x_261; 
x_256 = lean::cnstr_get(x_245, 0);
lean::inc(x_256);
lean::dec(x_245);
x_259 = lean::cnstr_get(x_256, 1);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_259, 3);
lean::inc(x_261);
if (lean::obj_tag(x_261) == 0)
{
obj* x_267; obj* x_270; 
lean::dec(x_13);
lean::dec(x_238);
lean::dec(x_241);
lean::dec(x_256);
x_267 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_270 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_267, x_259, x_3);
if (lean::obj_tag(x_270) == 0)
{
obj* x_274; obj* x_276; obj* x_277; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_274 = lean::cnstr_get(x_270, 0);
if (lean::is_exclusive(x_270)) {
 x_276 = x_270;
} else {
 lean::inc(x_274);
 lean::dec(x_270);
 x_276 = lean::box(0);
}
if (lean::is_scalar(x_276)) {
 x_277 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_277 = x_276;
}
lean::cnstr_set(x_277, 0, x_274);
return x_277;
}
else
{
obj* x_278; obj* x_281; 
x_278 = lean::cnstr_get(x_270, 0);
lean::inc(x_278);
lean::dec(x_270);
x_281 = lean::cnstr_get(x_278, 1);
lean::inc(x_281);
lean::dec(x_278);
x_1 = x_11;
x_2 = x_281;
goto _start;
}
}
else
{
obj* x_285; obj* x_287; obj* x_288; obj* x_290; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_298; obj* x_301; obj* x_302; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_312; obj* x_313; obj* x_314; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_285 = lean::cnstr_get(x_256, 0);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 1);
 x_287 = x_256;
} else {
 lean::inc(x_285);
 lean::dec(x_256);
 x_287 = lean::box(0);
}
x_288 = lean::cnstr_get(x_259, 0);
x_290 = lean::cnstr_get(x_259, 1);
x_292 = lean::cnstr_get(x_259, 2);
if (lean::is_exclusive(x_259)) {
 lean::cnstr_release(x_259, 3);
 x_294 = x_259;
} else {
 lean::inc(x_288);
 lean::inc(x_290);
 lean::inc(x_292);
 lean::dec(x_259);
 x_294 = lean::box(0);
}
x_295 = lean::cnstr_get(x_261, 0);
lean::inc(x_295);
x_297 = l_lean_parser_term_lambda_has__view;
x_298 = lean::cnstr_get(x_297, 1);
lean::inc(x_298);
lean::dec(x_297);
x_301 = lean::box(0);
x_302 = lean::cnstr_get(x_241, 3);
lean::inc(x_302);
x_304 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_305 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_305 = x_13;
}
lean::cnstr_set(x_305, 0, x_302);
lean::cnstr_set(x_305, 1, x_304);
x_306 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_305);
x_307 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_307, 0, x_306);
lean::cnstr_set(x_307, 1, x_301);
x_308 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_308, 0, x_307);
x_309 = lean::cnstr_get(x_241, 5);
lean::inc(x_309);
lean::dec(x_241);
x_312 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_313 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_314 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_308);
lean::cnstr_set(x_314, 2, x_313);
lean::cnstr_set(x_314, 3, x_309);
lean::inc(x_298);
x_316 = lean::apply_1(x_298, x_314);
x_317 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_317, 0, x_312);
lean::cnstr_set(x_317, 1, x_295);
lean::cnstr_set(x_317, 2, x_313);
lean::cnstr_set(x_317, 3, x_285);
x_318 = lean::apply_1(x_298, x_317);
x_319 = l_lean_parser_term_app_has__view;
x_320 = lean::cnstr_get(x_319, 1);
lean::inc(x_320);
lean::dec(x_319);
x_323 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_323, 0, x_316);
lean::cnstr_set(x_323, 1, x_318);
x_324 = lean::apply_1(x_320, x_323);
if (lean::is_scalar(x_287)) {
 x_325 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_325 = x_287;
}
lean::cnstr_set(x_325, 0, x_238);
lean::cnstr_set(x_325, 1, x_324);
x_326 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_326, 0, x_325);
lean::cnstr_set(x_326, 1, x_292);
if (lean::is_scalar(x_294)) {
 x_327 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_327 = x_294;
}
lean::cnstr_set(x_327, 0, x_288);
lean::cnstr_set(x_327, 1, x_290);
lean::cnstr_set(x_327, 2, x_326);
lean::cnstr_set(x_327, 3, x_261);
x_1 = x_11;
x_2 = x_327;
goto _start;
}
}
}
default:
{
obj* x_332; obj* x_335; obj* x_338; 
lean::dec(x_13);
lean::dec(x_147);
lean::dec(x_193);
x_332 = lean::cnstr_get(x_14, 1);
lean::inc(x_332);
lean::dec(x_14);
x_335 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_338 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_335, x_332, x_3);
if (lean::obj_tag(x_338) == 0)
{
obj* x_342; obj* x_344; obj* x_345; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_342 = lean::cnstr_get(x_338, 0);
if (lean::is_exclusive(x_338)) {
 x_344 = x_338;
} else {
 lean::inc(x_342);
 lean::dec(x_338);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_342);
return x_345;
}
else
{
obj* x_346; obj* x_349; 
x_346 = lean::cnstr_get(x_338, 0);
lean::inc(x_346);
lean::dec(x_338);
x_349 = lean::cnstr_get(x_346, 1);
lean::inc(x_349);
lean::dec(x_346);
x_1 = x_11;
x_2 = x_349;
goto _start;
}
}
}
}
}
}
}
}
lbl_17:
{
obj* x_353; 
x_353 = lean::cnstr_get(x_9, 1);
lean::inc(x_353);
lean::dec(x_9);
if (lean::obj_tag(x_353) == 0)
{
obj* x_356; 
x_356 = lean::cnstr_get(x_16, 1);
lean::inc(x_356);
lean::dec(x_16);
x_1 = x_11;
x_2 = x_356;
goto _start;
}
else
{
obj* x_360; obj* x_362; 
x_360 = lean::cnstr_get(x_353, 0);
if (lean::is_exclusive(x_353)) {
 lean::cnstr_set(x_353, 0, lean::box(0));
 x_362 = x_353;
} else {
 lean::inc(x_360);
 lean::dec(x_353);
 x_362 = lean::box(0);
}
switch (lean::obj_tag(x_360)) {
case 0:
{
obj* x_364; obj* x_368; 
lean::dec(x_360);
x_364 = lean::cnstr_get(x_16, 1);
lean::inc(x_364);
lean::dec(x_16);
lean::inc(x_3);
x_368 = l___private_init_lean_expander_1__pop__stx__arg(x_364, x_3);
if (lean::obj_tag(x_368) == 0)
{
obj* x_373; obj* x_375; obj* x_376; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_362);
x_373 = lean::cnstr_get(x_368, 0);
if (lean::is_exclusive(x_368)) {
 x_375 = x_368;
} else {
 lean::inc(x_373);
 lean::dec(x_368);
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
obj* x_377; obj* x_380; obj* x_382; obj* x_385; obj* x_387; obj* x_389; obj* x_392; obj* x_393; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; 
x_377 = lean::cnstr_get(x_368, 0);
lean::inc(x_377);
lean::dec(x_368);
x_380 = lean::cnstr_get(x_377, 0);
lean::inc(x_380);
x_382 = lean::cnstr_get(x_377, 1);
lean::inc(x_382);
lean::dec(x_377);
x_385 = lean::cnstr_get(x_382, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_382, 1);
lean::inc(x_387);
x_389 = lean::cnstr_get(x_382, 2);
lean::inc(x_389);
lean::dec(x_382);
x_392 = l_lean_parser_term_binder__ident_has__view;
x_393 = lean::cnstr_get(x_392, 0);
lean::inc(x_393);
lean::dec(x_392);
x_396 = lean::apply_1(x_393, x_380);
x_397 = lean::box(0);
x_398 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_397);
x_399 = lean::box(0);
x_400 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_400, 0, x_398);
lean::cnstr_set(x_400, 1, x_399);
x_401 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_401, 0, x_400);
if (lean::is_scalar(x_362)) {
 x_402 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_402 = x_362;
}
lean::cnstr_set(x_402, 0, x_401);
x_403 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_403, 0, x_385);
lean::cnstr_set(x_403, 1, x_387);
lean::cnstr_set(x_403, 2, x_389);
lean::cnstr_set(x_403, 3, x_402);
x_1 = x_11;
x_2 = x_403;
goto _start;
}
}
case 1:
{
obj* x_406; obj* x_410; 
lean::dec(x_360);
x_406 = lean::cnstr_get(x_16, 1);
lean::inc(x_406);
lean::dec(x_16);
lean::inc(x_3);
x_410 = l___private_init_lean_expander_1__pop__stx__arg(x_406, x_3);
if (lean::obj_tag(x_410) == 0)
{
obj* x_415; obj* x_417; obj* x_418; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_362);
x_415 = lean::cnstr_get(x_410, 0);
if (lean::is_exclusive(x_410)) {
 x_417 = x_410;
} else {
 lean::inc(x_415);
 lean::dec(x_410);
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
obj* x_419; obj* x_422; obj* x_424; obj* x_427; obj* x_429; obj* x_431; obj* x_434; obj* x_435; obj* x_438; obj* x_439; obj* x_440; 
x_419 = lean::cnstr_get(x_410, 0);
lean::inc(x_419);
lean::dec(x_410);
x_422 = lean::cnstr_get(x_419, 0);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_419, 1);
lean::inc(x_424);
lean::dec(x_419);
x_427 = lean::cnstr_get(x_424, 0);
lean::inc(x_427);
x_429 = lean::cnstr_get(x_424, 1);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_424, 2);
lean::inc(x_431);
lean::dec(x_424);
x_434 = l_lean_parser_term_binders_has__view;
x_435 = lean::cnstr_get(x_434, 0);
lean::inc(x_435);
lean::dec(x_434);
x_438 = lean::apply_1(x_435, x_422);
if (lean::is_scalar(x_362)) {
 x_439 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_439 = x_362;
}
lean::cnstr_set(x_439, 0, x_438);
x_440 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_440, 0, x_427);
lean::cnstr_set(x_440, 1, x_429);
lean::cnstr_set(x_440, 2, x_431);
lean::cnstr_set(x_440, 3, x_439);
x_1 = x_11;
x_2 = x_440;
goto _start;
}
}
default:
{
obj* x_443; obj* x_446; 
lean::dec(x_362);
x_443 = lean::cnstr_get(x_360, 0);
lean::inc(x_443);
lean::dec(x_360);
x_446 = lean::cnstr_get(x_443, 1);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_448; obj* x_451; obj* x_455; 
x_448 = lean::cnstr_get(x_16, 1);
lean::inc(x_448);
lean::dec(x_16);
x_451 = lean::cnstr_get(x_443, 0);
lean::inc(x_451);
lean::dec(x_443);
lean::inc(x_3);
x_455 = l___private_init_lean_expander_1__pop__stx__arg(x_448, x_3);
if (lean::obj_tag(x_455) == 0)
{
obj* x_460; obj* x_462; obj* x_463; 
lean::dec(x_451);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_460 = lean::cnstr_get(x_455, 0);
if (lean::is_exclusive(x_455)) {
 x_462 = x_455;
} else {
 lean::inc(x_460);
 lean::dec(x_455);
 x_462 = lean::box(0);
}
if (lean::is_scalar(x_462)) {
 x_463 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_463 = x_462;
}
lean::cnstr_set(x_463, 0, x_460);
return x_463;
}
else
{
obj* x_464; obj* x_467; obj* x_469; obj* x_471; obj* x_472; obj* x_474; obj* x_476; obj* x_477; obj* x_479; obj* x_480; obj* x_483; 
x_464 = lean::cnstr_get(x_455, 0);
lean::inc(x_464);
lean::dec(x_455);
x_467 = lean::cnstr_get(x_464, 0);
x_469 = lean::cnstr_get(x_464, 1);
if (lean::is_exclusive(x_464)) {
 x_471 = x_464;
} else {
 lean::inc(x_467);
 lean::inc(x_469);
 lean::dec(x_464);
 x_471 = lean::box(0);
}
x_472 = lean::cnstr_get(x_469, 0);
lean::inc(x_472);
x_474 = lean::cnstr_get(x_469, 1);
lean::inc(x_474);
if (lean::is_scalar(x_471)) {
 x_476 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_476 = x_471;
}
lean::cnstr_set(x_476, 0, x_451);
lean::cnstr_set(x_476, 1, x_467);
x_477 = lean::cnstr_get(x_469, 2);
lean::inc(x_477);
x_479 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_479, 0, x_476);
lean::cnstr_set(x_479, 1, x_477);
x_480 = lean::cnstr_get(x_469, 3);
lean::inc(x_480);
lean::dec(x_469);
x_483 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_483, 0, x_472);
lean::cnstr_set(x_483, 1, x_474);
lean::cnstr_set(x_483, 2, x_479);
lean::cnstr_set(x_483, 3, x_480);
x_1 = x_11;
x_2 = x_483;
goto _start;
}
}
else
{
obj* x_485; obj* x_488; 
x_485 = lean::cnstr_get(x_446, 0);
lean::inc(x_485);
lean::dec(x_446);
x_488 = lean::cnstr_get(x_485, 1);
lean::inc(x_488);
lean::dec(x_485);
switch (lean::obj_tag(x_488)) {
case 0:
{
obj* x_492; obj* x_495; obj* x_499; 
lean::dec(x_488);
x_492 = lean::cnstr_get(x_16, 1);
lean::inc(x_492);
lean::dec(x_16);
x_495 = lean::cnstr_get(x_443, 0);
lean::inc(x_495);
lean::dec(x_443);
lean::inc(x_3);
x_499 = l___private_init_lean_expander_1__pop__stx__arg(x_492, x_3);
if (lean::obj_tag(x_499) == 0)
{
obj* x_504; obj* x_506; obj* x_507; 
lean::dec(x_495);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_504 = lean::cnstr_get(x_499, 0);
if (lean::is_exclusive(x_499)) {
 x_506 = x_499;
} else {
 lean::inc(x_504);
 lean::dec(x_499);
 x_506 = lean::box(0);
}
if (lean::is_scalar(x_506)) {
 x_507 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_507 = x_506;
}
lean::cnstr_set(x_507, 0, x_504);
return x_507;
}
else
{
obj* x_508; obj* x_511; obj* x_513; obj* x_515; obj* x_516; obj* x_518; obj* x_520; obj* x_521; obj* x_523; obj* x_524; obj* x_527; 
x_508 = lean::cnstr_get(x_499, 0);
lean::inc(x_508);
lean::dec(x_499);
x_511 = lean::cnstr_get(x_508, 0);
x_513 = lean::cnstr_get(x_508, 1);
if (lean::is_exclusive(x_508)) {
 x_515 = x_508;
} else {
 lean::inc(x_511);
 lean::inc(x_513);
 lean::dec(x_508);
 x_515 = lean::box(0);
}
x_516 = lean::cnstr_get(x_513, 0);
lean::inc(x_516);
x_518 = lean::cnstr_get(x_513, 1);
lean::inc(x_518);
if (lean::is_scalar(x_515)) {
 x_520 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_520 = x_515;
}
lean::cnstr_set(x_520, 0, x_495);
lean::cnstr_set(x_520, 1, x_511);
x_521 = lean::cnstr_get(x_513, 2);
lean::inc(x_521);
x_523 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_523, 0, x_520);
lean::cnstr_set(x_523, 1, x_521);
x_524 = lean::cnstr_get(x_513, 3);
lean::inc(x_524);
lean::dec(x_513);
x_527 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_527, 0, x_516);
lean::cnstr_set(x_527, 1, x_518);
lean::cnstr_set(x_527, 2, x_523);
lean::cnstr_set(x_527, 3, x_524);
x_1 = x_11;
x_2 = x_527;
goto _start;
}
}
case 2:
{
obj* x_529; obj* x_532; obj* x_535; obj* x_539; 
x_529 = lean::cnstr_get(x_16, 1);
lean::inc(x_529);
lean::dec(x_16);
x_532 = lean::cnstr_get(x_443, 0);
lean::inc(x_532);
lean::dec(x_443);
x_535 = lean::cnstr_get(x_488, 0);
lean::inc(x_535);
lean::dec(x_488);
lean::inc(x_3);
x_539 = l___private_init_lean_expander_1__pop__stx__arg(x_529, x_3);
if (lean::obj_tag(x_539) == 0)
{
obj* x_545; obj* x_547; obj* x_548; 
lean::dec(x_532);
lean::dec(x_535);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_545 = lean::cnstr_get(x_539, 0);
if (lean::is_exclusive(x_539)) {
 x_547 = x_539;
} else {
 lean::inc(x_545);
 lean::dec(x_539);
 x_547 = lean::box(0);
}
if (lean::is_scalar(x_547)) {
 x_548 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_548 = x_547;
}
lean::cnstr_set(x_548, 0, x_545);
return x_548;
}
else
{
obj* x_549; obj* x_552; obj* x_554; 
x_549 = lean::cnstr_get(x_539, 0);
lean::inc(x_549);
lean::dec(x_539);
x_552 = lean::cnstr_get(x_549, 1);
lean::inc(x_552);
x_554 = lean::cnstr_get(x_552, 3);
lean::inc(x_554);
if (lean::obj_tag(x_554) == 0)
{
obj* x_559; obj* x_562; 
lean::dec(x_532);
lean::dec(x_535);
lean::dec(x_549);
x_559 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_562 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_559, x_552, x_3);
if (lean::obj_tag(x_562) == 0)
{
obj* x_566; obj* x_568; obj* x_569; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_566 = lean::cnstr_get(x_562, 0);
if (lean::is_exclusive(x_562)) {
 x_568 = x_562;
} else {
 lean::inc(x_566);
 lean::dec(x_562);
 x_568 = lean::box(0);
}
if (lean::is_scalar(x_568)) {
 x_569 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_569 = x_568;
}
lean::cnstr_set(x_569, 0, x_566);
return x_569;
}
else
{
obj* x_570; obj* x_573; 
x_570 = lean::cnstr_get(x_562, 0);
lean::inc(x_570);
lean::dec(x_562);
x_573 = lean::cnstr_get(x_570, 1);
lean::inc(x_573);
lean::dec(x_570);
x_1 = x_11;
x_2 = x_573;
goto _start;
}
}
else
{
obj* x_577; obj* x_579; obj* x_580; obj* x_582; obj* x_584; obj* x_586; obj* x_587; obj* x_589; obj* x_590; obj* x_593; obj* x_594; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_604; obj* x_605; obj* x_606; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; 
x_577 = lean::cnstr_get(x_549, 0);
if (lean::is_exclusive(x_549)) {
 lean::cnstr_release(x_549, 1);
 x_579 = x_549;
} else {
 lean::inc(x_577);
 lean::dec(x_549);
 x_579 = lean::box(0);
}
x_580 = lean::cnstr_get(x_552, 0);
x_582 = lean::cnstr_get(x_552, 1);
x_584 = lean::cnstr_get(x_552, 2);
if (lean::is_exclusive(x_552)) {
 lean::cnstr_release(x_552, 3);
 x_586 = x_552;
} else {
 lean::inc(x_580);
 lean::inc(x_582);
 lean::inc(x_584);
 lean::dec(x_552);
 x_586 = lean::box(0);
}
x_587 = lean::cnstr_get(x_554, 0);
lean::inc(x_587);
x_589 = l_lean_parser_term_lambda_has__view;
x_590 = lean::cnstr_get(x_589, 1);
lean::inc(x_590);
lean::dec(x_589);
x_593 = lean::box(0);
x_594 = lean::cnstr_get(x_535, 3);
lean::inc(x_594);
x_596 = lean::box(0);
x_597 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_597, 0, x_594);
lean::cnstr_set(x_597, 1, x_596);
x_598 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_597);
x_599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_593);
x_600 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_600, 0, x_599);
x_601 = lean::cnstr_get(x_535, 5);
lean::inc(x_601);
lean::dec(x_535);
x_604 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_605 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_606 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_606, 0, x_604);
lean::cnstr_set(x_606, 1, x_600);
lean::cnstr_set(x_606, 2, x_605);
lean::cnstr_set(x_606, 3, x_601);
lean::inc(x_590);
x_608 = lean::apply_1(x_590, x_606);
x_609 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_609, 0, x_604);
lean::cnstr_set(x_609, 1, x_587);
lean::cnstr_set(x_609, 2, x_605);
lean::cnstr_set(x_609, 3, x_577);
x_610 = lean::apply_1(x_590, x_609);
x_611 = l_lean_parser_term_app_has__view;
x_612 = lean::cnstr_get(x_611, 1);
lean::inc(x_612);
lean::dec(x_611);
x_615 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_615, 0, x_608);
lean::cnstr_set(x_615, 1, x_610);
x_616 = lean::apply_1(x_612, x_615);
if (lean::is_scalar(x_579)) {
 x_617 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_617 = x_579;
}
lean::cnstr_set(x_617, 0, x_532);
lean::cnstr_set(x_617, 1, x_616);
x_618 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_618, 0, x_617);
lean::cnstr_set(x_618, 1, x_584);
if (lean::is_scalar(x_586)) {
 x_619 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_619 = x_586;
}
lean::cnstr_set(x_619, 0, x_580);
lean::cnstr_set(x_619, 1, x_582);
lean::cnstr_set(x_619, 2, x_618);
lean::cnstr_set(x_619, 3, x_554);
x_1 = x_11;
x_2 = x_619;
goto _start;
}
}
}
default:
{
obj* x_623; obj* x_626; obj* x_629; 
lean::dec(x_488);
lean::dec(x_443);
x_623 = lean::cnstr_get(x_16, 1);
lean::inc(x_623);
lean::dec(x_16);
x_626 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_629 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_626, x_623, x_3);
if (lean::obj_tag(x_629) == 0)
{
obj* x_633; obj* x_635; obj* x_636; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_633 = lean::cnstr_get(x_629, 0);
if (lean::is_exclusive(x_629)) {
 x_635 = x_629;
} else {
 lean::inc(x_633);
 lean::dec(x_629);
 x_635 = lean::box(0);
}
if (lean::is_scalar(x_635)) {
 x_636 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_636 = x_635;
}
lean::cnstr_set(x_636, 0, x_633);
return x_636;
}
else
{
obj* x_637; obj* x_640; 
x_637 = lean::cnstr_get(x_629, 0);
lean::inc(x_637);
lean::dec(x_629);
x_640 = lean::cnstr_get(x_637, 1);
lean::inc(x_640);
lean::dec(x_637);
x_1 = x_11;
x_2 = x_640;
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
obj* x_1; uint8 x_3; 
x_1 = l_lean_parser_ident__univs;
lean::inc(x_0);
x_3 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_3 == 0)
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_6 = l_lean_parser_ident__univs_has__view;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; uint8 x_14; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean_name_dec_eq(x_9, x_1);
lean::dec(x_9);
if (x_14 == 0)
{
lean::dec(x_11);
x_0 = x_6;
goto _start;
}
else
{
obj* x_20; 
lean::dec(x_6);
lean::dec(x_1);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_11);
return x_20;
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
return x_16;
}
else
{
obj* x_20; 
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_0);
x_20 = lean::box(0);
return x_20;
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
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_23; obj* x_25; 
x_8 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::box(0);
x_15 = lean::box(0);
lean::inc(x_1);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_14);
lean::cnstr_set(x_17, 3, x_15);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_17);
x_25 = x_28;
goto lbl_26;
}
else
{
obj* x_29; obj* x_33; 
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
lean::dec(x_23);
lean::inc(x_2);
x_33 = l___private_init_lean_expander_1__pop__stx__arg(x_17, x_2);
if (lean::obj_tag(x_33) == 0)
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_18);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_21);
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
lean::cnstr_set(x_56, 0, x_29);
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
x_25 = x_65;
goto lbl_26;
}
}
lbl_26:
{
obj* x_66; obj* x_69; obj* x_72; 
x_66 = lean::cnstr_get(x_25, 1);
lean::inc(x_66);
lean::dec(x_25);
x_69 = lean::cnstr_get(x_21, 1);
lean::inc(x_69);
lean::dec(x_21);
x_72 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_69, x_66, x_2);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_18);
lean::dec(x_10);
x_75 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_77 = x_72;
} else {
 lean::inc(x_75);
 lean::dec(x_72);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
return x_78;
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_93; obj* x_94; obj* x_95; 
x_79 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_81 = x_72;
} else {
 lean::inc(x_79);
 lean::dec(x_72);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_85);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1), 2, 1);
lean::closure_set(x_89, 0, x_88);
x_90 = lean::cnstr_get(x_18, 4);
lean::inc(x_90);
lean::dec(x_18);
x_93 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_89, x_90);
if (lean::is_scalar(x_10)) {
 x_94 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_94 = x_10;
}
lean::cnstr_set(x_94, 0, x_93);
if (lean::is_scalar(x_81)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_81;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
}
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("b");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_7 = l_lean_name_to__string__with__sep___main(x_5, x_4);
x_8 = l_lean_parser_substring_of__string(x_7);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_1);
lean::cnstr_set(x_9, 4, x_1);
return x_9;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__2), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("b");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
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
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = lean::box(0);
x_13 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_14 = l_option_map___rarg(x_13, x_5);
x_15 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_16 = l_option_map___rarg(x_15, x_14);
x_17 = l_lean_expander_mixfix__to__notation__spec___closed__5;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_12);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
case 3:
{
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_3 = x_27;
goto lbl_4;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; uint8 x_35; 
x_28 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_30 = x_5;
} else {
 lean::inc(x_28);
 lean::dec(x_5);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
x_33 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_31);
x_34 = lean::mk_nat_obj(0u);
x_35 = lean::nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_2);
lean::dec(x_28);
x_38 = lean::mk_nat_obj(1u);
x_39 = lean::nat_sub(x_33, x_38);
lean::dec(x_33);
x_41 = l_lean_parser_number_view_of__nat(x_39);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
if (lean::is_scalar(x_30)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_30;
}
lean::cnstr_set(x_47, 0, x_46);
x_3 = x_47;
goto lbl_4;
}
else
{
obj* x_50; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_30);
lean::dec(x_33);
x_50 = l_lean_parser_command_notation__spec_precedence_has__view;
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
lean::dec(x_50);
x_54 = lean::apply_1(x_51, x_28);
x_55 = l_lean_expander_mixfix__to__notation__spec___closed__6;
x_56 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_54, x_55, x_2);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_1);
x_58 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_60 = x_56;
} else {
 lean::inc(x_58);
 lean::dec(x_56);
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
obj* x_62; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
x_3 = x_62;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
x_68 = lean::box(0);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_1);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_69);
x_72 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
default:
{
obj* x_77; 
lean::dec(x_0);
lean::dec(x_2);
x_77 = lean::box(0);
x_7 = x_77;
goto lbl_8;
}
}
lbl_4:
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_78 = lean::box(0);
x_79 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_3);
x_81 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_1);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_78);
x_85 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_84);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
return x_87;
}
lbl_8:
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_7);
x_89 = lean::box(0);
x_90 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_91 = l_option_map___rarg(x_90, x_5);
x_92 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_93 = l_option_map___rarg(x_92, x_91);
x_94 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_93);
x_96 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
x_98 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_98, 0, x_1);
lean::cnstr_set(x_98, 1, x_97);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_89);
x_100 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_11 = l_lean_parser_substring_of__string(x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_7);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
x_15 = lean::apply_1(x_2, x_14);
return x_15;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_12 = l_lean_parser_substring_of__string(x_11);
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_13, 3, x_5);
lean::cnstr_set(x_13, 4, x_5);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
x_15 = lean::apply_1(x_2, x_14);
return x_15;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
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
x_11 = l_lean_parser_substring_of__string(x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_7);
lean::cnstr_set(x_13, 3, x_12);
lean::cnstr_set(x_13, 4, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
x_15 = lean::apply_1(x_2, x_14);
return x_15;
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
obj* x_23; 
lean::inc(x_9);
x_23 = l_lean_expander_mixfix__to__notation__spec(x_9, x_11, x_1);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_6);
lean::dec(x_9);
x_26 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_28 = x_23;
} else {
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
return x_29;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_39; 
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
x_33 = l_lean_parser_command_notation_has__view;
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
x_37 = lean::cnstr_get(x_6, 0);
lean::inc(x_37);
switch (lean::obj_tag(x_9)) {
case 0:
{
obj* x_43; obj* x_44; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_9);
lean::dec(x_32);
x_43 = l_lean_parser_term_app_has__view;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
lean::dec(x_43);
x_47 = lean::cnstr_get(x_6, 4);
lean::inc(x_47);
lean::dec(x_6);
x_50 = l_lean_expander_mixfix_transform___closed__5;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::apply_1(x_44, x_51);
x_53 = l_lean_expander_mixfix_transform___closed__3;
x_54 = l_lean_expander_mixfix_transform___closed__4;
x_55 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_55, 0, x_37);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_30);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set(x_55, 4, x_52);
x_56 = lean::apply_1(x_34, x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
case 4:
{
obj* x_61; obj* x_62; obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_9);
lean::dec(x_32);
x_61 = l_lean_parser_term_app_has__view;
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
lean::dec(x_61);
x_65 = lean::cnstr_get(x_6, 4);
lean::inc(x_65);
lean::dec(x_6);
x_68 = l_lean_expander_mixfix_transform___closed__1;
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::apply_1(x_62, x_69);
x_71 = l_lean_expander_mixfix_transform___closed__3;
x_72 = l_lean_expander_mixfix_transform___closed__4;
x_73 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_73, 0, x_37);
lean::cnstr_set(x_73, 1, x_71);
lean::cnstr_set(x_73, 2, x_30);
lean::cnstr_set(x_73, 3, x_72);
lean::cnstr_set(x_73, 4, x_70);
x_74 = lean::apply_1(x_34, x_73);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
default:
{
obj* x_78; 
lean::dec(x_9);
x_78 = lean::box(0);
x_39 = x_78;
goto lbl_40;
}
}
lbl_40:
{
obj* x_80; obj* x_81; obj* x_84; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_39);
x_80 = l_lean_parser_term_app_has__view;
x_81 = lean::cnstr_get(x_80, 1);
lean::inc(x_81);
lean::dec(x_80);
x_84 = lean::cnstr_get(x_6, 4);
lean::inc(x_84);
lean::dec(x_6);
x_87 = l_lean_expander_mixfix_transform___closed__1;
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_84);
lean::cnstr_set(x_88, 1, x_87);
lean::inc(x_81);
x_90 = lean::apply_1(x_81, x_88);
x_91 = l_lean_expander_mixfix_transform___closed__2;
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::apply_1(x_81, x_92);
x_94 = l_lean_expander_mixfix_transform___closed__3;
x_95 = l_lean_expander_mixfix_transform___closed__4;
x_96 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_96, 0, x_37);
lean::cnstr_set(x_96, 1, x_94);
lean::cnstr_set(x_96, 2, x_30);
lean::cnstr_set(x_96, 3, x_95);
lean::cnstr_set(x_96, 4, x_93);
x_97 = lean::apply_1(x_34, x_96);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
if (lean::is_scalar(x_32)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_32;
}
lean::cnstr_set(x_99, 0, x_98);
return x_99;
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
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_15 = x_12;
} else {
 lean::inc(x_13);
 lean::dec(x_12);
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
obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_command_reserve__notation_has__view;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_24 = l_lean_expander_reserve__mixfix_transform___closed__1;
x_25 = l_lean_expander_mixfix_transform___closed__3;
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set(x_26, 2, x_17);
x_27 = lean::apply_1(x_21, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_19)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_19;
}
lean::cnstr_set(x_29, 0, x_28);
return x_29;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
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
lean::dec(x_0);
return x_1;
}
else
{
obj* x_5; 
lean::dec(x_0);
x_5 = l_lean_expander_binder__ident__to__ident___main___closed__1;
return x_5;
}
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
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
return x_5;
}
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
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
x_8 = 0;
x_9 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
x_10 = l_lean_expander_mk__simple__binder(x_7, x_8, x_9);
x_11 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_6;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_12 = l_lean_expander_get__opt__type___main(x_10);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_14 = l_lean_expander_mk__simple__binder(x_13, x_0, x_12);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_9;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
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
obj* x_6; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_11 = x_3;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
x_17 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_22 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_23 = l_lean_expander_mk__simple__binder(x_22, x_0, x_21);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_0, x_1, x_2, x_9);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
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
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_17 = l_lean_expander_mk__simple__binder(x_16, x_0, x_15);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_0, x_1, x_7);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
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
lean::inc(x_1);
x_12 = l_lean_expander_mk__simple__binder(x_10, x_0, x_1);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_12);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_11 = l_lean_expander_get__opt__type___main(x_9);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_13 = 0;
x_14 = l_lean_expander_mk__simple__binder(x_12, x_13, x_11);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = l_lean_expander_get__opt__type___main(x_11);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
x_16 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_20 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_21 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_22 = 0;
x_23 = l_lean_expander_mk__simple__binder(x_21, x_22, x_20);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_8);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_16 = 0;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_14);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_0, x_6);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
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
x_10 = 0;
lean::inc(x_0);
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_0);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_12);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_11 = l_lean_expander_get__opt__type___main(x_9);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_13 = 1;
x_14 = l_lean_expander_mk__simple__binder(x_12, x_13, x_11);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = l_lean_expander_get__opt__type___main(x_11);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
x_16 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_20 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_21 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_22 = 1;
x_23 = l_lean_expander_mk__simple__binder(x_21, x_22, x_20);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_8);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_16 = 1;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_14);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_0, x_6);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
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
x_10 = 1;
lean::inc(x_0);
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_0);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_12);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_11 = l_lean_expander_get__opt__type___main(x_9);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_13 = 2;
x_14 = l_lean_expander_mk__simple__binder(x_12, x_13, x_11);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = l_lean_expander_get__opt__type___main(x_11);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
x_16 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_20 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_21 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_22 = 2;
x_23 = l_lean_expander_mk__simple__binder(x_21, x_22, x_20);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_8);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_16 = 2;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_14);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_0, x_6);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
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
x_10 = 2;
lean::inc(x_0);
x_12 = l_lean_expander_mk__simple__binder(x_9, x_10, x_0);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_12);
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
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_16 = 3;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_14);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_8;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
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
x_14 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_15 = 3;
x_16 = l_lean_expander_mk__simple__binder(x_14, x_15, x_13);
x_17 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8 x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_12 = l_lean_expander_get__opt__type___main(x_10);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_14 = l_lean_expander_mk__simple__binder(x_13, x_0, x_12);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_9;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_11 = x_3;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
x_17 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_22 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_23 = l_lean_expander_mk__simple__binder(x_22, x_0, x_21);
x_24 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_0, x_1, x_2, x_9);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
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
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_17 = l_lean_expander_mk__simple__binder(x_16, x_0, x_15);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_0, x_1, x_7);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
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
lean::inc(x_1);
x_12 = l_lean_expander_mk__simple__binder(x_10, x_0, x_1);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_12);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_2);
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
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_1);
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_18, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_21, 0);
lean::inc(x_28);
lean::dec(x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_28, 0);
lean::inc(x_32);
lean::dec(x_28);
x_35 = lean::cnstr_get(x_18, 0);
lean::inc(x_35);
x_37 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_18, x_32, x_35);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_18, 1);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_1);
x_42 = lean::cnstr_get(x_28, 0);
lean::inc(x_42);
lean::dec(x_28);
x_45 = lean::cnstr_get(x_18, 0);
lean::inc(x_45);
lean::dec(x_18);
x_48 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_42, x_45);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_39);
x_51 = l_lean_parser_term_binder__default_has__view;
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
lean::dec(x_51);
x_55 = lean::apply_1(x_52, x_28);
x_56 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_57 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_55, x_56, x_1);
if (lean::obj_tag(x_57) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_18);
x_59 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_61 = x_57;
} else {
 lean::inc(x_59);
 lean::dec(x_57);
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
obj* x_63; obj* x_65; obj* x_66; obj* x_69; obj* x_70; 
x_63 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_65 = x_57;
} else {
 lean::inc(x_63);
 lean::dec(x_57);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_18, 0);
lean::inc(x_66);
lean::dec(x_18);
x_69 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_63, x_66);
if (lean::is_scalar(x_65)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_65;
}
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
}
}
}
}
}
case 1:
{
obj* x_73; 
lean::dec(x_4);
lean::dec(x_0);
x_73 = lean::cnstr_get(x_6, 2);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_1);
x_76 = lean::cnstr_get(x_6, 0);
lean::inc(x_76);
x_78 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_76);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
else
{
obj* x_80; 
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
lean::dec(x_73);
if (lean::obj_tag(x_80) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_1);
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
lean::dec(x_80);
x_87 = lean::cnstr_get(x_6, 0);
lean::inc(x_87);
x_89 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_84, x_87);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
return x_90;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_6, 1);
lean::inc(x_91);
if (lean::obj_tag(x_91) == 0)
{
obj* x_94; obj* x_97; obj* x_100; obj* x_101; 
lean::dec(x_1);
x_94 = lean::cnstr_get(x_80, 0);
lean::inc(x_94);
lean::dec(x_80);
x_97 = lean::cnstr_get(x_6, 0);
lean::inc(x_97);
lean::dec(x_6);
x_100 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_94, x_97);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
else
{
obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_91);
x_103 = l_lean_parser_term_binder__default_has__view;
x_104 = lean::cnstr_get(x_103, 1);
lean::inc(x_104);
lean::dec(x_103);
x_107 = lean::apply_1(x_104, x_80);
x_108 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_109 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_107, x_108, x_1);
if (lean::obj_tag(x_109) == 0)
{
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_6);
x_111 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_113 = x_109;
} else {
 lean::inc(x_111);
 lean::dec(x_109);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
return x_114;
}
else
{
obj* x_115; obj* x_117; obj* x_118; obj* x_121; obj* x_122; 
x_115 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_117 = x_109;
} else {
 lean::inc(x_115);
 lean::dec(x_109);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_6, 0);
lean::inc(x_118);
lean::dec(x_6);
x_121 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_115, x_118);
if (lean::is_scalar(x_117)) {
 x_122 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_122 = x_117;
}
lean::cnstr_set(x_122, 0, x_121);
return x_122;
}
}
}
}
}
case 2:
{
obj* x_125; 
lean::dec(x_4);
lean::dec(x_0);
x_125 = lean::cnstr_get(x_6, 2);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_128; obj* x_130; obj* x_131; 
lean::dec(x_1);
x_128 = lean::cnstr_get(x_6, 0);
lean::inc(x_128);
x_130 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_128);
x_131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
return x_131;
}
else
{
obj* x_132; 
x_132 = lean::cnstr_get(x_125, 0);
lean::inc(x_132);
lean::dec(x_125);
if (lean::obj_tag(x_132) == 0)
{
obj* x_136; obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_1);
x_136 = lean::cnstr_get(x_132, 0);
lean::inc(x_136);
lean::dec(x_132);
x_139 = lean::cnstr_get(x_6, 0);
lean::inc(x_139);
x_141 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_136, x_139);
x_142 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_142, 0, x_141);
return x_142;
}
else
{
obj* x_143; 
x_143 = lean::cnstr_get(x_6, 1);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_146; obj* x_149; obj* x_152; obj* x_153; 
lean::dec(x_1);
x_146 = lean::cnstr_get(x_132, 0);
lean::inc(x_146);
lean::dec(x_132);
x_149 = lean::cnstr_get(x_6, 0);
lean::inc(x_149);
lean::dec(x_6);
x_152 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_146, x_149);
x_153 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_153, 0, x_152);
return x_153;
}
else
{
obj* x_155; obj* x_156; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_143);
x_155 = l_lean_parser_term_binder__default_has__view;
x_156 = lean::cnstr_get(x_155, 1);
lean::inc(x_156);
lean::dec(x_155);
x_159 = lean::apply_1(x_156, x_132);
x_160 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_161 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_159, x_160, x_1);
if (lean::obj_tag(x_161) == 0)
{
obj* x_163; obj* x_165; obj* x_166; 
lean::dec(x_6);
x_163 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 x_165 = x_161;
} else {
 lean::inc(x_163);
 lean::dec(x_161);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
return x_166;
}
else
{
obj* x_167; obj* x_169; obj* x_170; obj* x_173; obj* x_174; 
x_167 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 x_169 = x_161;
} else {
 lean::inc(x_167);
 lean::dec(x_161);
 x_169 = lean::box(0);
}
x_170 = lean::cnstr_get(x_6, 0);
lean::inc(x_170);
lean::dec(x_6);
x_173 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_167, x_170);
if (lean::is_scalar(x_169)) {
 x_174 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_174 = x_169;
}
lean::cnstr_set(x_174, 0, x_173);
return x_174;
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
obj* x_178; obj* x_181; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_178 = lean::cnstr_get(x_6, 0);
lean::inc(x_178);
lean::dec(x_6);
x_181 = lean::cnstr_get(x_178, 0);
lean::inc(x_181);
x_183 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_183, 0, x_181);
x_184 = lean::box(0);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_183);
lean::cnstr_set(x_185, 1, x_184);
x_186 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_178, x_185);
x_187 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_187, 0, x_186);
return x_187;
}
else
{
obj* x_188; obj* x_191; obj* x_192; obj* x_193; 
x_188 = lean::cnstr_get(x_6, 0);
lean::inc(x_188);
lean::dec(x_6);
x_191 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_192 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_188, x_191);
x_193 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_193, 0, x_192);
return x_193;
}
}
default:
{
obj* x_196; obj* x_197; obj* x_200; obj* x_201; obj* x_203; 
lean::dec(x_6);
lean::dec(x_0);
x_196 = l_lean_parser_term_anonymous__constructor_has__view;
x_197 = lean::cnstr_get(x_196, 1);
lean::inc(x_197);
lean::dec(x_196);
x_200 = lean::apply_1(x_197, x_4);
x_201 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_203 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_200, x_201, x_1);
if (lean::obj_tag(x_203) == 0)
{
obj* x_205; obj* x_207; obj* x_208; 
lean::dec(x_1);
x_205 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_207 = x_203;
} else {
 lean::inc(x_205);
 lean::dec(x_203);
 x_207 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_205);
return x_208;
}
else
{
obj* x_209; obj* x_211; obj* x_212; obj* x_214; 
x_209 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 lean::cnstr_set(x_203, 0, lean::box(0));
 x_211 = x_203;
} else {
 lean::inc(x_209);
 lean::dec(x_203);
 x_211 = lean::box(0);
}
x_212 = lean::cnstr_get(x_209, 1);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_212, 2);
lean::inc(x_214);
if (lean::obj_tag(x_214) == 0)
{
obj* x_217; obj* x_220; uint8 x_222; obj* x_223; obj* x_224; 
lean::dec(x_1);
x_217 = lean::cnstr_get(x_209, 0);
lean::inc(x_217);
lean::dec(x_209);
x_220 = lean::cnstr_get(x_212, 0);
lean::inc(x_220);
x_222 = lean::unbox(x_217);
x_223 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_222, x_212, x_220);
if (lean::is_scalar(x_211)) {
 x_224 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_224 = x_211;
}
lean::cnstr_set(x_224, 0, x_223);
return x_224;
}
else
{
obj* x_225; 
x_225 = lean::cnstr_get(x_214, 0);
lean::inc(x_225);
lean::dec(x_214);
if (lean::obj_tag(x_225) == 0)
{
obj* x_229; obj* x_232; obj* x_235; uint8 x_237; obj* x_238; obj* x_239; 
lean::dec(x_1);
x_229 = lean::cnstr_get(x_209, 0);
lean::inc(x_229);
lean::dec(x_209);
x_232 = lean::cnstr_get(x_225, 0);
lean::inc(x_232);
lean::dec(x_225);
x_235 = lean::cnstr_get(x_212, 0);
lean::inc(x_235);
x_237 = lean::unbox(x_229);
x_238 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_237, x_212, x_232, x_235);
if (lean::is_scalar(x_211)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_211;
}
lean::cnstr_set(x_239, 0, x_238);
return x_239;
}
else
{
obj* x_240; 
x_240 = lean::cnstr_get(x_212, 1);
lean::inc(x_240);
if (lean::obj_tag(x_240) == 0)
{
obj* x_243; obj* x_246; obj* x_249; uint8 x_252; obj* x_253; obj* x_254; 
lean::dec(x_1);
x_243 = lean::cnstr_get(x_209, 0);
lean::inc(x_243);
lean::dec(x_209);
x_246 = lean::cnstr_get(x_225, 0);
lean::inc(x_246);
lean::dec(x_225);
x_249 = lean::cnstr_get(x_212, 0);
lean::inc(x_249);
lean::dec(x_212);
x_252 = lean::unbox(x_243);
x_253 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_252, x_246, x_249);
if (lean::is_scalar(x_211)) {
 x_254 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_254 = x_211;
}
lean::cnstr_set(x_254, 0, x_253);
return x_254;
}
else
{
obj* x_257; obj* x_260; obj* x_261; obj* x_264; obj* x_265; obj* x_266; 
lean::dec(x_211);
lean::dec(x_240);
x_257 = lean::cnstr_get(x_209, 0);
lean::inc(x_257);
lean::dec(x_209);
x_260 = l_lean_parser_term_binder__default_has__view;
x_261 = lean::cnstr_get(x_260, 1);
lean::inc(x_261);
lean::dec(x_260);
x_264 = lean::apply_1(x_261, x_225);
x_265 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_266 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_264, x_265, x_1);
if (lean::obj_tag(x_266) == 0)
{
obj* x_269; obj* x_271; obj* x_272; 
lean::dec(x_257);
lean::dec(x_212);
x_269 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_271 = x_266;
} else {
 lean::inc(x_269);
 lean::dec(x_266);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_269);
return x_272;
}
else
{
obj* x_273; obj* x_275; obj* x_276; uint8 x_279; obj* x_280; obj* x_281; 
x_273 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_275 = x_266;
} else {
 lean::inc(x_273);
 lean::dec(x_266);
 x_275 = lean::box(0);
}
x_276 = lean::cnstr_get(x_212, 0);
lean::inc(x_276);
lean::dec(x_212);
x_279 = lean::unbox(x_257);
x_280 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_279, x_273, x_276);
if (lean::is_scalar(x_275)) {
 x_281 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_281 = x_275;
}
lean::cnstr_set(x_281, 0, x_280);
return x_281;
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
obj* x_282; obj* x_285; 
x_282 = lean::cnstr_get(x_0, 0);
lean::inc(x_282);
lean::dec(x_0);
x_285 = lean::cnstr_get(x_282, 1);
lean::inc(x_285);
lean::dec(x_282);
if (lean::obj_tag(x_285) == 0)
{
obj* x_289; 
lean::dec(x_285);
x_289 = l_lean_expander_expand__bracketed__binder___main___closed__3;
x_2 = x_289;
goto lbl_3;
}
else
{
obj* x_290; uint8 x_293; obj* x_294; obj* x_295; 
x_290 = lean::cnstr_get(x_285, 0);
lean::inc(x_290);
lean::dec(x_285);
x_293 = 0;
x_294 = lean::box(x_293);
x_295 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_295, 0, x_294);
lean::cnstr_set(x_295, 1, x_290);
x_2 = x_295;
goto lbl_3;
}
}
case 1:
{
obj* x_296; obj* x_299; uint8 x_302; obj* x_303; obj* x_304; 
x_296 = lean::cnstr_get(x_0, 0);
lean::inc(x_296);
lean::dec(x_0);
x_299 = lean::cnstr_get(x_296, 1);
lean::inc(x_299);
lean::dec(x_296);
x_302 = 1;
x_303 = lean::box(x_302);
x_304 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_299);
x_2 = x_304;
goto lbl_3;
}
case 2:
{
obj* x_305; obj* x_308; uint8 x_311; obj* x_312; obj* x_313; 
x_305 = lean::cnstr_get(x_0, 0);
lean::inc(x_305);
lean::dec(x_0);
x_308 = lean::cnstr_get(x_305, 1);
lean::inc(x_308);
lean::dec(x_305);
x_311 = 2;
x_312 = lean::box(x_311);
x_313 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_313, 0, x_312);
lean::cnstr_set(x_313, 1, x_308);
x_2 = x_313;
goto lbl_3;
}
case 3:
{
obj* x_314; obj* x_317; 
x_314 = lean::cnstr_get(x_0, 0);
lean::inc(x_314);
lean::dec(x_0);
x_317 = lean::cnstr_get(x_314, 1);
lean::inc(x_317);
lean::dec(x_314);
if (lean::obj_tag(x_317) == 0)
{
obj* x_320; obj* x_323; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_332; obj* x_333; obj* x_334; obj* x_335; uint8 x_336; obj* x_337; obj* x_338; 
x_320 = lean::cnstr_get(x_317, 0);
lean::inc(x_320);
lean::dec(x_317);
x_323 = lean::cnstr_get(x_320, 0);
lean::inc(x_323);
x_325 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_325, 0, x_323);
x_326 = lean::box(0);
x_327 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_327, 0, x_325);
lean::cnstr_set(x_327, 1, x_326);
x_328 = lean::box(0);
x_329 = lean::cnstr_get(x_320, 2);
lean::inc(x_329);
lean::dec(x_320);
x_332 = l_lean_expander_mk__simple__binder___closed__1;
x_333 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_329);
x_334 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_334, 0, x_333);
x_335 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_335, 0, x_327);
lean::cnstr_set(x_335, 1, x_334);
lean::cnstr_set(x_335, 2, x_328);
x_336 = 3;
x_337 = lean::box(x_336);
x_338 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_338, 0, x_337);
lean::cnstr_set(x_338, 1, x_335);
x_2 = x_338;
goto lbl_3;
}
else
{
obj* x_339; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; uint8 x_348; obj* x_349; obj* x_350; 
x_339 = lean::cnstr_get(x_317, 0);
lean::inc(x_339);
lean::dec(x_317);
x_342 = lean::box(0);
x_343 = l_lean_expander_mk__simple__binder___closed__1;
x_344 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_344, 0, x_343);
lean::cnstr_set(x_344, 1, x_339);
x_345 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_345, 0, x_344);
x_346 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_347 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_347, 0, x_346);
lean::cnstr_set(x_347, 1, x_345);
lean::cnstr_set(x_347, 2, x_342);
x_348 = 3;
x_349 = lean::box(x_348);
x_350 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_350, 0, x_349);
lean::cnstr_set(x_350, 1, x_347);
x_2 = x_350;
goto lbl_3;
}
}
default:
{
obj* x_351; obj* x_354; obj* x_355; obj* x_358; obj* x_359; obj* x_361; 
x_351 = lean::cnstr_get(x_0, 0);
lean::inc(x_351);
lean::dec(x_0);
x_354 = l_lean_parser_term_anonymous__constructor_has__view;
x_355 = lean::cnstr_get(x_354, 1);
lean::inc(x_355);
lean::dec(x_354);
x_358 = lean::apply_1(x_355, x_351);
x_359 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_361 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_358, x_359, x_1);
if (lean::obj_tag(x_361) == 0)
{
obj* x_363; obj* x_365; obj* x_366; 
lean::dec(x_1);
x_363 = lean::cnstr_get(x_361, 0);
if (lean::is_exclusive(x_361)) {
 x_365 = x_361;
} else {
 lean::inc(x_363);
 lean::dec(x_361);
 x_365 = lean::box(0);
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_363);
return x_366;
}
else
{
obj* x_367; 
x_367 = lean::cnstr_get(x_361, 0);
lean::inc(x_367);
lean::dec(x_361);
x_2 = x_367;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_370; obj* x_372; 
x_370 = lean::cnstr_get(x_2, 1);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_370, 2);
lean::inc(x_372);
if (lean::obj_tag(x_372) == 0)
{
obj* x_375; obj* x_378; uint8 x_380; obj* x_381; obj* x_382; 
lean::dec(x_1);
x_375 = lean::cnstr_get(x_2, 0);
lean::inc(x_375);
lean::dec(x_2);
x_378 = lean::cnstr_get(x_370, 0);
lean::inc(x_378);
x_380 = lean::unbox(x_375);
x_381 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_380, x_370, x_378);
x_382 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_382, 0, x_381);
return x_382;
}
else
{
obj* x_383; 
x_383 = lean::cnstr_get(x_372, 0);
lean::inc(x_383);
lean::dec(x_372);
if (lean::obj_tag(x_383) == 0)
{
obj* x_387; obj* x_390; obj* x_393; uint8 x_395; obj* x_396; obj* x_397; 
lean::dec(x_1);
x_387 = lean::cnstr_get(x_2, 0);
lean::inc(x_387);
lean::dec(x_2);
x_390 = lean::cnstr_get(x_383, 0);
lean::inc(x_390);
lean::dec(x_383);
x_393 = lean::cnstr_get(x_370, 0);
lean::inc(x_393);
x_395 = lean::unbox(x_387);
x_396 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_395, x_370, x_390, x_393);
x_397 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_397, 0, x_396);
return x_397;
}
else
{
obj* x_398; 
x_398 = lean::cnstr_get(x_370, 1);
lean::inc(x_398);
if (lean::obj_tag(x_398) == 0)
{
obj* x_401; obj* x_404; obj* x_407; uint8 x_410; obj* x_411; obj* x_412; 
lean::dec(x_1);
x_401 = lean::cnstr_get(x_2, 0);
lean::inc(x_401);
lean::dec(x_2);
x_404 = lean::cnstr_get(x_383, 0);
lean::inc(x_404);
lean::dec(x_383);
x_407 = lean::cnstr_get(x_370, 0);
lean::inc(x_407);
lean::dec(x_370);
x_410 = lean::unbox(x_401);
x_411 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_410, x_404, x_407);
x_412 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_412, 0, x_411);
return x_412;
}
else
{
obj* x_414; obj* x_417; obj* x_418; obj* x_421; obj* x_422; obj* x_423; 
lean::dec(x_398);
x_414 = lean::cnstr_get(x_2, 0);
lean::inc(x_414);
lean::dec(x_2);
x_417 = l_lean_parser_term_binder__default_has__view;
x_418 = lean::cnstr_get(x_417, 1);
lean::inc(x_418);
lean::dec(x_417);
x_421 = lean::apply_1(x_418, x_383);
x_422 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_423 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_421, x_422, x_1);
if (lean::obj_tag(x_423) == 0)
{
obj* x_426; obj* x_428; obj* x_429; 
lean::dec(x_414);
lean::dec(x_370);
x_426 = lean::cnstr_get(x_423, 0);
if (lean::is_exclusive(x_423)) {
 x_428 = x_423;
} else {
 lean::inc(x_426);
 lean::dec(x_423);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_426);
return x_429;
}
else
{
obj* x_430; obj* x_432; obj* x_433; uint8 x_436; obj* x_437; obj* x_438; 
x_430 = lean::cnstr_get(x_423, 0);
if (lean::is_exclusive(x_423)) {
 x_432 = x_423;
} else {
 lean::inc(x_430);
 lean::dec(x_423);
 x_432 = lean::box(0);
}
x_433 = lean::cnstr_get(x_370, 0);
lean::inc(x_433);
lean::dec(x_370);
x_436 = lean::unbox(x_414);
x_437 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_436, x_430, x_433);
if (lean::is_scalar(x_432)) {
 x_438 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_438 = x_432;
}
lean::cnstr_set(x_438, 0, x_437);
return x_438;
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
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_4, x_1, x_2, x_3);
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
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_4, x_1, x_2, x_3);
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
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_1, x_6);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_12 = 0;
x_13 = l_lean_expander_get__opt__type___main___closed__1;
x_14 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
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
return x_1;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_0);
x_14 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_1, x_2, x_8);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_16 = 0;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_11);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_2(x_0, x_18, x_14);
return x_19;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_1, x_6);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_12 = 0;
x_13 = l_lean_expander_get__opt__type___main___closed__1;
x_14 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
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
return x_1;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_0);
x_14 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_1, x_2, x_8);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_16 = 0;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_11);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_2(x_0, x_18, x_14);
return x_19;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_1, x_6);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_4);
x_12 = lean::apply_2(x_0, x_11, x_10);
return x_12;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_lean_parser_ident__univs_has__view;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_3);
x_15 = lean::apply_1(x_11, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string(".");
lean::inc(x_2);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_2);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_lean_parser_term_hole_has__view;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::mk_string("_");
x_15 = l_string_trim(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::apply_1(x_11, x_17);
x_19 = 0;
x_20 = l_lean_expander_mk__simple__binder(x_9, x_19, x_18);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
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
obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
x_71 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_73 = x_64;
} else {
 lean::inc(x_71);
 lean::dec(x_64);
 x_73 = lean::box(0);
}
x_74 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_23, x_71);
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
obj* x_78; obj* x_80; obj* x_81; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_11);
lean::dec(x_3);
x_78 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_80 = x_14;
} else {
 lean::inc(x_78);
 lean::dec(x_14);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_7, 0);
lean::inc(x_81);
lean::dec(x_7);
x_84 = l_lean_expander_binder__ident__to__ident___main(x_81);
x_85 = 0;
x_86 = l_lean_expander_get__opt__type___main___closed__1;
x_87 = l_lean_expander_mk__simple__binder(x_84, x_85, x_86);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_89 = lean::apply_2(x_0, x_88, x_78);
if (lean::is_scalar(x_80)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_80;
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
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_0);
x_10 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_1, x_6);
x_11 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_12 = 0;
x_13 = l_lean_expander_get__opt__type___main___closed__1;
x_14 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_0, x_15, x_10);
return x_16;
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
return x_1;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_0);
x_14 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_1, x_2, x_8);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_16 = 0;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_11);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_2(x_0, x_18, x_14);
return x_19;
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
obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_2, x_19, x_10);
if (lean::is_scalar(x_18)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_18;
}
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_27; 
lean::dec(x_16);
lean::dec(x_18);
x_27 = lean::box(0);
x_13 = x_27;
goto lbl_14;
}
}
lbl_14:
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_13);
x_29 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_2, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
else
{
obj* x_32; 
x_32 = lean::cnstr_get(x_7, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_38; 
lean::dec(x_3);
x_35 = lean::cnstr_get(x_4, 0);
lean::inc(x_35);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_41; 
lean::dec(x_32);
x_41 = lean::box(0);
x_38 = x_41;
goto lbl_39;
}
else
{
obj* x_42; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_42 = x_7;
} else {
 lean::dec(x_7);
 x_42 = lean::box(0);
}
if (lean::obj_tag(x_32) == 0)
{
obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_32, 0);
lean::inc(x_43);
lean::dec(x_32);
x_46 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_2, x_43, x_35);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
else
{
obj* x_51; 
lean::dec(x_42);
lean::dec(x_32);
x_51 = lean::box(0);
x_38 = x_51;
goto lbl_39;
}
}
lbl_39:
{
obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_38);
x_53 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_2, x_35);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
else
{
obj* x_56; obj* x_60; 
x_56 = lean::cnstr_get(x_32, 0);
lean::inc(x_56);
lean::inc(x_56);
lean::inc(x_0);
x_60 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_2, x_56, x_3);
if (lean::obj_tag(x_60) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_56);
lean::dec(x_32);
x_66 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_68 = x_60;
} else {
 lean::inc(x_66);
 lean::dec(x_60);
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
obj* x_70; obj* x_72; obj* x_73; obj* x_76; 
x_70 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_set(x_60, 0, lean::box(0));
 x_72 = x_60;
} else {
 lean::inc(x_70);
 lean::dec(x_60);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_4, 0);
lean::inc(x_73);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_80; 
lean::dec(x_56);
lean::dec(x_32);
x_80 = lean::box(0);
x_76 = x_80;
goto lbl_77;
}
else
{
obj* x_81; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_81 = x_7;
} else {
 lean::dec(x_7);
 x_81 = lean::box(0);
}
if (lean::obj_tag(x_32) == 0)
{
obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_72);
lean::dec(x_32);
x_84 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_70, x_56, x_73);
if (lean::is_scalar(x_81)) {
 x_85 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_85 = x_81;
}
lean::cnstr_set(x_85, 0, x_84);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
else
{
obj* x_90; 
lean::dec(x_56);
lean::dec(x_32);
lean::dec(x_81);
x_90 = lean::box(0);
x_76 = x_90;
goto lbl_77;
}
}
lbl_77:
{
obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_76);
x_92 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_70, x_73);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
if (lean::is_scalar(x_72)) {
 x_94 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_94 = x_72;
}
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
else
{
obj* x_99; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_99 = l_lean_expander_no__expansion___closed__1;
return x_99;
}
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("a");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_3 = l_lean_parser_term_arrow_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = l_lean_parser_term_pi_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_15 = l_lean_expander_arrow_transform___closed__1;
x_16 = l_lean_expander_mk__simple__binder___closed__1;
x_17 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set(x_18, 2, x_16);
lean::cnstr_set(x_18, 3, x_12);
lean::cnstr_set(x_18, 4, x_17);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::cnstr_get(x_7, 2);
lean::inc(x_21);
lean::dec(x_7);
x_24 = l_lean_expander_arrow_transform___closed__2;
x_25 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_25);
lean::cnstr_set(x_26, 3, x_21);
x_27 = lean::apply_1(x_9, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
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
obj* x_3; 
lean::dec(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
return x_5;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_10 = x_0;
} else {
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
lean::inc(x_3);
x_12 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_3, lean::box(0));
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_13 = x_3;
} else {
 lean::dec(x_3);
 x_13 = lean::box(0);
}
x_14 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
x_18 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_17, x_16);
return x_18;
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_3 = l_lean_parser_term_paren_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; 
x_11 = l_lean_expander_paren_transform___closed__1;
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_14 = x_8;
} else {
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
lean::dec(x_12);
if (lean::is_scalar(x_14)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_14;
}
lean::cnstr_set(x_20, 0, x_17);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_23; obj* x_25; 
lean::dec(x_14);
x_23 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_25 = x_15;
} else {
 lean::inc(x_23);
 lean::dec(x_15);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_25);
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
lean::dec(x_12);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_33 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_27, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_35 = lean::cnstr_get(x_12, 0);
lean::inc(x_35);
lean::dec(x_12);
x_38 = lean::cnstr_get(x_23, 0);
lean::inc(x_38);
lean::dec(x_23);
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
if (lean::is_scalar(x_25)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_25;
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
obj* _init_l_lean_expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_string("this");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
obj* l_lean_expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_3 = l_lean_parser_term_assume_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = l_lean_parser_term_lambda_has__view;
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_14; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_7, 3);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_24 = l_lean_expander_assume_transform___closed__1;
x_25 = l_lean_expander_mk__simple__binder___closed__1;
x_26 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
x_27 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_27, 3, x_20);
lean::cnstr_set(x_27, 4, x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_31 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_32 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_31);
lean::cnstr_set(x_32, 3, x_14);
x_33 = lean::apply_1(x_11, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_36 = lean::cnstr_get(x_10, 1);
lean::inc(x_36);
lean::dec(x_10);
x_39 = lean::cnstr_get(x_7, 3);
lean::inc(x_39);
lean::dec(x_7);
x_42 = lean::cnstr_get(x_8, 0);
lean::inc(x_42);
lean::dec(x_8);
x_45 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_46 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_47 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_42);
lean::cnstr_set(x_47, 2, x_46);
lean::cnstr_set(x_47, 3, x_39);
x_48 = lean::apply_1(x_36, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_3 = l_lean_parser_term_if_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_10 = lean::cnstr_get(x_7, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 6);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_expander_if_transform___closed__1;
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_21, x_20);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_25 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_27 = x_8;
} else {
 lean::inc(x_25);
 lean::dec(x_8);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_7, 2);
lean::inc(x_28);
x_30 = l_lean_parser_term_lambda_has__view;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::cnstr_get(x_25, 0);
lean::inc(x_34);
lean::dec(x_25);
x_37 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_38 = l_lean_expander_mk__simple__binder___closed__1;
x_39 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_28);
lean::inc(x_34);
x_42 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_38);
lean::cnstr_set(x_42, 3, x_28);
lean::cnstr_set(x_42, 4, x_39);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean::cnstr_get(x_7, 4);
lean::inc(x_45);
x_47 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_48 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_44);
lean::cnstr_set(x_49, 2, x_48);
lean::cnstr_set(x_49, 3, x_45);
lean::inc(x_31);
x_51 = lean::apply_1(x_31, x_49);
x_52 = lean::box(0);
lean::inc(x_28);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_28);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_lean_expander_if_transform___closed__2;
x_56 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_55, x_54);
x_57 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_34);
lean::cnstr_set(x_57, 2, x_38);
lean::cnstr_set(x_57, 3, x_56);
lean::cnstr_set(x_57, 4, x_39);
x_58 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::cnstr_get(x_7, 6);
lean::inc(x_60);
lean::dec(x_7);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_47);
lean::cnstr_set(x_63, 1, x_59);
lean::cnstr_set(x_63, 2, x_48);
lean::cnstr_set(x_63, 3, x_60);
x_64 = lean::apply_1(x_31, x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_52);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_51);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_28);
lean::cnstr_set(x_67, 1, x_66);
x_68 = l_lean_expander_if_transform___closed__3;
x_69 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_68, x_67);
if (lean::is_scalar(x_27)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_27;
}
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_let_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_11 = x_7;
} else {
 lean::inc(x_9);
 lean::dec(x_7);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_16 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
} else {
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::dec(x_3);
x_22 = lean::cnstr_get(x_6, 0);
lean::inc(x_22);
x_24 = l_lean_expander_let_transform___closed__1;
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_16);
lean::cnstr_set(x_25, 1, x_12);
lean::cnstr_set(x_25, 2, x_24);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::cnstr_get(x_6, 2);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_6, 3);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_6, 4);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_6, 5);
lean::inc(x_33);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_26);
lean::cnstr_set(x_36, 2, x_27);
lean::cnstr_set(x_36, 3, x_29);
lean::cnstr_set(x_36, 4, x_31);
lean::cnstr_set(x_36, 5, x_33);
x_37 = lean::apply_1(x_19, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
else
{
obj* x_44; 
lean::dec(x_14);
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_6);
x_44 = l_lean_expander_no__expansion___closed__1;
return x_44;
}
}
else
{
obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_45 = lean::cnstr_get(x_9, 0);
x_47 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 1);
 x_49 = x_9;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_9);
 x_49 = lean::box(0);
}
x_50 = lean::box(0);
x_51 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_12);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::cnstr_get(x_3, 1);
lean::inc(x_56);
lean::dec(x_3);
x_59 = lean::cnstr_get(x_6, 0);
lean::inc(x_59);
x_61 = l_lean_parser_term_pi_has__view;
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
lean::dec(x_61);
x_65 = l_lean_expander_get__opt__type___main(x_47);
x_66 = l_lean_expander_arrow_transform___closed__2;
x_67 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_55);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_55);
lean::cnstr_set(x_69, 2, x_67);
lean::cnstr_set(x_69, 3, x_65);
x_70 = lean::apply_1(x_62, x_69);
x_71 = l_lean_expander_mk__simple__binder___closed__1;
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
if (lean::is_scalar(x_49)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_49;
}
lean::cnstr_set(x_74, 0, x_45);
lean::cnstr_set(x_74, 1, x_50);
lean::cnstr_set(x_74, 2, x_73);
if (lean::is_scalar(x_11)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_11;
}
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::cnstr_get(x_6, 2);
lean::inc(x_76);
x_78 = l_lean_parser_term_lambda_has__view;
x_79 = lean::cnstr_get(x_78, 1);
lean::inc(x_79);
lean::dec(x_78);
x_82 = lean::cnstr_get(x_6, 3);
lean::inc(x_82);
x_84 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_55);
lean::cnstr_set(x_85, 2, x_67);
lean::cnstr_set(x_85, 3, x_82);
x_86 = lean::apply_1(x_79, x_85);
x_87 = lean::cnstr_get(x_6, 4);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_6, 5);
lean::inc(x_89);
lean::dec(x_6);
x_92 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_92, 0, x_59);
lean::cnstr_set(x_92, 1, x_75);
lean::cnstr_set(x_92, 2, x_76);
lean::cnstr_set(x_92, 3, x_86);
lean::cnstr_set(x_92, 4, x_87);
lean::cnstr_set(x_92, 5, x_89);
x_93 = lean::apply_1(x_56, x_92);
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
x_96 = lean::cnstr_get(x_7, 0);
lean::inc(x_96);
lean::dec(x_7);
x_99 = l_lean_parser_term_match_has__view;
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
lean::dec(x_99);
x_103 = lean::box(0);
x_104 = lean::cnstr_get(x_6, 3);
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
x_111 = lean::cnstr_get(x_6, 5);
lean::inc(x_111);
lean::dec(x_6);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_3 = l_lean_parser_command_constant_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::box(0);
x_18 = l_list_map___main___at_lean_expander_constant_transform___spec__1(x_14);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::dec(x_3);
x_26 = lean::cnstr_get(x_6, 0);
x_28 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 2);
 x_30 = x_6;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_6);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_term_pi_has__view;
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
lean::dec(x_31);
x_35 = lean::cnstr_get(x_11, 1);
lean::inc(x_35);
lean::dec(x_11);
x_38 = l_lean_expander_arrow_transform___closed__2;
x_39 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_40 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_22);
lean::cnstr_set(x_40, 2, x_39);
lean::cnstr_set(x_40, 3, x_35);
x_41 = lean::apply_1(x_32, x_40);
x_42 = l_lean_expander_mk__simple__binder___closed__1;
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_lean_expander_constant_transform___closed__1;
if (lean::is_scalar(x_13)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_13;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
if (lean::is_scalar(x_30)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_30;
}
lean::cnstr_set(x_46, 0, x_26);
lean::cnstr_set(x_46, 1, x_28);
lean::cnstr_set(x_46, 2, x_45);
x_47 = lean::apply_1(x_23, x_46);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_53; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_9);
x_53 = l_lean_expander_no__expansion___closed__1;
return x_53;
}
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("class");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string(".");
lean::inc(x_4);
x_7 = l_lean_name_to__string__with__sep___main(x_5, x_4);
x_8 = l_lean_parser_substring_of__string(x_7);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_1);
lean::cnstr_set(x_9, 4, x_1);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
return x_11;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_command_declaration_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
switch (lean::obj_tag(x_7)) {
case 4:
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_11 = x_7;
} else {
 lean::inc(x_9);
 lean::dec(x_7);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; 
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_11);
x_17 = l_lean_expander_no__expansion___closed__1;
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_18 = x_12;
} else {
 lean::dec(x_12);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_9, 1);
x_21 = lean::cnstr_get(x_9, 2);
x_23 = lean::cnstr_get(x_9, 3);
x_25 = lean::cnstr_get(x_9, 4);
x_27 = lean::cnstr_get(x_9, 5);
x_29 = lean::cnstr_get(x_9, 6);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_31 = x_9;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_9);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_6, 0);
lean::inc(x_32);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
x_37 = lean::box(0);
x_38 = l_lean_expander_declaration_transform___closed__1;
x_39 = l_option_get__or__else___main___rarg(x_35, x_38);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_32, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_39, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_39, 1);
lean::inc(x_47);
x_49 = l_lean_expander_declaration_transform___closed__2;
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
x_51 = lean::cnstr_get(x_39, 2);
lean::inc(x_51);
lean::dec(x_39);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_45);
lean::cnstr_set(x_54, 1, x_50);
lean::cnstr_set(x_54, 2, x_51);
if (lean::is_scalar(x_18)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_18;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::cnstr_get(x_32, 2);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_32, 3);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_32, 4);
lean::inc(x_60);
lean::dec(x_32);
x_63 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_63, 0, x_43);
lean::cnstr_set(x_63, 1, x_55);
lean::cnstr_set(x_63, 2, x_56);
lean::cnstr_set(x_63, 3, x_58);
lean::cnstr_set(x_63, 4, x_60);
if (lean::is_scalar(x_31)) {
 x_64 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_64 = x_31;
}
lean::cnstr_set(x_64, 0, x_37);
lean::cnstr_set(x_64, 1, x_19);
lean::cnstr_set(x_64, 2, x_21);
lean::cnstr_set(x_64, 3, x_23);
lean::cnstr_set(x_64, 4, x_25);
lean::cnstr_set(x_64, 5, x_27);
lean::cnstr_set(x_64, 6, x_29);
if (lean::is_scalar(x_11)) {
 x_65 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_65 = x_11;
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
x_70 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_72 = x_7;
} else {
 lean::inc(x_70);
 lean::dec(x_7);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_79; 
lean::dec(x_6);
lean::dec(x_73);
lean::dec(x_72);
lean::dec(x_70);
x_79 = l_lean_expander_no__expansion___closed__1;
return x_79;
}
else
{
obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_117; obj* x_118; obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
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
x_96 = lean::cnstr_get(x_6, 0);
lean::inc(x_96);
lean::dec(x_6);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
x_101 = l_lean_expander_declaration_transform___closed__1;
x_102 = l_option_get__or__else___main___rarg(x_99, x_101);
x_103 = lean::cnstr_get(x_3, 1);
lean::inc(x_103);
lean::dec(x_3);
x_106 = lean::cnstr_get(x_96, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_102, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_102, 1);
lean::inc(x_110);
x_112 = l_lean_expander_declaration_transform___closed__2;
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_110);
x_114 = lean::cnstr_get(x_102, 2);
lean::inc(x_114);
lean::dec(x_102);
x_117 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_117, 0, x_108);
lean::cnstr_set(x_117, 1, x_113);
lean::cnstr_set(x_117, 2, x_114);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
x_119 = lean::cnstr_get(x_96, 2);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_96, 3);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_96, 4);
lean::inc(x_123);
lean::dec(x_96);
x_126 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_126, 0, x_106);
lean::cnstr_set(x_126, 1, x_118);
lean::cnstr_set(x_126, 2, x_119);
lean::cnstr_set(x_126, 3, x_121);
lean::cnstr_set(x_126, 4, x_123);
x_127 = l_lean_expander_declaration_transform___closed__3;
if (lean::is_scalar(x_95)) {
 x_128 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_128 = x_95;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_81);
lean::cnstr_set(x_128, 2, x_83);
lean::cnstr_set(x_128, 3, x_85);
lean::cnstr_set(x_128, 4, x_87);
lean::cnstr_set(x_128, 5, x_89);
lean::cnstr_set(x_128, 6, x_91);
lean::cnstr_set(x_128, 7, x_93);
if (lean::is_scalar(x_72)) {
 x_129 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_129 = x_72;
}
lean::cnstr_set(x_129, 0, x_128);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::apply_1(x_103, x_130);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
x_133 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_133, 0, x_132);
return x_133;
}
}
default:
{
obj* x_136; 
lean::dec(x_7);
lean::dec(x_6);
x_136 = l_lean_expander_no__expansion___closed__1;
return x_136;
}
}
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_3 = l_lean_parser_command_intro__rule_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; 
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_9);
x_17 = l_lean_expander_no__expansion___closed__1;
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_23 = x_11;
} else {
 lean::inc(x_21);
 lean::dec(x_11);
 x_23 = lean::box(0);
}
x_24 = lean::box(0);
x_25 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_18);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::cnstr_get(x_3, 1);
lean::inc(x_30);
lean::dec(x_3);
x_33 = lean::cnstr_get(x_6, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_6, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_6, 2);
lean::inc(x_37);
lean::dec(x_6);
x_40 = l_lean_parser_term_pi_has__view;
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
lean::dec(x_40);
x_44 = lean::cnstr_get(x_21, 1);
lean::inc(x_44);
lean::dec(x_21);
x_47 = l_lean_expander_arrow_transform___closed__2;
x_48 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_29);
lean::cnstr_set(x_49, 2, x_48);
lean::cnstr_set(x_49, 3, x_44);
x_50 = lean::apply_1(x_41, x_49);
x_51 = l_lean_expander_mk__simple__binder___closed__1;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = l_lean_expander_constant_transform___closed__1;
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_53);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_33);
lean::cnstr_set(x_56, 1, x_35);
lean::cnstr_set(x_56, 2, x_37);
lean::cnstr_set(x_56, 3, x_55);
x_57 = lean::apply_1(x_30, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
else
{
obj* x_63; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_9);
x_63 = l_lean_expander_no__expansion___closed__1;
return x_63;
}
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_1);
x_3 = l_lean_parser_command_variable_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = l_lean_parser_command_variables_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::box(0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_15);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = l_lean_expander_variable_transform___closed__1;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = lean::apply_1(x_9, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_26 = lean::cnstr_get(x_12, 0);
lean::inc(x_26);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
x_30 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_31 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_31);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_15);
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = l_lean_expander_variable_transform___closed__1;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
x_38 = lean::apply_1(x_9, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
x_2 = l_option_map___rarg(x_1, x_0);
x_3 = lean::box(3);
x_4 = l_option_get__or__else___main___rarg(x_2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_lean_expander_binding__annotation__update;
x_8 = l_lean_parser_syntax_mk__node(x_7, x_6);
return x_8;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1), 8, 3);
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__tokens___spec__1), 8, 3);
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
obj* x_3; obj* x_4; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_level_leading_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
switch (lean::obj_tag(x_7)) {
case 3:
{
obj* x_8; obj* x_11; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_11);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
default:
{
obj* x_17; 
lean::dec(x_7);
x_17 = l_lean_expander_no__expansion___closed__1;
return x_17;
}
}
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_3 = l_lean_parser_term_subtype_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = l_lean_parser_term_lambda_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 2);
lean::inc(x_14);
x_16 = l_lean_expander_get__opt__type___main(x_14);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_12, x_17, x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::cnstr_get(x_7, 4);
lean::inc(x_20);
lean::dec(x_7);
x_23 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_24 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_20);
x_26 = lean::apply_1(x_9, x_25);
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
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_3 = l_lean_parser_command_universes_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_8);
x_12 = l_lean_parser_no__kind;
x_13 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_expander_sorry_transform___closed__1;
return x_4;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; uint8 x_19; 
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
lean::inc(x_9);
lean::inc(x_1);
x_18 = l_lean_name_quick__lt___main(x_1, x_9);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; uint8 x_23; 
lean::inc(x_1);
lean::inc(x_9);
x_22 = l_lean_name_quick__lt___main(x_9, x_1);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_7);
lean::cnstr_set(x_29, 1, x_9);
lean::cnstr_set(x_29, 2, x_11);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_6);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
lean::cnstr_set(x_32, 2, x_11);
lean::cnstr_set(x_32, 3, x_13);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_6);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; uint8 x_46; 
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
lean::inc(x_36);
lean::inc(x_1);
x_45 = l_lean_name_quick__lt___main(x_1, x_36);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_49; uint8 x_50; 
lean::inc(x_1);
lean::inc(x_36);
x_49 = l_lean_name_quick__lt___main(x_36, x_1);
x_50 = lean::unbox(x_49);
if (x_50 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_38);
lean::dec(x_36);
if (lean::is_scalar(x_42)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_42;
}
lean::cnstr_set(x_53, 0, x_34);
lean::cnstr_set(x_53, 1, x_1);
lean::cnstr_set(x_53, 2, x_2);
lean::cnstr_set(x_53, 3, x_40);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_6);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_56; 
lean::inc(x_40);
x_56 = l_rbnode_is__red___main___rarg(x_40);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_61; obj* x_62; 
lean::dec(x_42);
x_61 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_40, x_1, x_2);
x_62 = l_rbnode_balance2___main___rarg(x_61, x_36, x_38, x_34);
return x_62;
}
}
}
else
{
uint8 x_64; 
lean::inc(x_34);
x_64 = l_rbnode_is__red___main___rarg(x_34);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_66 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_66 = x_42;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_36);
lean::cnstr_set(x_66, 2, x_38);
lean::cnstr_set(x_66, 3, x_40);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_6);
x_67 = x_66;
return x_67;
}
else
{
obj* x_69; obj* x_70; 
lean::dec(x_42);
x_69 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_69, x_36, x_38, x_40);
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
uint8 x_4; 
lean::inc(x_0);
x_4 = l_rbnode_is__red___main___rarg(x_0);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_arrow_transform), 2, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_term_paren;
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_paren_transform), 2, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_term_assume;
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_assume_transform), 2, 0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_term_if;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_if_transform), 2, 0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_term_let;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_let_transform), 2, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_constant;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_constant_transform), 2, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_declaration;
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_declaration_transform), 2, 0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_lean_parser_command_intro__rule;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_intro__rule_transform), 2, 0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_variable;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variable_transform), 2, 0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_parser_command_variables;
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variables_transform), 2, 0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_level_leading;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_level_leading_transform), 2, 0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_lean_parser_term_subtype;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_subtype_transform), 2, 0);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_lean_parser_command_universes;
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_universes_transform), 2, 0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = l_lean_parser_term_sorry;
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_sorry_transform), 2, 0);
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_0, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_lean_parser_syntax_get__pos(x_0);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_option_get__or__else___main___rarg(x_13, x_14);
x_16 = l_lean_file__map_to__position(x_10, x_15);
x_17 = lean::box(0);
x_18 = 2;
x_19 = l_string_join___closed__1;
x_20 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_20, 0, x_8);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg), 4, 0);
return x_2;
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
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_24; 
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
lean::inc(x_21);
x_24 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_19, x_21);
if (lean::obj_tag(x_24) == 0)
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
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
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
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
if (lean::is_scalar(x_36)) {
 x_44 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_44 = x_36;
}
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
}
else
{
obj* x_45; obj* x_49; 
x_45 = lean::cnstr_get(x_24, 0);
lean::inc(x_45);
lean::dec(x_24);
lean::inc(x_3);
x_49 = l_lean_expander_mk__scope(x_2, x_3);
if (lean::obj_tag(x_49) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_45);
lean::dec(x_17);
lean::dec(x_21);
x_55 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_57 = x_49;
} else {
 lean::inc(x_55);
 lean::dec(x_49);
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
obj* x_59; obj* x_62; obj* x_64; obj* x_67; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_59 = lean::cnstr_get(x_49, 0);
lean::inc(x_59);
lean::dec(x_49);
x_62 = lean::cnstr_get(x_59, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
lean::dec(x_59);
x_67 = lean::cnstr_get(x_13, 1);
lean::inc(x_67);
lean::dec(x_13);
lean::inc(x_67);
lean::inc(x_62);
x_72 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_62, x_67);
lean::inc(x_21);
x_74 = l_lean_parser_syntax_mk__node(x_21, x_72);
x_75 = lean::cnstr_get(x_3, 0);
lean::inc(x_75);
x_77 = lean::apply_2(x_45, x_74, x_75);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_3);
lean::dec(x_67);
lean::dec(x_62);
lean::dec(x_64);
lean::dec(x_17);
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
lean::dec(x_62);
x_92 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_17, x_67, x_64, x_3);
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
x_106 = l_lean_parser_syntax_mk__node(x_21, x_101);
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
obj* x_111; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_67);
lean::dec(x_21);
x_111 = lean::cnstr_get(x_88, 0);
lean::inc(x_111);
lean::dec(x_88);
x_114 = lean::box(0);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_62);
lean::cnstr_set(x_115, 1, x_114);
x_116 = l_lean_parser_syntax_flip__scopes___main(x_115, x_111);
x_0 = x_17;
x_1 = x_116;
x_2 = x_64;
goto _start;
}
}
}
}
}
}
else
{
obj* x_119; obj* x_120; 
lean::dec(x_0);
x_119 = l___private_init_lean_expander_2__expand__core___main___closed__1;
x_120 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_1, x_119, x_2, x_3);
return x_120;
}
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
