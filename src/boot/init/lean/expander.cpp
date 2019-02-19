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
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
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
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
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
obj* l_lean_expander_coe__ident__ident__univs(obj*);
obj* l_lean_expander_paren_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
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
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
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
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
x_4 = l_lean_name_to__string__with__sep___main(x_2, x_0);
x_5 = l_lean_parser_substring_of__string(x_4);
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_0);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set(x_6, 4, x_1);
return x_6;
}
}
obj* l_lean_expander_glob__id(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
x_8 = l_lean_name_to__string__with__sep___main(x_6, x_0);
x_9 = l_lean_parser_substring_of__string(x_8);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_5);
x_12 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set(x_12, 1, x_9);
lean::cnstr_set(x_12, 2, x_0);
lean::cnstr_set(x_12, 3, x_11);
lean::cnstr_set(x_12, 4, x_5);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_5);
x_14 = lean::apply_1(x_2, x_13);
return x_14;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
 lean::cnstr_set(x_26, 0, lean::box(0));
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
 lean::cnstr_set(x_42, 0, lean::box(0));
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
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_set(x_14, 1, lean::box(0));
 x_56 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_9, 1);
lean::inc(x_57);
lean::dec(x_9);
if (lean::obj_tag(x_57) == 0)
{
lean::dec(x_13);
lean::dec(x_56);
x_1 = x_11;
x_2 = x_54;
goto _start;
}
else
{
obj* x_63; obj* x_65; 
x_63 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_set(x_57, 0, lean::box(0));
 x_65 = x_57;
} else {
 lean::inc(x_63);
 lean::dec(x_57);
 x_65 = lean::box(0);
}
switch (lean::obj_tag(x_63)) {
case 0:
{
obj* x_69; 
lean::dec(x_63);
lean::dec(x_56);
lean::inc(x_3);
x_69 = l___private_init_lean_expander_1__pop__stx__arg(x_54, x_3);
if (lean::obj_tag(x_69) == 0)
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_65);
x_75 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_set(x_69, 0, lean::box(0));
 x_77 = x_69;
} else {
 lean::inc(x_75);
 lean::dec(x_69);
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
obj* x_79; obj* x_82; obj* x_84; obj* x_87; obj* x_89; obj* x_91; obj* x_94; obj* x_95; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_79 = lean::cnstr_get(x_69, 0);
lean::inc(x_79);
lean::dec(x_69);
x_82 = lean::cnstr_get(x_79, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 1);
lean::inc(x_84);
lean::dec(x_79);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_84, 2);
lean::inc(x_91);
lean::dec(x_84);
x_94 = l_lean_parser_term_binder__ident_has__view;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
lean::dec(x_94);
x_98 = lean::apply_1(x_95, x_82);
x_99 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_100 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_100 = x_13;
}
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
if (lean::is_scalar(x_65)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_65;
}
lean::cnstr_set(x_103, 0, x_102);
x_104 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_104, 0, x_87);
lean::cnstr_set(x_104, 1, x_89);
lean::cnstr_set(x_104, 2, x_91);
lean::cnstr_set(x_104, 3, x_103);
x_1 = x_11;
x_2 = x_104;
goto _start;
}
}
case 1:
{
obj* x_110; 
lean::dec(x_13);
lean::dec(x_63);
lean::dec(x_56);
lean::inc(x_3);
x_110 = l___private_init_lean_expander_1__pop__stx__arg(x_54, x_3);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_65);
x_115 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_set(x_110, 0, lean::box(0));
 x_117 = x_110;
} else {
 lean::inc(x_115);
 lean::dec(x_110);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
return x_118;
}
else
{
obj* x_119; obj* x_122; obj* x_124; obj* x_127; obj* x_129; obj* x_131; obj* x_134; obj* x_135; obj* x_138; obj* x_139; obj* x_140; 
x_119 = lean::cnstr_get(x_110, 0);
lean::inc(x_119);
lean::dec(x_110);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 1);
lean::inc(x_124);
lean::dec(x_119);
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_124, 2);
lean::inc(x_131);
lean::dec(x_124);
x_134 = l_lean_parser_term_binders_has__view;
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
lean::dec(x_134);
x_138 = lean::apply_1(x_135, x_122);
if (lean::is_scalar(x_65)) {
 x_139 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_139 = x_65;
}
lean::cnstr_set(x_139, 0, x_138);
x_140 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_140, 0, x_127);
lean::cnstr_set(x_140, 1, x_129);
lean::cnstr_set(x_140, 2, x_131);
lean::cnstr_set(x_140, 3, x_139);
x_1 = x_11;
x_2 = x_140;
goto _start;
}
}
default:
{
obj* x_143; obj* x_146; obj* x_148; 
lean::dec(x_65);
x_143 = lean::cnstr_get(x_63, 0);
lean::inc(x_143);
lean::dec(x_63);
x_146 = lean::cnstr_get(x_143, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_143, 1);
lean::inc(x_148);
lean::dec(x_143);
if (lean::obj_tag(x_148) == 0)
{
obj* x_152; 
lean::inc(x_3);
x_152 = l___private_init_lean_expander_1__pop__stx__arg(x_54, x_3);
if (lean::obj_tag(x_152) == 0)
{
obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_56);
x_159 = lean::cnstr_get(x_152, 0);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_set(x_152, 0, lean::box(0));
 x_161 = x_152;
} else {
 lean::inc(x_159);
 lean::dec(x_152);
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
obj* x_163; obj* x_166; obj* x_168; obj* x_171; obj* x_173; obj* x_175; obj* x_176; obj* x_178; obj* x_179; obj* x_182; 
x_163 = lean::cnstr_get(x_152, 0);
lean::inc(x_163);
lean::dec(x_152);
x_166 = lean::cnstr_get(x_163, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_163, 1);
lean::inc(x_168);
lean::dec(x_163);
x_171 = lean::cnstr_get(x_168, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_168, 1);
lean::inc(x_173);
if (lean::is_scalar(x_56)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_56;
}
lean::cnstr_set(x_175, 0, x_146);
lean::cnstr_set(x_175, 1, x_166);
x_176 = lean::cnstr_get(x_168, 2);
lean::inc(x_176);
if (lean::is_scalar(x_13)) {
 x_178 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_178 = x_13;
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
x_1 = x_11;
x_2 = x_182;
goto _start;
}
}
else
{
obj* x_184; obj* x_187; 
x_184 = lean::cnstr_get(x_148, 0);
lean::inc(x_184);
lean::dec(x_148);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
lean::dec(x_184);
switch (lean::obj_tag(x_187)) {
case 0:
{
obj* x_192; 
lean::dec(x_187);
lean::inc(x_3);
x_192 = l___private_init_lean_expander_1__pop__stx__arg(x_54, x_3);
if (lean::obj_tag(x_192) == 0)
{
obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_56);
x_199 = lean::cnstr_get(x_192, 0);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_set(x_192, 0, lean::box(0));
 x_201 = x_192;
} else {
 lean::inc(x_199);
 lean::dec(x_192);
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
obj* x_203; obj* x_206; obj* x_208; obj* x_211; obj* x_213; obj* x_215; obj* x_216; obj* x_218; obj* x_219; obj* x_222; 
x_203 = lean::cnstr_get(x_192, 0);
lean::inc(x_203);
lean::dec(x_192);
x_206 = lean::cnstr_get(x_203, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_203, 1);
lean::inc(x_208);
lean::dec(x_203);
x_211 = lean::cnstr_get(x_208, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_208, 1);
lean::inc(x_213);
if (lean::is_scalar(x_56)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_56;
}
lean::cnstr_set(x_215, 0, x_146);
lean::cnstr_set(x_215, 1, x_206);
x_216 = lean::cnstr_get(x_208, 2);
lean::inc(x_216);
if (lean::is_scalar(x_13)) {
 x_218 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_218 = x_13;
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
x_1 = x_11;
x_2 = x_222;
goto _start;
}
}
case 2:
{
obj* x_224; obj* x_228; 
x_224 = lean::cnstr_get(x_187, 0);
lean::inc(x_224);
lean::dec(x_187);
lean::inc(x_3);
x_228 = l___private_init_lean_expander_1__pop__stx__arg(x_54, x_3);
if (lean::obj_tag(x_228) == 0)
{
obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_224);
lean::dec(x_56);
x_236 = lean::cnstr_get(x_228, 0);
if (lean::is_exclusive(x_228)) {
 lean::cnstr_set(x_228, 0, lean::box(0));
 x_238 = x_228;
} else {
 lean::inc(x_236);
 lean::dec(x_228);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
return x_239;
}
else
{
obj* x_240; obj* x_242; obj* x_243; obj* x_245; obj* x_248; obj* x_250; obj* x_252; obj* x_254; 
x_240 = lean::cnstr_get(x_228, 0);
if (lean::is_exclusive(x_228)) {
 lean::cnstr_set(x_228, 0, lean::box(0));
 x_242 = x_228;
} else {
 lean::inc(x_240);
 lean::dec(x_228);
 x_242 = lean::box(0);
}
x_243 = lean::cnstr_get(x_240, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_240, 1);
lean::inc(x_245);
lean::dec(x_240);
x_248 = lean::cnstr_get(x_245, 0);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_245, 1);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_245, 2);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_245, 3);
lean::inc(x_254);
if (lean::obj_tag(x_254) == 0)
{
obj* x_264; obj* x_267; 
lean::dec(x_146);
lean::dec(x_243);
lean::dec(x_13);
lean::dec(x_252);
lean::dec(x_248);
lean::dec(x_224);
lean::dec(x_250);
lean::dec(x_56);
x_264 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_267 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_264, x_245, x_3);
if (lean::obj_tag(x_267) == 0)
{
obj* x_271; obj* x_274; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_271 = lean::cnstr_get(x_267, 0);
lean::inc(x_271);
lean::dec(x_267);
if (lean::is_scalar(x_242)) {
 x_274 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_274 = x_242;
 lean::cnstr_set_tag(x_242, 0);
}
lean::cnstr_set(x_274, 0, x_271);
return x_274;
}
else
{
obj* x_276; obj* x_279; 
lean::dec(x_242);
x_276 = lean::cnstr_get(x_267, 0);
lean::inc(x_276);
lean::dec(x_267);
x_279 = lean::cnstr_get(x_276, 1);
lean::inc(x_279);
lean::dec(x_276);
x_1 = x_11;
x_2 = x_279;
goto _start;
}
}
else
{
obj* x_285; obj* x_287; obj* x_288; obj* x_291; obj* x_292; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_301; obj* x_302; obj* x_303; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
lean::dec(x_242);
lean::dec(x_245);
x_285 = lean::cnstr_get(x_254, 0);
lean::inc(x_285);
x_287 = l_lean_parser_term_lambda_has__view;
x_288 = lean::cnstr_get(x_287, 1);
lean::inc(x_288);
lean::dec(x_287);
x_291 = lean::box(0);
x_292 = lean::cnstr_get(x_224, 3);
lean::inc(x_292);
if (lean::is_scalar(x_13)) {
 x_294 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_294 = x_13;
}
lean::cnstr_set(x_294, 0, x_292);
lean::cnstr_set(x_294, 1, x_291);
x_295 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_294);
x_296 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_296, 0, x_295);
lean::cnstr_set(x_296, 1, x_291);
x_297 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_297, 0, x_296);
x_298 = lean::cnstr_get(x_224, 5);
lean::inc(x_298);
lean::dec(x_224);
x_301 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_302 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_303 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_303, 0, x_301);
lean::cnstr_set(x_303, 1, x_297);
lean::cnstr_set(x_303, 2, x_302);
lean::cnstr_set(x_303, 3, x_298);
lean::inc(x_288);
x_305 = lean::apply_1(x_288, x_303);
x_306 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_306, 0, x_301);
lean::cnstr_set(x_306, 1, x_285);
lean::cnstr_set(x_306, 2, x_302);
lean::cnstr_set(x_306, 3, x_243);
x_307 = lean::apply_1(x_288, x_306);
x_308 = l_lean_parser_term_app_has__view;
x_309 = lean::cnstr_get(x_308, 1);
lean::inc(x_309);
lean::dec(x_308);
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_305);
lean::cnstr_set(x_312, 1, x_307);
x_313 = lean::apply_1(x_309, x_312);
if (lean::is_scalar(x_56)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_56;
}
lean::cnstr_set(x_314, 0, x_146);
lean::cnstr_set(x_314, 1, x_313);
x_315 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_252);
x_316 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_316, 0, x_248);
lean::cnstr_set(x_316, 1, x_250);
lean::cnstr_set(x_316, 2, x_315);
lean::cnstr_set(x_316, 3, x_254);
x_1 = x_11;
x_2 = x_316;
goto _start;
}
}
}
default:
{
obj* x_322; obj* x_325; 
lean::dec(x_146);
lean::dec(x_13);
lean::dec(x_187);
lean::dec(x_56);
x_322 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_325 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_322, x_54, x_3);
if (lean::obj_tag(x_325) == 0)
{
obj* x_329; obj* x_331; obj* x_332; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_329 = lean::cnstr_get(x_325, 0);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_set(x_325, 0, lean::box(0));
 x_331 = x_325;
} else {
 lean::inc(x_329);
 lean::dec(x_325);
 x_331 = lean::box(0);
}
if (lean::is_scalar(x_331)) {
 x_332 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_332 = x_331;
}
lean::cnstr_set(x_332, 0, x_329);
return x_332;
}
else
{
obj* x_333; obj* x_336; 
x_333 = lean::cnstr_get(x_325, 0);
lean::inc(x_333);
lean::dec(x_325);
x_336 = lean::cnstr_get(x_333, 1);
lean::inc(x_336);
lean::dec(x_333);
x_1 = x_11;
x_2 = x_336;
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
obj* x_340; obj* x_342; obj* x_343; 
x_340 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_342 = x_16;
} else {
 lean::inc(x_340);
 lean::dec(x_16);
 x_342 = lean::box(0);
}
x_343 = lean::cnstr_get(x_9, 1);
lean::inc(x_343);
lean::dec(x_9);
if (lean::obj_tag(x_343) == 0)
{
lean::dec(x_342);
x_1 = x_11;
x_2 = x_340;
goto _start;
}
else
{
obj* x_348; obj* x_350; 
x_348 = lean::cnstr_get(x_343, 0);
if (lean::is_exclusive(x_343)) {
 lean::cnstr_set(x_343, 0, lean::box(0));
 x_350 = x_343;
} else {
 lean::inc(x_348);
 lean::dec(x_343);
 x_350 = lean::box(0);
}
switch (lean::obj_tag(x_348)) {
case 0:
{
obj* x_354; 
lean::dec(x_342);
lean::dec(x_348);
lean::inc(x_3);
x_354 = l___private_init_lean_expander_1__pop__stx__arg(x_340, x_3);
if (lean::obj_tag(x_354) == 0)
{
obj* x_359; obj* x_361; obj* x_362; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_350);
x_359 = lean::cnstr_get(x_354, 0);
if (lean::is_exclusive(x_354)) {
 lean::cnstr_set(x_354, 0, lean::box(0));
 x_361 = x_354;
} else {
 lean::inc(x_359);
 lean::dec(x_354);
 x_361 = lean::box(0);
}
if (lean::is_scalar(x_361)) {
 x_362 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_362 = x_361;
}
lean::cnstr_set(x_362, 0, x_359);
return x_362;
}
else
{
obj* x_363; obj* x_366; obj* x_368; obj* x_371; obj* x_373; obj* x_375; obj* x_378; obj* x_379; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; 
x_363 = lean::cnstr_get(x_354, 0);
lean::inc(x_363);
lean::dec(x_354);
x_366 = lean::cnstr_get(x_363, 0);
lean::inc(x_366);
x_368 = lean::cnstr_get(x_363, 1);
lean::inc(x_368);
lean::dec(x_363);
x_371 = lean::cnstr_get(x_368, 0);
lean::inc(x_371);
x_373 = lean::cnstr_get(x_368, 1);
lean::inc(x_373);
x_375 = lean::cnstr_get(x_368, 2);
lean::inc(x_375);
lean::dec(x_368);
x_378 = l_lean_parser_term_binder__ident_has__view;
x_379 = lean::cnstr_get(x_378, 0);
lean::inc(x_379);
lean::dec(x_378);
x_382 = lean::apply_1(x_379, x_366);
x_383 = lean::box(0);
x_384 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_384, 0, x_382);
lean::cnstr_set(x_384, 1, x_383);
x_385 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_385, 0, x_384);
lean::cnstr_set(x_385, 1, x_383);
x_386 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_386, 0, x_385);
if (lean::is_scalar(x_350)) {
 x_387 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_387 = x_350;
}
lean::cnstr_set(x_387, 0, x_386);
x_388 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_388, 0, x_371);
lean::cnstr_set(x_388, 1, x_373);
lean::cnstr_set(x_388, 2, x_375);
lean::cnstr_set(x_388, 3, x_387);
x_1 = x_11;
x_2 = x_388;
goto _start;
}
}
case 1:
{
obj* x_393; 
lean::dec(x_342);
lean::dec(x_348);
lean::inc(x_3);
x_393 = l___private_init_lean_expander_1__pop__stx__arg(x_340, x_3);
if (lean::obj_tag(x_393) == 0)
{
obj* x_398; obj* x_400; obj* x_401; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_350);
x_398 = lean::cnstr_get(x_393, 0);
if (lean::is_exclusive(x_393)) {
 lean::cnstr_set(x_393, 0, lean::box(0));
 x_400 = x_393;
} else {
 lean::inc(x_398);
 lean::dec(x_393);
 x_400 = lean::box(0);
}
if (lean::is_scalar(x_400)) {
 x_401 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_401 = x_400;
}
lean::cnstr_set(x_401, 0, x_398);
return x_401;
}
else
{
obj* x_402; obj* x_405; obj* x_407; obj* x_410; obj* x_412; obj* x_414; obj* x_417; obj* x_418; obj* x_421; obj* x_422; obj* x_423; 
x_402 = lean::cnstr_get(x_393, 0);
lean::inc(x_402);
lean::dec(x_393);
x_405 = lean::cnstr_get(x_402, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_402, 1);
lean::inc(x_407);
lean::dec(x_402);
x_410 = lean::cnstr_get(x_407, 0);
lean::inc(x_410);
x_412 = lean::cnstr_get(x_407, 1);
lean::inc(x_412);
x_414 = lean::cnstr_get(x_407, 2);
lean::inc(x_414);
lean::dec(x_407);
x_417 = l_lean_parser_term_binders_has__view;
x_418 = lean::cnstr_get(x_417, 0);
lean::inc(x_418);
lean::dec(x_417);
x_421 = lean::apply_1(x_418, x_405);
if (lean::is_scalar(x_350)) {
 x_422 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_422 = x_350;
}
lean::cnstr_set(x_422, 0, x_421);
x_423 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_423, 0, x_410);
lean::cnstr_set(x_423, 1, x_412);
lean::cnstr_set(x_423, 2, x_414);
lean::cnstr_set(x_423, 3, x_422);
x_1 = x_11;
x_2 = x_423;
goto _start;
}
}
default:
{
obj* x_426; obj* x_429; obj* x_431; 
lean::dec(x_350);
x_426 = lean::cnstr_get(x_348, 0);
lean::inc(x_426);
lean::dec(x_348);
x_429 = lean::cnstr_get(x_426, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_426, 1);
lean::inc(x_431);
lean::dec(x_426);
if (lean::obj_tag(x_431) == 0)
{
obj* x_435; 
lean::inc(x_3);
x_435 = l___private_init_lean_expander_1__pop__stx__arg(x_340, x_3);
if (lean::obj_tag(x_435) == 0)
{
obj* x_441; obj* x_443; obj* x_444; 
lean::dec(x_429);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_342);
x_441 = lean::cnstr_get(x_435, 0);
if (lean::is_exclusive(x_435)) {
 lean::cnstr_set(x_435, 0, lean::box(0));
 x_443 = x_435;
} else {
 lean::inc(x_441);
 lean::dec(x_435);
 x_443 = lean::box(0);
}
if (lean::is_scalar(x_443)) {
 x_444 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_444 = x_443;
}
lean::cnstr_set(x_444, 0, x_441);
return x_444;
}
else
{
obj* x_445; obj* x_448; obj* x_450; obj* x_453; obj* x_455; obj* x_457; obj* x_458; obj* x_460; obj* x_461; obj* x_464; 
x_445 = lean::cnstr_get(x_435, 0);
lean::inc(x_445);
lean::dec(x_435);
x_448 = lean::cnstr_get(x_445, 0);
lean::inc(x_448);
x_450 = lean::cnstr_get(x_445, 1);
lean::inc(x_450);
lean::dec(x_445);
x_453 = lean::cnstr_get(x_450, 0);
lean::inc(x_453);
x_455 = lean::cnstr_get(x_450, 1);
lean::inc(x_455);
if (lean::is_scalar(x_342)) {
 x_457 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_457 = x_342;
}
lean::cnstr_set(x_457, 0, x_429);
lean::cnstr_set(x_457, 1, x_448);
x_458 = lean::cnstr_get(x_450, 2);
lean::inc(x_458);
x_460 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_460, 0, x_457);
lean::cnstr_set(x_460, 1, x_458);
x_461 = lean::cnstr_get(x_450, 3);
lean::inc(x_461);
lean::dec(x_450);
x_464 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_464, 0, x_453);
lean::cnstr_set(x_464, 1, x_455);
lean::cnstr_set(x_464, 2, x_460);
lean::cnstr_set(x_464, 3, x_461);
x_1 = x_11;
x_2 = x_464;
goto _start;
}
}
else
{
obj* x_466; obj* x_469; 
x_466 = lean::cnstr_get(x_431, 0);
lean::inc(x_466);
lean::dec(x_431);
x_469 = lean::cnstr_get(x_466, 1);
lean::inc(x_469);
lean::dec(x_466);
switch (lean::obj_tag(x_469)) {
case 0:
{
obj* x_474; 
lean::dec(x_469);
lean::inc(x_3);
x_474 = l___private_init_lean_expander_1__pop__stx__arg(x_340, x_3);
if (lean::obj_tag(x_474) == 0)
{
obj* x_480; obj* x_482; obj* x_483; 
lean::dec(x_429);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_342);
x_480 = lean::cnstr_get(x_474, 0);
if (lean::is_exclusive(x_474)) {
 lean::cnstr_set(x_474, 0, lean::box(0));
 x_482 = x_474;
} else {
 lean::inc(x_480);
 lean::dec(x_474);
 x_482 = lean::box(0);
}
if (lean::is_scalar(x_482)) {
 x_483 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_483 = x_482;
}
lean::cnstr_set(x_483, 0, x_480);
return x_483;
}
else
{
obj* x_484; obj* x_487; obj* x_489; obj* x_492; obj* x_494; obj* x_496; obj* x_497; obj* x_499; obj* x_500; obj* x_503; 
x_484 = lean::cnstr_get(x_474, 0);
lean::inc(x_484);
lean::dec(x_474);
x_487 = lean::cnstr_get(x_484, 0);
lean::inc(x_487);
x_489 = lean::cnstr_get(x_484, 1);
lean::inc(x_489);
lean::dec(x_484);
x_492 = lean::cnstr_get(x_489, 0);
lean::inc(x_492);
x_494 = lean::cnstr_get(x_489, 1);
lean::inc(x_494);
if (lean::is_scalar(x_342)) {
 x_496 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_496 = x_342;
}
lean::cnstr_set(x_496, 0, x_429);
lean::cnstr_set(x_496, 1, x_487);
x_497 = lean::cnstr_get(x_489, 2);
lean::inc(x_497);
x_499 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_499, 0, x_496);
lean::cnstr_set(x_499, 1, x_497);
x_500 = lean::cnstr_get(x_489, 3);
lean::inc(x_500);
lean::dec(x_489);
x_503 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_503, 0, x_492);
lean::cnstr_set(x_503, 1, x_494);
lean::cnstr_set(x_503, 2, x_499);
lean::cnstr_set(x_503, 3, x_500);
x_1 = x_11;
x_2 = x_503;
goto _start;
}
}
case 2:
{
obj* x_505; obj* x_509; 
x_505 = lean::cnstr_get(x_469, 0);
lean::inc(x_505);
lean::dec(x_469);
lean::inc(x_3);
x_509 = l___private_init_lean_expander_1__pop__stx__arg(x_340, x_3);
if (lean::obj_tag(x_509) == 0)
{
obj* x_516; obj* x_518; obj* x_519; 
lean::dec(x_429);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_505);
lean::dec(x_342);
x_516 = lean::cnstr_get(x_509, 0);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_set(x_509, 0, lean::box(0));
 x_518 = x_509;
} else {
 lean::inc(x_516);
 lean::dec(x_509);
 x_518 = lean::box(0);
}
if (lean::is_scalar(x_518)) {
 x_519 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_519 = x_518;
}
lean::cnstr_set(x_519, 0, x_516);
return x_519;
}
else
{
obj* x_520; obj* x_522; obj* x_523; obj* x_525; obj* x_528; obj* x_530; obj* x_532; obj* x_534; 
x_520 = lean::cnstr_get(x_509, 0);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_set(x_509, 0, lean::box(0));
 x_522 = x_509;
} else {
 lean::inc(x_520);
 lean::dec(x_509);
 x_522 = lean::box(0);
}
x_523 = lean::cnstr_get(x_520, 0);
lean::inc(x_523);
x_525 = lean::cnstr_get(x_520, 1);
lean::inc(x_525);
lean::dec(x_520);
x_528 = lean::cnstr_get(x_525, 0);
lean::inc(x_528);
x_530 = lean::cnstr_get(x_525, 1);
lean::inc(x_530);
x_532 = lean::cnstr_get(x_525, 2);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_525, 3);
lean::inc(x_534);
if (lean::obj_tag(x_534) == 0)
{
obj* x_543; obj* x_546; 
lean::dec(x_429);
lean::dec(x_528);
lean::dec(x_523);
lean::dec(x_530);
lean::dec(x_505);
lean::dec(x_342);
lean::dec(x_532);
x_543 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_546 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_543, x_525, x_3);
if (lean::obj_tag(x_546) == 0)
{
obj* x_550; obj* x_553; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_550 = lean::cnstr_get(x_546, 0);
lean::inc(x_550);
lean::dec(x_546);
if (lean::is_scalar(x_522)) {
 x_553 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_553 = x_522;
 lean::cnstr_set_tag(x_522, 0);
}
lean::cnstr_set(x_553, 0, x_550);
return x_553;
}
else
{
obj* x_555; obj* x_558; 
lean::dec(x_522);
x_555 = lean::cnstr_get(x_546, 0);
lean::inc(x_555);
lean::dec(x_546);
x_558 = lean::cnstr_get(x_555, 1);
lean::inc(x_558);
lean::dec(x_555);
x_1 = x_11;
x_2 = x_558;
goto _start;
}
}
else
{
obj* x_564; obj* x_566; obj* x_567; obj* x_570; obj* x_571; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_580; obj* x_581; obj* x_582; obj* x_584; obj* x_585; obj* x_586; obj* x_587; obj* x_588; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; 
lean::dec(x_522);
lean::dec(x_525);
x_564 = lean::cnstr_get(x_534, 0);
lean::inc(x_564);
x_566 = l_lean_parser_term_lambda_has__view;
x_567 = lean::cnstr_get(x_566, 1);
lean::inc(x_567);
lean::dec(x_566);
x_570 = lean::box(0);
x_571 = lean::cnstr_get(x_505, 3);
lean::inc(x_571);
x_573 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_573, 0, x_571);
lean::cnstr_set(x_573, 1, x_570);
x_574 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_573);
x_575 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_575, 0, x_574);
lean::cnstr_set(x_575, 1, x_570);
x_576 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_576, 0, x_575);
x_577 = lean::cnstr_get(x_505, 5);
lean::inc(x_577);
lean::dec(x_505);
x_580 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_581 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_582 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_582, 0, x_580);
lean::cnstr_set(x_582, 1, x_576);
lean::cnstr_set(x_582, 2, x_581);
lean::cnstr_set(x_582, 3, x_577);
lean::inc(x_567);
x_584 = lean::apply_1(x_567, x_582);
x_585 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_585, 0, x_580);
lean::cnstr_set(x_585, 1, x_564);
lean::cnstr_set(x_585, 2, x_581);
lean::cnstr_set(x_585, 3, x_523);
x_586 = lean::apply_1(x_567, x_585);
x_587 = l_lean_parser_term_app_has__view;
x_588 = lean::cnstr_get(x_587, 1);
lean::inc(x_588);
lean::dec(x_587);
x_591 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_591, 0, x_584);
lean::cnstr_set(x_591, 1, x_586);
x_592 = lean::apply_1(x_588, x_591);
if (lean::is_scalar(x_342)) {
 x_593 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_593 = x_342;
}
lean::cnstr_set(x_593, 0, x_429);
lean::cnstr_set(x_593, 1, x_592);
x_594 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_594, 0, x_593);
lean::cnstr_set(x_594, 1, x_532);
x_595 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_595, 0, x_528);
lean::cnstr_set(x_595, 1, x_530);
lean::cnstr_set(x_595, 2, x_594);
lean::cnstr_set(x_595, 3, x_534);
x_1 = x_11;
x_2 = x_595;
goto _start;
}
}
}
default:
{
obj* x_600; obj* x_603; 
lean::dec(x_469);
lean::dec(x_429);
lean::dec(x_342);
x_600 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_0);
x_603 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_600, x_340, x_3);
if (lean::obj_tag(x_603) == 0)
{
obj* x_607; obj* x_609; obj* x_610; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_607 = lean::cnstr_get(x_603, 0);
if (lean::is_exclusive(x_603)) {
 lean::cnstr_set(x_603, 0, lean::box(0));
 x_609 = x_603;
} else {
 lean::inc(x_607);
 lean::dec(x_603);
 x_609 = lean::box(0);
}
if (lean::is_scalar(x_609)) {
 x_610 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_610 = x_609;
}
lean::cnstr_set(x_610, 0, x_607);
return x_610;
}
else
{
obj* x_611; obj* x_614; 
x_611 = lean::cnstr_get(x_603, 0);
lean::inc(x_611);
lean::dec(x_603);
x_614 = lean::cnstr_get(x_611, 1);
lean::inc(x_614);
lean::dec(x_611);
x_1 = x_11;
x_2 = x_614;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
obj* x_5; obj* x_8; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_13);
return x_16;
}
else
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_8);
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
obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_22; obj* x_24; 
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
lean::inc(x_1);
x_16 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_14);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; 
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_16);
x_24 = x_26;
goto lbl_25;
}
else
{
obj* x_27; obj* x_31; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
lean::dec(x_22);
lean::inc(x_2);
x_31 = l___private_init_lean_expander_1__pop__stx__arg(x_16, x_2);
if (lean::obj_tag(x_31) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_27);
x_38 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_set(x_31, 0, lean::box(0));
 x_40 = x_31;
} else {
 lean::inc(x_38);
 lean::dec(x_31);
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
obj* x_42; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; 
x_42 = lean::cnstr_get(x_31, 0);
lean::inc(x_42);
lean::dec(x_31);
x_45 = lean::cnstr_get(x_42, 0);
x_47 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 lean::cnstr_set(x_42, 1, lean::box(0));
 x_49 = x_42;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_42);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
if (lean::is_scalar(x_49)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_49;
}
lean::cnstr_set(x_54, 0, x_27);
lean::cnstr_set(x_54, 1, x_45);
x_55 = lean::cnstr_get(x_47, 2);
lean::inc(x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
x_58 = lean::cnstr_get(x_47, 3);
lean::inc(x_58);
lean::dec(x_47);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_50);
lean::cnstr_set(x_61, 1, x_52);
lean::cnstr_set(x_61, 2, x_57);
lean::cnstr_set(x_61, 3, x_58);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_14);
lean::cnstr_set(x_62, 1, x_61);
x_24 = x_62;
goto lbl_25;
}
}
lbl_25:
{
obj* x_63; obj* x_66; obj* x_69; 
x_63 = lean::cnstr_get(x_24, 1);
lean::inc(x_63);
lean::dec(x_24);
x_66 = lean::cnstr_get(x_20, 1);
lean::inc(x_66);
lean::dec(x_20);
x_69 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_66, x_63, x_2);
if (lean::obj_tag(x_69) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_17);
lean::dec(x_10);
x_72 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_set(x_69, 0, lean::box(0));
 x_74 = x_69;
} else {
 lean::inc(x_72);
 lean::dec(x_69);
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
obj* x_76; obj* x_78; obj* x_79; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
x_76 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_set(x_69, 0, lean::box(0));
 x_78 = x_69;
} else {
 lean::inc(x_76);
 lean::dec(x_69);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = lean::cnstr_get(x_79, 2);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_82);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1), 2, 1);
lean::closure_set(x_86, 0, x_85);
x_87 = lean::cnstr_get(x_17, 4);
lean::inc(x_87);
lean::dec(x_17);
x_90 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_86, x_87);
if (lean::is_scalar(x_10)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_10;
}
lean::cnstr_set(x_91, 0, x_90);
if (lean::is_scalar(x_78)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_78;
}
lean::cnstr_set(x_92, 0, x_91);
return x_92;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
return x_7;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
return x_7;
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
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_13 = l_option_map___rarg(x_12, x_5);
x_14 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_15 = l_option_map___rarg(x_14, x_13);
x_16 = l_lean_expander_mixfix__to__notation__spec___closed__5;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_11);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
case 3:
{
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_3 = x_26;
goto lbl_4;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; uint8 x_34; 
x_27 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_29 = x_5;
} else {
 lean::inc(x_27);
 lean::dec(x_5);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
x_32 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_30);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::nat_dec_eq(x_32, x_33);
if (x_34 == 0)
{
obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_2);
lean::dec(x_27);
x_37 = lean::mk_nat_obj(1u);
x_38 = lean::nat_sub(x_32, x_37);
lean::dec(x_32);
x_40 = l_lean_parser_number_view_of__nat(x_38);
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
if (lean::is_scalar(x_29)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_29;
}
lean::cnstr_set(x_46, 0, x_45);
x_3 = x_46;
goto lbl_4;
}
else
{
obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_29);
lean::dec(x_32);
x_49 = l_lean_parser_command_notation__spec_precedence_has__view;
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
lean::dec(x_49);
x_53 = lean::apply_1(x_50, x_27);
x_54 = l_lean_expander_mixfix__to__notation__spec___closed__6;
x_55 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_53, x_54, x_2);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_1);
x_57 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_set(x_55, 0, lean::box(0));
 x_59 = x_55;
} else {
 lean::inc(x_57);
 lean::dec(x_55);
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
obj* x_61; 
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
lean::dec(x_55);
x_3 = x_61;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_67);
x_70 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_69);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
default:
{
obj* x_75; 
lean::dec(x_0);
lean::dec(x_2);
x_75 = lean::box(0);
x_7 = x_75;
goto lbl_8;
}
}
lbl_4:
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_76 = lean::box(0);
x_77 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_3);
x_79 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_1);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_76);
x_83 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
lbl_8:
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_7);
x_87 = lean::box(0);
x_88 = l_lean_expander_mixfix__to__notation__spec___closed__3;
x_89 = l_option_map___rarg(x_88, x_5);
x_90 = l_lean_expander_mixfix__to__notation__spec___closed__4;
x_91 = l_option_map___rarg(x_90, x_89);
x_92 = l_lean_expander_mixfix__to__notation__spec___closed__1;
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_1);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_87);
x_98 = l_lean_expander_mixfix__to__notation__spec___closed__2;
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_97);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
return x_100;
}
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::mk_string("a");
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::apply_1(x_2, x_12);
return x_13;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::mk_string("b");
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::apply_1(x_2, x_12);
return x_13;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::mk_string("b");
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::apply_1(x_2, x_12);
return x_13;
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
 lean::cnstr_set(x_23, 0, lean::box(0));
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
 lean::cnstr_set(x_12, 0, lean::box(0));
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
 lean::cnstr_set(x_12, 0, lean::box(0));
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
return x_7;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
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
obj* x_0; obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
lean::cnstr_set(x_1, 2, x_0);
x_2 = 0;
x_3 = lean::box(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
return x_9;
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
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_18, 1);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_28);
x_45 = lean::cnstr_get(x_18, 0);
lean::inc(x_45);
lean::dec(x_18);
x_48 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_39, x_45);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
else
{
obj* x_52; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_39);
lean::dec(x_41);
x_52 = l_lean_parser_term_binder__default_has__view;
x_53 = lean::cnstr_get(x_52, 1);
lean::inc(x_53);
lean::dec(x_52);
x_56 = lean::apply_1(x_53, x_28);
x_57 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_58 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_56, x_57, x_1);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_18);
x_60 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_set(x_58, 0, lean::box(0));
 x_62 = x_58;
} else {
 lean::inc(x_60);
 lean::dec(x_58);
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
obj* x_64; obj* x_66; obj* x_67; obj* x_70; obj* x_71; 
x_64 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_set(x_58, 0, lean::box(0));
 x_66 = x_58;
} else {
 lean::inc(x_64);
 lean::dec(x_58);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_18, 0);
lean::inc(x_67);
lean::dec(x_18);
x_70 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_64, x_67);
if (lean::is_scalar(x_66)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_66;
}
lean::cnstr_set(x_71, 0, x_70);
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
obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_1);
x_77 = lean::cnstr_get(x_6, 0);
lean::inc(x_77);
x_79 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_77);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
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
obj* x_85; obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_1);
x_85 = lean::cnstr_get(x_81, 0);
lean::inc(x_85);
lean::dec(x_81);
x_88 = lean::cnstr_get(x_6, 0);
lean::inc(x_88);
x_90 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_85, x_88);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
else
{
obj* x_92; obj* x_94; 
x_92 = lean::cnstr_get(x_81, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_6, 1);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_1);
lean::dec(x_81);
x_98 = lean::cnstr_get(x_6, 0);
lean::inc(x_98);
lean::dec(x_6);
x_101 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_92, x_98);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
else
{
obj* x_105; obj* x_106; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_94);
lean::dec(x_92);
x_105 = l_lean_parser_term_binder__default_has__view;
x_106 = lean::cnstr_get(x_105, 1);
lean::inc(x_106);
lean::dec(x_105);
x_109 = lean::apply_1(x_106, x_81);
x_110 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_111 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_109, x_110, x_1);
if (lean::obj_tag(x_111) == 0)
{
obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_6);
x_113 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_set(x_111, 0, lean::box(0));
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
obj* x_117; obj* x_119; obj* x_120; obj* x_123; obj* x_124; 
x_117 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_set(x_111, 0, lean::box(0));
 x_119 = x_111;
} else {
 lean::inc(x_117);
 lean::dec(x_111);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_6, 0);
lean::inc(x_120);
lean::dec(x_6);
x_123 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_117, x_120);
if (lean::is_scalar(x_119)) {
 x_124 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_124 = x_119;
}
lean::cnstr_set(x_124, 0, x_123);
return x_124;
}
}
}
}
}
case 2:
{
obj* x_127; 
lean::dec(x_4);
lean::dec(x_0);
x_127 = lean::cnstr_get(x_6, 2);
lean::inc(x_127);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_1);
x_130 = lean::cnstr_get(x_6, 0);
lean::inc(x_130);
x_132 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_130);
x_133 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_133, 0, x_132);
return x_133;
}
else
{
obj* x_134; 
x_134 = lean::cnstr_get(x_127, 0);
lean::inc(x_134);
lean::dec(x_127);
if (lean::obj_tag(x_134) == 0)
{
obj* x_138; obj* x_141; obj* x_143; obj* x_144; 
lean::dec(x_1);
x_138 = lean::cnstr_get(x_134, 0);
lean::inc(x_138);
lean::dec(x_134);
x_141 = lean::cnstr_get(x_6, 0);
lean::inc(x_141);
x_143 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_138, x_141);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_143);
return x_144;
}
else
{
obj* x_145; obj* x_147; 
x_145 = lean::cnstr_get(x_134, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_6, 1);
lean::inc(x_147);
if (lean::obj_tag(x_147) == 0)
{
obj* x_151; obj* x_154; obj* x_155; 
lean::dec(x_1);
lean::dec(x_134);
x_151 = lean::cnstr_get(x_6, 0);
lean::inc(x_151);
lean::dec(x_6);
x_154 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_145, x_151);
x_155 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
return x_155;
}
else
{
obj* x_158; obj* x_159; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_147);
lean::dec(x_145);
x_158 = l_lean_parser_term_binder__default_has__view;
x_159 = lean::cnstr_get(x_158, 1);
lean::inc(x_159);
lean::dec(x_158);
x_162 = lean::apply_1(x_159, x_134);
x_163 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_164 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_162, x_163, x_1);
if (lean::obj_tag(x_164) == 0)
{
obj* x_166; obj* x_168; obj* x_169; 
lean::dec(x_6);
x_166 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_set(x_164, 0, lean::box(0));
 x_168 = x_164;
} else {
 lean::inc(x_166);
 lean::dec(x_164);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
return x_169;
}
else
{
obj* x_170; obj* x_172; obj* x_173; obj* x_176; obj* x_177; 
x_170 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_set(x_164, 0, lean::box(0));
 x_172 = x_164;
} else {
 lean::inc(x_170);
 lean::dec(x_164);
 x_172 = lean::box(0);
}
x_173 = lean::cnstr_get(x_6, 0);
lean::inc(x_173);
lean::dec(x_6);
x_176 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_170, x_173);
if (lean::is_scalar(x_172)) {
 x_177 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_177 = x_172;
}
lean::cnstr_set(x_177, 0, x_176);
return x_177;
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
obj* x_181; obj* x_184; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_181 = lean::cnstr_get(x_6, 0);
lean::inc(x_181);
lean::dec(x_6);
x_184 = lean::cnstr_get(x_181, 0);
lean::inc(x_184);
x_186 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_186, 0, x_184);
x_187 = lean::box(0);
x_188 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_188, 0, x_186);
lean::cnstr_set(x_188, 1, x_187);
x_189 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_181, x_188);
x_190 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_190, 0, x_189);
return x_190;
}
else
{
obj* x_191; obj* x_194; obj* x_195; obj* x_196; 
x_191 = lean::cnstr_get(x_6, 0);
lean::inc(x_191);
lean::dec(x_6);
x_194 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_195 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_191, x_194);
x_196 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_196, 0, x_195);
return x_196;
}
}
default:
{
obj* x_199; obj* x_200; obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_6);
lean::dec(x_0);
x_199 = l_lean_parser_term_anonymous__constructor_has__view;
x_200 = lean::cnstr_get(x_199, 1);
lean::inc(x_200);
lean::dec(x_199);
x_203 = lean::apply_1(x_200, x_4);
x_204 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_206 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_203, x_204, x_1);
if (lean::obj_tag(x_206) == 0)
{
obj* x_208; obj* x_210; obj* x_211; 
lean::dec(x_1);
x_208 = lean::cnstr_get(x_206, 0);
if (lean::is_exclusive(x_206)) {
 lean::cnstr_set(x_206, 0, lean::box(0));
 x_210 = x_206;
} else {
 lean::inc(x_208);
 lean::dec(x_206);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_208);
return x_211;
}
else
{
obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_220; 
x_212 = lean::cnstr_get(x_206, 0);
if (lean::is_exclusive(x_206)) {
 lean::cnstr_set(x_206, 0, lean::box(0));
 x_214 = x_206;
} else {
 lean::inc(x_212);
 lean::dec(x_206);
 x_214 = lean::box(0);
}
x_215 = lean::cnstr_get(x_212, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 1);
lean::inc(x_217);
lean::dec(x_212);
x_220 = lean::cnstr_get(x_217, 2);
lean::inc(x_220);
if (lean::obj_tag(x_220) == 0)
{
obj* x_223; uint8 x_225; obj* x_226; obj* x_227; 
lean::dec(x_1);
x_223 = lean::cnstr_get(x_217, 0);
lean::inc(x_223);
x_225 = lean::unbox(x_215);
x_226 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_225, x_217, x_223);
if (lean::is_scalar(x_214)) {
 x_227 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_227 = x_214;
}
lean::cnstr_set(x_227, 0, x_226);
return x_227;
}
else
{
obj* x_228; 
x_228 = lean::cnstr_get(x_220, 0);
lean::inc(x_228);
lean::dec(x_220);
if (lean::obj_tag(x_228) == 0)
{
obj* x_232; obj* x_235; uint8 x_237; obj* x_238; obj* x_239; 
lean::dec(x_1);
x_232 = lean::cnstr_get(x_228, 0);
lean::inc(x_232);
lean::dec(x_228);
x_235 = lean::cnstr_get(x_217, 0);
lean::inc(x_235);
x_237 = lean::unbox(x_215);
x_238 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_237, x_217, x_232, x_235);
if (lean::is_scalar(x_214)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_214;
}
lean::cnstr_set(x_239, 0, x_238);
return x_239;
}
else
{
obj* x_240; obj* x_242; 
x_240 = lean::cnstr_get(x_228, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get(x_217, 1);
lean::inc(x_242);
if (lean::obj_tag(x_242) == 0)
{
obj* x_246; uint8 x_249; obj* x_250; obj* x_251; 
lean::dec(x_228);
lean::dec(x_1);
x_246 = lean::cnstr_get(x_217, 0);
lean::inc(x_246);
lean::dec(x_217);
x_249 = lean::unbox(x_215);
x_250 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_249, x_240, x_246);
if (lean::is_scalar(x_214)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_214;
}
lean::cnstr_set(x_251, 0, x_250);
return x_251;
}
else
{
obj* x_254; obj* x_255; obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_242);
lean::dec(x_240);
x_254 = l_lean_parser_term_binder__default_has__view;
x_255 = lean::cnstr_get(x_254, 1);
lean::inc(x_255);
lean::dec(x_254);
x_258 = lean::apply_1(x_255, x_228);
x_259 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_260 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_258, x_259, x_1);
if (lean::obj_tag(x_260) == 0)
{
obj* x_263; obj* x_266; 
lean::dec(x_215);
lean::dec(x_217);
x_263 = lean::cnstr_get(x_260, 0);
lean::inc(x_263);
lean::dec(x_260);
if (lean::is_scalar(x_214)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_214;
 lean::cnstr_set_tag(x_214, 0);
}
lean::cnstr_set(x_266, 0, x_263);
return x_266;
}
else
{
obj* x_267; obj* x_270; uint8 x_273; obj* x_274; obj* x_275; 
x_267 = lean::cnstr_get(x_260, 0);
lean::inc(x_267);
lean::dec(x_260);
x_270 = lean::cnstr_get(x_217, 0);
lean::inc(x_270);
lean::dec(x_217);
x_273 = lean::unbox(x_215);
x_274 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_273, x_267, x_270);
if (lean::is_scalar(x_214)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_214;
}
lean::cnstr_set(x_275, 0, x_274);
return x_275;
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
obj* x_276; obj* x_279; 
x_276 = lean::cnstr_get(x_0, 0);
lean::inc(x_276);
lean::dec(x_0);
x_279 = lean::cnstr_get(x_276, 1);
lean::inc(x_279);
lean::dec(x_276);
if (lean::obj_tag(x_279) == 0)
{
obj* x_283; 
lean::dec(x_279);
x_283 = l_lean_expander_expand__bracketed__binder___main___closed__3;
x_2 = x_283;
goto lbl_3;
}
else
{
obj* x_284; uint8 x_287; obj* x_288; obj* x_289; 
x_284 = lean::cnstr_get(x_279, 0);
lean::inc(x_284);
lean::dec(x_279);
x_287 = 0;
x_288 = lean::box(x_287);
x_289 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_284);
x_2 = x_289;
goto lbl_3;
}
}
case 1:
{
obj* x_290; obj* x_293; uint8 x_296; obj* x_297; obj* x_298; 
x_290 = lean::cnstr_get(x_0, 0);
lean::inc(x_290);
lean::dec(x_0);
x_293 = lean::cnstr_get(x_290, 1);
lean::inc(x_293);
lean::dec(x_290);
x_296 = 1;
x_297 = lean::box(x_296);
x_298 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_293);
x_2 = x_298;
goto lbl_3;
}
case 2:
{
obj* x_299; obj* x_302; uint8 x_305; obj* x_306; obj* x_307; 
x_299 = lean::cnstr_get(x_0, 0);
lean::inc(x_299);
lean::dec(x_0);
x_302 = lean::cnstr_get(x_299, 1);
lean::inc(x_302);
lean::dec(x_299);
x_305 = 2;
x_306 = lean::box(x_305);
x_307 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_307, 0, x_306);
lean::cnstr_set(x_307, 1, x_302);
x_2 = x_307;
goto lbl_3;
}
case 3:
{
obj* x_308; obj* x_311; 
x_308 = lean::cnstr_get(x_0, 0);
lean::inc(x_308);
lean::dec(x_0);
x_311 = lean::cnstr_get(x_308, 1);
lean::inc(x_311);
lean::dec(x_308);
if (lean::obj_tag(x_311) == 0)
{
obj* x_314; obj* x_317; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_325; obj* x_326; obj* x_327; obj* x_328; uint8 x_329; obj* x_330; obj* x_331; 
x_314 = lean::cnstr_get(x_311, 0);
lean::inc(x_314);
lean::dec(x_311);
x_317 = lean::cnstr_get(x_314, 0);
lean::inc(x_317);
x_319 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_319, 0, x_317);
x_320 = lean::box(0);
x_321 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_321, 0, x_319);
lean::cnstr_set(x_321, 1, x_320);
x_322 = lean::cnstr_get(x_314, 2);
lean::inc(x_322);
lean::dec(x_314);
x_325 = l_lean_expander_mk__simple__binder___closed__1;
x_326 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_326, 0, x_325);
lean::cnstr_set(x_326, 1, x_322);
x_327 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_327, 0, x_326);
x_328 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_328, 0, x_321);
lean::cnstr_set(x_328, 1, x_327);
lean::cnstr_set(x_328, 2, x_320);
x_329 = 3;
x_330 = lean::box(x_329);
x_331 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_328);
x_2 = x_331;
goto lbl_3;
}
else
{
obj* x_332; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; uint8 x_341; obj* x_342; obj* x_343; 
x_332 = lean::cnstr_get(x_311, 0);
lean::inc(x_332);
lean::dec(x_311);
x_335 = lean::box(0);
x_336 = l_lean_expander_mk__simple__binder___closed__1;
x_337 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_337, 0, x_336);
lean::cnstr_set(x_337, 1, x_332);
x_338 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_338, 0, x_337);
x_339 = l_lean_expander_expand__bracketed__binder___main___closed__6;
x_340 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_340, 0, x_339);
lean::cnstr_set(x_340, 1, x_338);
lean::cnstr_set(x_340, 2, x_335);
x_341 = 3;
x_342 = lean::box(x_341);
x_343 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_340);
x_2 = x_343;
goto lbl_3;
}
}
default:
{
obj* x_344; obj* x_347; obj* x_348; obj* x_351; obj* x_352; obj* x_354; 
x_344 = lean::cnstr_get(x_0, 0);
lean::inc(x_344);
lean::dec(x_0);
x_347 = l_lean_parser_term_anonymous__constructor_has__view;
x_348 = lean::cnstr_get(x_347, 1);
lean::inc(x_348);
lean::dec(x_347);
x_351 = lean::apply_1(x_348, x_344);
x_352 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
x_354 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_351, x_352, x_1);
if (lean::obj_tag(x_354) == 0)
{
obj* x_356; obj* x_358; obj* x_359; 
lean::dec(x_1);
x_356 = lean::cnstr_get(x_354, 0);
if (lean::is_exclusive(x_354)) {
 lean::cnstr_set(x_354, 0, lean::box(0));
 x_358 = x_354;
} else {
 lean::inc(x_356);
 lean::dec(x_354);
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
obj* x_360; 
x_360 = lean::cnstr_get(x_354, 0);
lean::inc(x_360);
lean::dec(x_354);
x_2 = x_360;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_363; obj* x_365; obj* x_368; 
x_363 = lean::cnstr_get(x_2, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_2, 1);
lean::inc(x_365);
lean::dec(x_2);
x_368 = lean::cnstr_get(x_365, 2);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_371; uint8 x_373; obj* x_374; obj* x_375; 
lean::dec(x_1);
x_371 = lean::cnstr_get(x_365, 0);
lean::inc(x_371);
x_373 = lean::unbox(x_363);
x_374 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_373, x_365, x_371);
x_375 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_375, 0, x_374);
return x_375;
}
else
{
obj* x_376; 
x_376 = lean::cnstr_get(x_368, 0);
lean::inc(x_376);
lean::dec(x_368);
if (lean::obj_tag(x_376) == 0)
{
obj* x_380; obj* x_383; uint8 x_385; obj* x_386; obj* x_387; 
lean::dec(x_1);
x_380 = lean::cnstr_get(x_376, 0);
lean::inc(x_380);
lean::dec(x_376);
x_383 = lean::cnstr_get(x_365, 0);
lean::inc(x_383);
x_385 = lean::unbox(x_363);
x_386 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_385, x_365, x_380, x_383);
x_387 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_387, 0, x_386);
return x_387;
}
else
{
obj* x_388; obj* x_390; 
x_388 = lean::cnstr_get(x_376, 0);
lean::inc(x_388);
x_390 = lean::cnstr_get(x_365, 1);
lean::inc(x_390);
if (lean::obj_tag(x_390) == 0)
{
obj* x_394; uint8 x_397; obj* x_398; obj* x_399; 
lean::dec(x_376);
lean::dec(x_1);
x_394 = lean::cnstr_get(x_365, 0);
lean::inc(x_394);
lean::dec(x_365);
x_397 = lean::unbox(x_363);
x_398 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_397, x_388, x_394);
x_399 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_399, 0, x_398);
return x_399;
}
else
{
obj* x_402; obj* x_403; obj* x_406; obj* x_407; obj* x_408; 
lean::dec(x_388);
lean::dec(x_390);
x_402 = l_lean_parser_term_binder__default_has__view;
x_403 = lean::cnstr_get(x_402, 1);
lean::inc(x_403);
lean::dec(x_402);
x_406 = lean::apply_1(x_403, x_376);
x_407 = l_lean_expander_expand__bracketed__binder___main___closed__2;
x_408 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_406, x_407, x_1);
if (lean::obj_tag(x_408) == 0)
{
obj* x_411; obj* x_413; obj* x_414; 
lean::dec(x_365);
lean::dec(x_363);
x_411 = lean::cnstr_get(x_408, 0);
if (lean::is_exclusive(x_408)) {
 lean::cnstr_set(x_408, 0, lean::box(0));
 x_413 = x_408;
} else {
 lean::inc(x_411);
 lean::dec(x_408);
 x_413 = lean::box(0);
}
if (lean::is_scalar(x_413)) {
 x_414 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_414 = x_413;
}
lean::cnstr_set(x_414, 0, x_411);
return x_414;
}
else
{
obj* x_415; obj* x_417; obj* x_418; uint8 x_421; obj* x_422; obj* x_423; 
x_415 = lean::cnstr_get(x_408, 0);
if (lean::is_exclusive(x_408)) {
 lean::cnstr_set(x_408, 0, lean::box(0));
 x_417 = x_408;
} else {
 lean::inc(x_415);
 lean::dec(x_408);
 x_417 = lean::box(0);
}
x_418 = lean::cnstr_get(x_365, 0);
lean::inc(x_418);
lean::dec(x_365);
x_421 = lean::unbox(x_363);
x_422 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_421, x_415, x_418);
if (lean::is_scalar(x_417)) {
 x_423 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_423 = x_417;
}
lean::cnstr_set(x_423, 0, x_422);
return x_423;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
x_8 = l_lean_parser_ident__univs_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::apply_1(x_9, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
return x_15;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
x_8 = l_lean_parser_term_hole_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::mk_string("_");
x_13 = l_string_trim(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_1(x_9, x_15);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_7, x_17, x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
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
 lean::cnstr_set(x_14, 0, lean::box(0));
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
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_25 = x_14;
} else {
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
lean::dec(x_7);
switch (lean::obj_tag(x_26)) {
case 4:
{
obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_3);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_26, 0);
lean::inc(x_33);
lean::dec(x_26);
x_36 = lean::box(0);
x_37 = l_lean_parser_term_match_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_41 = l_lean_parser_term_anonymous__constructor_has__view;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_33);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_36);
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
lean::cnstr_set(x_50, 1, x_36);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_36);
x_52 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_53 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
x_54 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
x_55 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_36);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set(x_55, 4, x_36);
lean::cnstr_set(x_55, 5, x_51);
x_56 = lean::apply_1(x_38, x_55);
x_57 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
x_58 = lean::apply_2(x_0, x_57, x_56);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
default:
{
obj* x_61; 
lean::dec(x_11);
x_61 = lean::box(0);
x_29 = x_61;
goto lbl_30;
}
}
lbl_30:
{
obj* x_63; 
lean::dec(x_29);
x_63 = l_lean_expander_expand__bracketed__binder___main(x_26, x_3);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_69; 
lean::dec(x_0);
lean::dec(x_23);
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
lean::dec(x_63);
if (lean::is_scalar(x_25)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_25;
 lean::cnstr_set_tag(x_25, 0);
}
lean::cnstr_set(x_69, 0, x_66);
return x_69;
}
else
{
obj* x_70; obj* x_73; obj* x_74; 
x_70 = lean::cnstr_get(x_63, 0);
lean::inc(x_70);
lean::dec(x_63);
x_73 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_23, x_70);
if (lean::is_scalar(x_25)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_25;
}
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
}
else
{
obj* x_77; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_11);
lean::dec(x_3);
x_77 = lean::cnstr_get(x_7, 0);
lean::inc(x_77);
lean::dec(x_7);
x_80 = l_lean_expander_binder__ident__to__ident___main(x_77);
x_81 = 0;
x_82 = l_lean_expander_get__opt__type___main___closed__1;
x_83 = l_lean_expander_mk__simple__binder(x_80, x_81, x_82);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
x_85 = lean::apply_2(x_0, x_84, x_23);
if (lean::is_scalar(x_25)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_25;
}
lean::cnstr_set(x_86, 0, x_85);
return x_86;
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
 lean::cnstr_set(x_60, 0, lean::box(0));
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
 lean::cnstr_set(x_10, 0, lean::box(0));
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
obj* x_18; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 x_20 = x_10;
} else {
 lean::inc(x_18);
 lean::dec(x_10);
 x_20 = lean::box(0);
}
x_21 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_8);
lean::dec(x_18);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
lean::dec(x_21);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_21, 0);
lean::inc(x_28);
lean::dec(x_21);
if (lean::is_scalar(x_8)) {
 x_31 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_31 = x_8;
}
lean::cnstr_set(x_31, 0, x_18);
lean::cnstr_set(x_31, 1, x_28);
if (lean::is_scalar(x_20)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_20;
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
 lean::cnstr_set(x_9, 0, lean::box(0));
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
 lean::cnstr_set(x_9, 0, lean::box(0));
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
return x_7;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
obj* x_3; obj* x_5; obj* x_7; 
lean::dec(x_1);
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
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_7);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_5, lean::box(0));
x_10 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
x_14 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
return x_14;
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
obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
x_12 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_14 = x_8;
} else {
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_21; 
if (lean::is_scalar(x_14)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_14;
}
lean::cnstr_set(x_20, 0, x_15);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_29; obj* x_30; 
lean::dec(x_14);
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_29 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_15, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_15);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_lean_expander_paren_transform___closed__2;
x_41 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_40, x_39);
if (lean::is_scalar(x_14)) {
 x_42 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_42 = x_14;
}
lean::cnstr_set(x_42, 0, x_41);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
obj* _init_l_lean_expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
return x_7;
}
}
obj* l_lean_expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_14; 
lean::dec(x_1);
x_3 = l_lean_parser_term_assume_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::apply_1(x_4, x_0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = l_lean_parser_term_lambda_has__view;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_7, 3);
lean::inc(x_14);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
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
obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_8, 0);
lean::inc(x_36);
lean::dec(x_8);
x_39 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_40 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_40);
lean::cnstr_set(x_41, 3, x_14);
x_42 = lean::apply_1(x_11, x_41);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
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
 lean::cnstr_set(x_8, 0, lean::box(0));
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; 
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
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_18 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
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
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_14);
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
obj* x_45; 
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_18);
x_45 = l_lean_expander_no__expansion___closed__1;
return x_45;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_46 = lean::box(0);
x_47 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_14);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::cnstr_get(x_3, 1);
lean::inc(x_52);
lean::dec(x_3);
x_55 = lean::cnstr_get(x_6, 0);
lean::inc(x_55);
x_57 = l_lean_parser_term_pi_has__view;
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
lean::dec(x_57);
x_61 = l_lean_expander_get__opt__type___main(x_16);
x_62 = l_lean_expander_arrow_transform___closed__2;
x_63 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_51);
x_65 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_51);
lean::cnstr_set(x_65, 2, x_63);
lean::cnstr_set(x_65, 3, x_61);
x_66 = lean::apply_1(x_58, x_65);
x_67 = l_lean_expander_mk__simple__binder___closed__1;
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
if (lean::is_scalar(x_18)) {
 x_70 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_70 = x_18;
}
lean::cnstr_set(x_70, 0, x_12);
lean::cnstr_set(x_70, 1, x_46);
lean::cnstr_set(x_70, 2, x_69);
if (lean::is_scalar(x_11)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_11;
}
lean::cnstr_set(x_71, 0, x_70);
x_72 = lean::cnstr_get(x_6, 2);
lean::inc(x_72);
x_74 = l_lean_parser_term_lambda_has__view;
x_75 = lean::cnstr_get(x_74, 1);
lean::inc(x_75);
lean::dec(x_74);
x_78 = lean::cnstr_get(x_6, 3);
lean::inc(x_78);
x_80 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_81 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_51);
lean::cnstr_set(x_81, 2, x_63);
lean::cnstr_set(x_81, 3, x_78);
x_82 = lean::apply_1(x_75, x_81);
x_83 = lean::cnstr_get(x_6, 4);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_6, 5);
lean::inc(x_85);
lean::dec(x_6);
x_88 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_88, 0, x_55);
lean::cnstr_set(x_88, 1, x_71);
lean::cnstr_set(x_88, 2, x_72);
lean::cnstr_set(x_88, 3, x_82);
lean::cnstr_set(x_88, 4, x_83);
lean::cnstr_set(x_88, 5, x_85);
x_89 = lean::apply_1(x_52, x_88);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
}
else
{
obj* x_92; obj* x_95; obj* x_96; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_92 = lean::cnstr_get(x_7, 0);
lean::inc(x_92);
lean::dec(x_7);
x_95 = l_lean_parser_term_match_has__view;
x_96 = lean::cnstr_get(x_95, 1);
lean::inc(x_96);
lean::dec(x_95);
x_99 = lean::box(0);
x_100 = lean::cnstr_get(x_6, 3);
lean::inc(x_100);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_99);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_92);
lean::cnstr_set(x_104, 1, x_99);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_99);
x_106 = lean::cnstr_get(x_6, 5);
lean::inc(x_106);
lean::dec(x_6);
x_109 = l_lean_expander_mixfix_transform___closed__4;
x_110 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_110, 0, x_105);
lean::cnstr_set(x_110, 1, x_109);
lean::cnstr_set(x_110, 2, x_106);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_99);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_99);
x_113 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_114 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
x_115 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_103);
lean::cnstr_set(x_115, 2, x_99);
lean::cnstr_set(x_115, 3, x_114);
lean::cnstr_set(x_115, 4, x_99);
lean::cnstr_set(x_115, 5, x_112);
x_116 = lean::apply_1(x_96, x_115);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
return x_118;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_constant_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 2);
lean::inc(x_7);
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
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
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
lean::inc(x_26);
x_28 = lean::cnstr_get(x_6, 1);
lean::inc(x_28);
lean::dec(x_6);
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
x_46 = lean::alloc_cnstr(0, 3, 0);
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
obj* x_54; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_54 = l_lean_expander_no__expansion___closed__1;
return x_54;
}
}
}
obj* _init_l_lean_expander_declaration_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@[");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::mk_string("]");
x_6 = l_string_trim(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::mk_string("class");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string(".");
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_3, x_2);
x_6 = l_lean_parser_substring_of__string(x_5);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_0);
lean::cnstr_set(x_7, 4, x_0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
return x_9;
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; 
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
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
x_18 = lean::cnstr_get(x_9, 3);
x_20 = lean::cnstr_get(x_9, 4);
x_22 = lean::cnstr_get(x_9, 5);
x_24 = lean::cnstr_get(x_9, 6);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 lean::cnstr_set(x_9, 3, lean::box(0));
 lean::cnstr_set(x_9, 4, lean::box(0));
 lean::cnstr_set(x_9, 5, lean::box(0));
 lean::cnstr_set(x_9, 6, lean::box(0));
 x_26 = x_9;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_36; 
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_6);
lean::dec(x_26);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_11);
lean::dec(x_14);
lean::dec(x_16);
x_36 = l_lean_expander_no__expansion___closed__1;
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_37 = x_12;
} else {
 lean::dec(x_12);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
lean::dec(x_6);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::box(0);
x_44 = l_lean_expander_declaration_transform___closed__1;
x_45 = l_option_get__or__else___main___rarg(x_41, x_44);
x_46 = lean::cnstr_get(x_3, 1);
lean::inc(x_46);
lean::dec(x_3);
x_49 = lean::cnstr_get(x_38, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_45, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_45, 1);
lean::inc(x_53);
x_55 = l_lean_expander_declaration_transform___closed__2;
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
x_57 = lean::cnstr_get(x_45, 2);
lean::inc(x_57);
lean::dec(x_45);
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_51);
lean::cnstr_set(x_60, 1, x_56);
lean::cnstr_set(x_60, 2, x_57);
if (lean::is_scalar(x_37)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_37;
}
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::cnstr_get(x_38, 2);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_38, 4);
lean::inc(x_66);
lean::dec(x_38);
x_69 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_69, 0, x_49);
lean::cnstr_set(x_69, 1, x_61);
lean::cnstr_set(x_69, 2, x_62);
lean::cnstr_set(x_69, 3, x_64);
lean::cnstr_set(x_69, 4, x_66);
if (lean::is_scalar(x_26)) {
 x_70 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_70 = x_26;
}
lean::cnstr_set(x_70, 0, x_43);
lean::cnstr_set(x_70, 1, x_14);
lean::cnstr_set(x_70, 2, x_16);
lean::cnstr_set(x_70, 3, x_18);
lean::cnstr_set(x_70, 4, x_20);
lean::cnstr_set(x_70, 5, x_22);
lean::cnstr_set(x_70, 6, x_24);
if (lean::is_scalar(x_11)) {
 x_71 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_71 = x_11;
}
lean::cnstr_set(x_71, 0, x_70);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_71);
x_73 = lean::apply_1(x_46, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
case 5:
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; 
x_76 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_78 = x_7;
} else {
 lean::inc(x_76);
 lean::dec(x_7);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_76, 0);
x_81 = lean::cnstr_get(x_76, 1);
x_83 = lean::cnstr_get(x_76, 2);
x_85 = lean::cnstr_get(x_76, 3);
x_87 = lean::cnstr_get(x_76, 4);
x_89 = lean::cnstr_get(x_76, 5);
x_91 = lean::cnstr_get(x_76, 6);
x_93 = lean::cnstr_get(x_76, 7);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_set(x_76, 0, lean::box(0));
 lean::cnstr_set(x_76, 1, lean::box(0));
 lean::cnstr_set(x_76, 2, lean::box(0));
 lean::cnstr_set(x_76, 3, lean::box(0));
 lean::cnstr_set(x_76, 4, lean::box(0));
 lean::cnstr_set(x_76, 5, lean::box(0));
 lean::cnstr_set(x_76, 6, lean::box(0));
 lean::cnstr_set(x_76, 7, lean::box(0));
 x_95 = x_76;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_76);
 x_95 = lean::box(0);
}
if (lean::obj_tag(x_79) == 0)
{
obj* x_107; 
lean::dec(x_6);
lean::dec(x_79);
lean::dec(x_93);
lean::dec(x_91);
lean::dec(x_78);
lean::dec(x_89);
lean::dec(x_81);
lean::dec(x_95);
lean::dec(x_85);
lean::dec(x_83);
lean::dec(x_87);
x_107 = l_lean_expander_no__expansion___closed__1;
return x_107;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; obj* x_116; obj* x_119; obj* x_121; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_130; obj* x_131; obj* x_132; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_79);
x_109 = lean::cnstr_get(x_6, 0);
lean::inc(x_109);
lean::dec(x_6);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
x_114 = l_lean_expander_declaration_transform___closed__1;
x_115 = l_option_get__or__else___main___rarg(x_112, x_114);
x_116 = lean::cnstr_get(x_3, 1);
lean::inc(x_116);
lean::dec(x_3);
x_119 = lean::cnstr_get(x_109, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_115, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_115, 1);
lean::inc(x_123);
x_125 = l_lean_expander_declaration_transform___closed__2;
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_123);
x_127 = lean::cnstr_get(x_115, 2);
lean::inc(x_127);
lean::dec(x_115);
x_130 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_130, 0, x_121);
lean::cnstr_set(x_130, 1, x_126);
lean::cnstr_set(x_130, 2, x_127);
x_131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
x_132 = lean::cnstr_get(x_109, 2);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_109, 3);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_109, 4);
lean::inc(x_136);
lean::dec(x_109);
x_139 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_139, 0, x_119);
lean::cnstr_set(x_139, 1, x_131);
lean::cnstr_set(x_139, 2, x_132);
lean::cnstr_set(x_139, 3, x_134);
lean::cnstr_set(x_139, 4, x_136);
x_140 = l_lean_expander_declaration_transform___closed__3;
if (lean::is_scalar(x_95)) {
 x_141 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_141 = x_95;
}
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_81);
lean::cnstr_set(x_141, 2, x_83);
lean::cnstr_set(x_141, 3, x_85);
lean::cnstr_set(x_141, 4, x_87);
lean::cnstr_set(x_141, 5, x_89);
lean::cnstr_set(x_141, 6, x_91);
lean::cnstr_set(x_141, 7, x_93);
if (lean::is_scalar(x_78)) {
 x_142 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_142 = x_78;
}
lean::cnstr_set(x_142, 0, x_141);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_139);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::apply_1(x_116, x_143);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
x_146 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_146, 0, x_145);
return x_146;
}
}
default:
{
obj* x_149; 
lean::dec(x_7);
lean::dec(x_6);
x_149 = l_lean_expander_no__expansion___closed__1;
return x_149;
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_intro__rule_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
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
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_20; 
lean::dec(x_13);
lean::dec(x_14);
lean::dec(x_6);
x_20 = l_lean_expander_no__expansion___closed__1;
return x_20;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_21 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_23 = x_11;
} else {
 lean::inc(x_21);
 lean::dec(x_11);
 x_23 = lean::box(0);
}
x_24 = lean::box(0);
x_25 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_14);
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
obj* x_64; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_64 = l_lean_expander_no__expansion___closed__1;
return x_64;
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
x_17 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_19 = x_11;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_25; 
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_13);
lean::dec(x_19);
lean::inc(x_1);
x_25 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
x_9 = x_25;
goto lbl_10;
}
else
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_35; 
x_26 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_28 = x_15;
} else {
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
x_33 = lean::cnstr_get(x_26, 2);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_set(x_26, 0, lean::box(0));
 lean::cnstr_set(x_26, 1, lean::box(0));
 lean::cnstr_set(x_26, 2, lean::box(0));
 x_35 = x_26;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_26);
 x_35 = lean::box(0);
}
if (lean::obj_tag(x_31) == 0)
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_4);
x_37 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
if (lean::is_scalar(x_35)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_35;
}
lean::cnstr_set(x_38, 0, x_29);
lean::cnstr_set(x_38, 1, x_37);
lean::cnstr_set(x_38, 2, x_33);
if (lean::is_scalar(x_28)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_28;
}
lean::cnstr_set(x_39, 0, x_38);
if (lean::is_scalar(x_19)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_19;
}
lean::cnstr_set(x_40, 0, x_13);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set(x_40, 2, x_17);
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::inc(x_1);
x_43 = l_lean_expander_expand__bracketed__binder___main(x_41, x_1);
x_9 = x_43;
goto lbl_10;
}
else
{
obj* x_52; 
lean::dec(x_17);
lean::dec(x_13);
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_28);
lean::dec(x_29);
lean::dec(x_19);
lean::inc(x_1);
x_52 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
x_9 = x_52;
goto lbl_10;
}
}
else
{
obj* x_62; 
lean::dec(x_17);
lean::dec(x_13);
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_28);
lean::dec(x_29);
lean::dec(x_19);
lean::inc(x_1);
x_62 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
x_9 = x_62;
goto lbl_10;
}
}
}
default:
{
obj* x_64; 
lean::inc(x_1);
x_64 = l_lean_expander_expand__bracketed__binder___main(x_4, x_1);
x_9 = x_64;
goto lbl_10;
}
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_1);
x_68 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_70 = x_9;
} else {
 lean::inc(x_68);
 lean::dec(x_9);
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
obj* x_72; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_74 = x_9;
} else {
 lean::inc(x_72);
 lean::dec(x_9);
 x_74 = lean::box(0);
}
x_75 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_75) == 0)
{
obj* x_78; obj* x_81; 
lean::dec(x_8);
lean::dec(x_72);
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
lean::dec(x_75);
if (lean::is_scalar(x_74)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_74;
 lean::cnstr_set_tag(x_74, 0);
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
lean::dec(x_75);
if (lean::is_scalar(x_8)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_8;
}
lean::cnstr_set(x_85, 0, x_72);
lean::cnstr_set(x_85, 1, x_82);
if (lean::is_scalar(x_74)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_74;
}
lean::cnstr_set(x_86, 0, x_85);
return x_86;
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
 lean::cnstr_set(x_12, 0, lean::box(0));
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
 lean::cnstr_set(x_12, 0, lean::box(0));
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
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_0 = lean::box(0);
x_1 = lean::mk_string("sorry_ax");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
x_4 = l_lean_parser_term_hole_has__view;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::mk_string("_");
x_9 = l_string_trim(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::apply_1(x_5, x_11);
x_13 = lean::mk_string("bool");
x_14 = lean_name_mk_string(x_0, x_13);
x_15 = lean::mk_string("ff");
x_16 = lean_name_mk_string(x_14, x_15);
x_17 = l_lean_expander_glob__id(x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_3, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
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
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get(x_0, 2);
x_10 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_19; uint8 x_20; 
lean::inc(x_1);
lean::inc(x_6);
x_19 = l_lean_name_quick__lt___main(x_6, x_1);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_23 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_23 = x_12;
}
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_2);
lean::cnstr_set(x_23, 3, x_10);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_6);
lean::cnstr_set(x_25, 2, x_8);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_10);
return x_27;
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; uint8 x_40; 
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
lean::inc(x_30);
lean::inc(x_1);
x_39 = l_lean_name_quick__lt___main(x_1, x_30);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_43; uint8 x_44; 
lean::inc(x_1);
lean::inc(x_30);
x_43 = l_lean_name_quick__lt___main(x_30, x_1);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_47; 
lean::dec(x_30);
lean::dec(x_32);
if (lean::is_scalar(x_36)) {
 x_47 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_47 = x_36;
}
lean::cnstr_set(x_47, 0, x_28);
lean::cnstr_set(x_47, 1, x_1);
lean::cnstr_set(x_47, 2, x_2);
lean::cnstr_set(x_47, 3, x_34);
return x_47;
}
else
{
uint8 x_49; 
lean::inc(x_34);
x_49 = l_rbnode_get__color___main___rarg(x_34);
if (x_49 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_36);
x_51 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_28);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_53);
return x_54;
}
}
}
else
{
uint8 x_56; 
lean::inc(x_28);
x_56 = l_rbnode_get__color___main___rarg(x_28);
if (x_56 == 0)
{
obj* x_58; obj* x_59; 
lean::dec(x_36);
x_58 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_61 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_61 = x_36;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_30);
lean::cnstr_set(x_61, 2, x_32);
lean::cnstr_set(x_61, 3, x_34);
return x_61;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
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
x_77 = l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(x_57, x_76);
return x_77;
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
 lean::cnstr_set(x_16, 0, lean::box(0));
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_27 = x_16;
} else {
 lean::inc(x_25);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
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
x_33 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(x_0, x_11, x_30, x_3);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_13);
lean::dec(x_28);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
lean::inc(x_41);
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_13)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_13;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_32)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_32;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_27)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_27;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
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
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
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
 lean::cnstr_set(x_16, 0, lean::box(0));
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
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_27 = x_16;
} else {
 lean::inc(x_25);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
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
x_33 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_0, x_11, x_30, x_3);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_13);
lean::dec(x_28);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_40, 0, x_37);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_33, 0);
lean::inc(x_41);
lean::dec(x_33);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
if (lean::is_scalar(x_13)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_13;
}
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_44);
if (lean::is_scalar(x_32)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_32;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
if (lean::is_scalar(x_27)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_27;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
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
 lean::cnstr_set(x_28, 0, lean::box(0));
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
 lean::cnstr_set(x_28, 0, lean::box(0));
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_34, 0);
x_39 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_set(x_34, 0, lean::box(0));
 lean::cnstr_set(x_34, 1, lean::box(0));
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
 lean::cnstr_set(x_49, 0, lean::box(0));
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
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_59 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_set(x_49, 0, lean::box(0));
 x_61 = x_49;
} else {
 lean::inc(x_59);
 lean::dec(x_49);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 0);
x_64 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_set(x_59, 0, lean::box(0));
 lean::cnstr_set(x_59, 1, lean::box(0));
 x_66 = x_59;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_59);
 x_66 = lean::box(0);
}
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
obj* x_85; obj* x_88; 
lean::dec(x_3);
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_66);
lean::dec(x_67);
lean::dec(x_17);
lean::dec(x_21);
x_85 = lean::cnstr_get(x_77, 0);
lean::inc(x_85);
lean::dec(x_77);
if (lean::is_scalar(x_61)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_61;
 lean::cnstr_set_tag(x_61, 0);
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_89; 
x_89 = lean::cnstr_get(x_77, 0);
lean::inc(x_89);
lean::dec(x_77);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; 
lean::dec(x_62);
x_93 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_17, x_67, x_64, x_3);
if (lean::obj_tag(x_93) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_66);
lean::dec(x_21);
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
lean::dec(x_93);
if (lean::is_scalar(x_61)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_61;
 lean::cnstr_set_tag(x_61, 0);
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_100; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_93, 0);
lean::inc(x_100);
lean::dec(x_93);
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
x_108 = l_lean_parser_syntax_mk__node(x_21, x_103);
if (lean::is_scalar(x_66)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_66;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
if (lean::is_scalar(x_61)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_61;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
else
{
obj* x_115; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_61);
lean::dec(x_66);
lean::dec(x_67);
lean::dec(x_21);
x_115 = lean::cnstr_get(x_89, 0);
lean::inc(x_115);
lean::dec(x_89);
x_118 = lean::box(0);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_62);
lean::cnstr_set(x_119, 1, x_118);
x_120 = l_lean_parser_syntax_flip__scopes___main(x_119, x_115);
x_0 = x_17;
x_1 = x_120;
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
obj* x_123; obj* x_124; 
lean::dec(x_0);
x_123 = l___private_init_lean_expander_2__expand__core___main___closed__1;
x_124 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_1, x_123, x_2, x_3);
return x_124;
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
 lean::cnstr_set(x_4, 0, lean::box(0));
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
 lean::cnstr_set(x_4, 0, lean::box(0));
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
