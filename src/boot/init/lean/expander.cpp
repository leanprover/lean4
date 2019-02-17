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
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_transformer() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
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
lean::inc(x_2);
return x_2;
}
}
obj* l_lean_expander_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
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
lean::inc(x_20);
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_18);
lean::cnstr_set(x_22, 3, x_20);
lean::cnstr_set(x_22, 4, x_3);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_19);
x_23 = x_22;
x_24 = lean::apply_2(x_5, lean::box(0), x_23);
return x_24;
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
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_9; 
x_1 = lean::box(0);
x_2 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_2, x_0);
x_6 = l_lean_parser_substring_of__string(x_5);
lean::inc(x_1);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_0);
lean::cnstr_set(x_9, 3, x_1);
lean::cnstr_set(x_9, 4, x_1);
return x_9;
}
}
obj* l_lean_expander_glob__id(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::box(0);
x_5 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
lean::inc(x_5);
x_8 = l_lean_name_to__string__with__sep___main(x_5, x_0);
x_9 = l_lean_parser_substring_of__string(x_8);
lean::inc(x_4);
lean::inc(x_0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_4);
lean::inc(x_4);
lean::inc(x_4);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_9);
lean::cnstr_set(x_15, 2, x_0);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set(x_15, 4, x_4);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_4);
x_17 = lean::apply_1(x_2, x_16);
return x_17;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_9 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_7);
lean::cnstr_set(x_12, 2, x_9);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
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
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_13);
lean::cnstr_set(x_18, 2, x_14);
lean::cnstr_set(x_18, 3, x_16);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_15);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
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
obj* x_4; obj* x_6; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_6);
x_8 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_4, x_6, x_0, x_1);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 3);
lean::inc(x_19);
lean::dec(x_0);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_15);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_17);
lean::cnstr_set(x_22, 3, x_19);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_10);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
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
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_14);
lean::cnstr_set(x_16, 4, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*5, x_13);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
}
x_18 = lean::cnstr_get(x_9, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_27; 
x_23 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_23);
lean::inc(x_0);
x_27 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_23, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 x_35 = x_27;
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
obj* x_37; 
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
lean::dec(x_27);
x_14 = x_37;
goto lbl_15;
}
}
else
{
obj* x_43; 
lean::dec(x_13);
lean::dec(x_20);
lean::inc(x_3);
x_43 = l___private_init_lean_expander_1__pop__stx__arg(x_2, x_3);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 x_50 = x_43;
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
obj* x_52; 
x_52 = lean::cnstr_get(x_43, 0);
lean::inc(x_52);
lean::dec(x_43);
x_16 = x_52;
goto lbl_17;
}
}
lbl_15:
{
obj* x_55; obj* x_57; obj* x_58; 
x_55 = lean::cnstr_get(x_14, 1);
lean::inc(x_55);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_57 = x_14;
}
x_58 = lean::cnstr_get(x_9, 1);
lean::inc(x_58);
lean::dec(x_9);
if (lean::obj_tag(x_58) == 0)
{
lean::dec(x_13);
lean::dec(x_57);
x_1 = x_11;
x_2 = x_55;
goto _start;
}
else
{
obj* x_64; obj* x_66; 
x_64 = lean::cnstr_get(x_58, 0);
lean::inc(x_64);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_66 = x_58;
}
switch (lean::obj_tag(x_64)) {
case 0:
{
obj* x_70; 
lean::dec(x_64);
lean::dec(x_57);
lean::inc(x_3);
x_70 = l___private_init_lean_expander_1__pop__stx__arg(x_55, x_3);
if (lean::obj_tag(x_70) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_66);
x_76 = lean::cnstr_get(x_70, 0);
lean::inc(x_76);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_78 = x_70;
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
obj* x_80; obj* x_83; obj* x_85; obj* x_88; obj* x_90; obj* x_92; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
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
x_98 = lean::apply_1(x_96, x_83);
x_99 = lean::box(0);
lean::inc(x_99);
if (lean::is_scalar(x_13)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_13;
}
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_99);
x_103 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
if (lean::is_scalar(x_66)) {
 x_104 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_104 = x_66;
}
lean::cnstr_set(x_104, 0, x_103);
x_105 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_105, 0, x_88);
lean::cnstr_set(x_105, 1, x_90);
lean::cnstr_set(x_105, 2, x_92);
lean::cnstr_set(x_105, 3, x_104);
x_1 = x_11;
x_2 = x_105;
goto _start;
}
}
case 1:
{
obj* x_111; 
lean::dec(x_13);
lean::dec(x_64);
lean::dec(x_57);
lean::inc(x_3);
x_111 = l___private_init_lean_expander_1__pop__stx__arg(x_55, x_3);
if (lean::obj_tag(x_111) == 0)
{
obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_66);
x_116 = lean::cnstr_get(x_111, 0);
lean::inc(x_116);
if (lean::is_shared(x_111)) {
 lean::dec(x_111);
 x_118 = lean::box(0);
} else {
 lean::cnstr_release(x_111, 0);
 x_118 = x_111;
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
return x_119;
}
else
{
obj* x_120; obj* x_123; obj* x_125; obj* x_128; obj* x_130; obj* x_132; obj* x_135; obj* x_136; obj* x_138; obj* x_139; obj* x_140; 
x_120 = lean::cnstr_get(x_111, 0);
lean::inc(x_120);
lean::dec(x_111);
x_123 = lean::cnstr_get(x_120, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_120, 1);
lean::inc(x_125);
lean::dec(x_120);
x_128 = lean::cnstr_get(x_125, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_125, 1);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_125, 2);
lean::inc(x_132);
lean::dec(x_125);
x_135 = l_lean_parser_term_binders_has__view;
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::apply_1(x_136, x_123);
if (lean::is_scalar(x_66)) {
 x_139 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_139 = x_66;
}
lean::cnstr_set(x_139, 0, x_138);
x_140 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_140, 0, x_128);
lean::cnstr_set(x_140, 1, x_130);
lean::cnstr_set(x_140, 2, x_132);
lean::cnstr_set(x_140, 3, x_139);
x_1 = x_11;
x_2 = x_140;
goto _start;
}
}
default:
{
obj* x_143; obj* x_146; obj* x_148; 
lean::dec(x_66);
x_143 = lean::cnstr_get(x_64, 0);
lean::inc(x_143);
lean::dec(x_64);
x_146 = lean::cnstr_get(x_143, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_143, 1);
lean::inc(x_148);
lean::dec(x_143);
if (lean::obj_tag(x_148) == 0)
{
obj* x_152; 
lean::inc(x_3);
x_152 = l___private_init_lean_expander_1__pop__stx__arg(x_55, x_3);
if (lean::obj_tag(x_152) == 0)
{
obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_57);
x_159 = lean::cnstr_get(x_152, 0);
lean::inc(x_159);
if (lean::is_shared(x_152)) {
 lean::dec(x_152);
 x_161 = lean::box(0);
} else {
 lean::cnstr_release(x_152, 0);
 x_161 = x_152;
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
if (lean::is_scalar(x_57)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_57;
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
x_192 = l___private_init_lean_expander_1__pop__stx__arg(x_55, x_3);
if (lean::obj_tag(x_192) == 0)
{
obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_57);
x_199 = lean::cnstr_get(x_192, 0);
lean::inc(x_199);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_201 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 x_201 = x_192;
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
if (lean::is_scalar(x_57)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_57;
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
x_228 = l___private_init_lean_expander_1__pop__stx__arg(x_55, x_3);
if (lean::obj_tag(x_228) == 0)
{
obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_146);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_224);
lean::dec(x_57);
x_236 = lean::cnstr_get(x_228, 0);
lean::inc(x_236);
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_238 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_238 = x_228;
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
lean::inc(x_240);
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_242 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_242 = x_228;
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
obj* x_264; obj* x_268; 
lean::dec(x_146);
lean::dec(x_13);
lean::dec(x_248);
lean::dec(x_243);
lean::dec(x_250);
lean::dec(x_252);
lean::dec(x_224);
lean::dec(x_57);
x_264 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_264);
lean::inc(x_0);
x_268 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_264, x_245, x_3);
if (lean::obj_tag(x_268) == 0)
{
obj* x_272; obj* x_275; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_272 = lean::cnstr_get(x_268, 0);
lean::inc(x_272);
lean::dec(x_268);
if (lean::is_scalar(x_242)) {
 x_275 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_275 = x_242;
 lean::cnstr_set_tag(x_242, 0);
}
lean::cnstr_set(x_275, 0, x_272);
return x_275;
}
else
{
obj* x_277; obj* x_280; 
lean::dec(x_242);
x_277 = lean::cnstr_get(x_268, 0);
lean::inc(x_277);
lean::dec(x_268);
x_280 = lean::cnstr_get(x_277, 1);
lean::inc(x_280);
lean::dec(x_277);
x_1 = x_11;
x_2 = x_280;
goto _start;
}
}
else
{
obj* x_286; obj* x_288; obj* x_289; obj* x_291; obj* x_292; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_302; obj* x_303; obj* x_306; obj* x_308; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
lean::dec(x_245);
lean::dec(x_242);
x_286 = lean::cnstr_get(x_254, 0);
lean::inc(x_286);
x_288 = l_lean_parser_term_lambda_has__view;
x_289 = lean::cnstr_get(x_288, 1);
lean::inc(x_289);
x_291 = lean::box(0);
x_292 = lean::cnstr_get(x_224, 3);
lean::inc(x_292);
lean::inc(x_291);
if (lean::is_scalar(x_13)) {
 x_295 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_295 = x_13;
}
lean::cnstr_set(x_295, 0, x_292);
lean::cnstr_set(x_295, 1, x_291);
x_296 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_295);
x_297 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_291);
x_298 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_298, 0, x_297);
x_299 = lean::cnstr_get(x_224, 5);
lean::inc(x_299);
lean::dec(x_224);
x_302 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_303 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_303);
lean::inc(x_302);
x_306 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_306, 0, x_302);
lean::cnstr_set(x_306, 1, x_298);
lean::cnstr_set(x_306, 2, x_303);
lean::cnstr_set(x_306, 3, x_299);
lean::inc(x_289);
x_308 = lean::apply_1(x_289, x_306);
lean::inc(x_303);
lean::inc(x_302);
x_311 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_311, 0, x_302);
lean::cnstr_set(x_311, 1, x_286);
lean::cnstr_set(x_311, 2, x_303);
lean::cnstr_set(x_311, 3, x_243);
x_312 = lean::apply_1(x_289, x_311);
x_313 = l_lean_parser_term_app_has__view;
x_314 = lean::cnstr_get(x_313, 1);
lean::inc(x_314);
x_316 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_316, 0, x_308);
lean::cnstr_set(x_316, 1, x_312);
x_317 = lean::apply_1(x_314, x_316);
if (lean::is_scalar(x_57)) {
 x_318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_318 = x_57;
}
lean::cnstr_set(x_318, 0, x_146);
lean::cnstr_set(x_318, 1, x_317);
x_319 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_319, 0, x_318);
lean::cnstr_set(x_319, 1, x_252);
x_320 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_320, 0, x_248);
lean::cnstr_set(x_320, 1, x_250);
lean::cnstr_set(x_320, 2, x_319);
lean::cnstr_set(x_320, 3, x_254);
x_1 = x_11;
x_2 = x_320;
goto _start;
}
}
}
default:
{
obj* x_326; obj* x_330; 
lean::dec(x_146);
lean::dec(x_187);
lean::dec(x_13);
lean::dec(x_57);
x_326 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_326);
lean::inc(x_0);
x_330 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_326, x_55, x_3);
if (lean::obj_tag(x_330) == 0)
{
obj* x_334; obj* x_336; obj* x_337; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_334 = lean::cnstr_get(x_330, 0);
lean::inc(x_334);
if (lean::is_shared(x_330)) {
 lean::dec(x_330);
 x_336 = lean::box(0);
} else {
 lean::cnstr_release(x_330, 0);
 x_336 = x_330;
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
x_338 = lean::cnstr_get(x_330, 0);
lean::inc(x_338);
lean::dec(x_330);
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
lean::dec(x_338);
x_1 = x_11;
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
lbl_17:
{
obj* x_345; obj* x_347; obj* x_348; 
x_345 = lean::cnstr_get(x_16, 1);
lean::inc(x_345);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_347 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_347 = x_16;
}
x_348 = lean::cnstr_get(x_9, 1);
lean::inc(x_348);
lean::dec(x_9);
if (lean::obj_tag(x_348) == 0)
{
lean::dec(x_347);
x_1 = x_11;
x_2 = x_345;
goto _start;
}
else
{
obj* x_353; obj* x_355; 
x_353 = lean::cnstr_get(x_348, 0);
lean::inc(x_353);
if (lean::is_shared(x_348)) {
 lean::dec(x_348);
 x_355 = lean::box(0);
} else {
 lean::cnstr_release(x_348, 0);
 x_355 = x_348;
}
switch (lean::obj_tag(x_353)) {
case 0:
{
obj* x_359; 
lean::dec(x_347);
lean::dec(x_353);
lean::inc(x_3);
x_359 = l___private_init_lean_expander_1__pop__stx__arg(x_345, x_3);
if (lean::obj_tag(x_359) == 0)
{
obj* x_364; obj* x_366; obj* x_367; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_355);
x_364 = lean::cnstr_get(x_359, 0);
lean::inc(x_364);
if (lean::is_shared(x_359)) {
 lean::dec(x_359);
 x_366 = lean::box(0);
} else {
 lean::cnstr_release(x_359, 0);
 x_366 = x_359;
}
if (lean::is_scalar(x_366)) {
 x_367 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_367 = x_366;
}
lean::cnstr_set(x_367, 0, x_364);
return x_367;
}
else
{
obj* x_368; obj* x_371; obj* x_373; obj* x_376; obj* x_378; obj* x_380; obj* x_383; obj* x_384; obj* x_386; obj* x_387; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; 
x_368 = lean::cnstr_get(x_359, 0);
lean::inc(x_368);
lean::dec(x_359);
x_371 = lean::cnstr_get(x_368, 0);
lean::inc(x_371);
x_373 = lean::cnstr_get(x_368, 1);
lean::inc(x_373);
lean::dec(x_368);
x_376 = lean::cnstr_get(x_373, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_373, 1);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_373, 2);
lean::inc(x_380);
lean::dec(x_373);
x_383 = l_lean_parser_term_binder__ident_has__view;
x_384 = lean::cnstr_get(x_383, 0);
lean::inc(x_384);
x_386 = lean::apply_1(x_384, x_371);
x_387 = lean::box(0);
lean::inc(x_387);
x_389 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_389, 0, x_386);
lean::cnstr_set(x_389, 1, x_387);
x_390 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_390, 0, x_389);
lean::cnstr_set(x_390, 1, x_387);
x_391 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_391, 0, x_390);
if (lean::is_scalar(x_355)) {
 x_392 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_392 = x_355;
}
lean::cnstr_set(x_392, 0, x_391);
x_393 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_393, 0, x_376);
lean::cnstr_set(x_393, 1, x_378);
lean::cnstr_set(x_393, 2, x_380);
lean::cnstr_set(x_393, 3, x_392);
x_1 = x_11;
x_2 = x_393;
goto _start;
}
}
case 1:
{
obj* x_398; 
lean::dec(x_347);
lean::dec(x_353);
lean::inc(x_3);
x_398 = l___private_init_lean_expander_1__pop__stx__arg(x_345, x_3);
if (lean::obj_tag(x_398) == 0)
{
obj* x_403; obj* x_405; obj* x_406; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_355);
x_403 = lean::cnstr_get(x_398, 0);
lean::inc(x_403);
if (lean::is_shared(x_398)) {
 lean::dec(x_398);
 x_405 = lean::box(0);
} else {
 lean::cnstr_release(x_398, 0);
 x_405 = x_398;
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
obj* x_407; obj* x_410; obj* x_412; obj* x_415; obj* x_417; obj* x_419; obj* x_422; obj* x_423; obj* x_425; obj* x_426; obj* x_427; 
x_407 = lean::cnstr_get(x_398, 0);
lean::inc(x_407);
lean::dec(x_398);
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
x_425 = lean::apply_1(x_423, x_410);
if (lean::is_scalar(x_355)) {
 x_426 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_426 = x_355;
}
lean::cnstr_set(x_426, 0, x_425);
x_427 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_427, 0, x_415);
lean::cnstr_set(x_427, 1, x_417);
lean::cnstr_set(x_427, 2, x_419);
lean::cnstr_set(x_427, 3, x_426);
x_1 = x_11;
x_2 = x_427;
goto _start;
}
}
default:
{
obj* x_430; obj* x_433; obj* x_435; 
lean::dec(x_355);
x_430 = lean::cnstr_get(x_353, 0);
lean::inc(x_430);
lean::dec(x_353);
x_433 = lean::cnstr_get(x_430, 0);
lean::inc(x_433);
x_435 = lean::cnstr_get(x_430, 1);
lean::inc(x_435);
lean::dec(x_430);
if (lean::obj_tag(x_435) == 0)
{
obj* x_439; 
lean::inc(x_3);
x_439 = l___private_init_lean_expander_1__pop__stx__arg(x_345, x_3);
if (lean::obj_tag(x_439) == 0)
{
obj* x_445; obj* x_447; obj* x_448; 
lean::dec(x_433);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_347);
x_445 = lean::cnstr_get(x_439, 0);
lean::inc(x_445);
if (lean::is_shared(x_439)) {
 lean::dec(x_439);
 x_447 = lean::box(0);
} else {
 lean::cnstr_release(x_439, 0);
 x_447 = x_439;
}
if (lean::is_scalar(x_447)) {
 x_448 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_448 = x_447;
}
lean::cnstr_set(x_448, 0, x_445);
return x_448;
}
else
{
obj* x_449; obj* x_452; obj* x_454; obj* x_457; obj* x_459; obj* x_461; obj* x_462; obj* x_464; obj* x_465; obj* x_468; 
x_449 = lean::cnstr_get(x_439, 0);
lean::inc(x_449);
lean::dec(x_439);
x_452 = lean::cnstr_get(x_449, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get(x_449, 1);
lean::inc(x_454);
lean::dec(x_449);
x_457 = lean::cnstr_get(x_454, 0);
lean::inc(x_457);
x_459 = lean::cnstr_get(x_454, 1);
lean::inc(x_459);
if (lean::is_scalar(x_347)) {
 x_461 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_461 = x_347;
}
lean::cnstr_set(x_461, 0, x_433);
lean::cnstr_set(x_461, 1, x_452);
x_462 = lean::cnstr_get(x_454, 2);
lean::inc(x_462);
x_464 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_464, 0, x_461);
lean::cnstr_set(x_464, 1, x_462);
x_465 = lean::cnstr_get(x_454, 3);
lean::inc(x_465);
lean::dec(x_454);
x_468 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_468, 0, x_457);
lean::cnstr_set(x_468, 1, x_459);
lean::cnstr_set(x_468, 2, x_464);
lean::cnstr_set(x_468, 3, x_465);
x_1 = x_11;
x_2 = x_468;
goto _start;
}
}
else
{
obj* x_470; obj* x_473; 
x_470 = lean::cnstr_get(x_435, 0);
lean::inc(x_470);
lean::dec(x_435);
x_473 = lean::cnstr_get(x_470, 1);
lean::inc(x_473);
lean::dec(x_470);
switch (lean::obj_tag(x_473)) {
case 0:
{
obj* x_478; 
lean::dec(x_473);
lean::inc(x_3);
x_478 = l___private_init_lean_expander_1__pop__stx__arg(x_345, x_3);
if (lean::obj_tag(x_478) == 0)
{
obj* x_484; obj* x_486; obj* x_487; 
lean::dec(x_433);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_347);
x_484 = lean::cnstr_get(x_478, 0);
lean::inc(x_484);
if (lean::is_shared(x_478)) {
 lean::dec(x_478);
 x_486 = lean::box(0);
} else {
 lean::cnstr_release(x_478, 0);
 x_486 = x_478;
}
if (lean::is_scalar(x_486)) {
 x_487 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_487 = x_486;
}
lean::cnstr_set(x_487, 0, x_484);
return x_487;
}
else
{
obj* x_488; obj* x_491; obj* x_493; obj* x_496; obj* x_498; obj* x_500; obj* x_501; obj* x_503; obj* x_504; obj* x_507; 
x_488 = lean::cnstr_get(x_478, 0);
lean::inc(x_488);
lean::dec(x_478);
x_491 = lean::cnstr_get(x_488, 0);
lean::inc(x_491);
x_493 = lean::cnstr_get(x_488, 1);
lean::inc(x_493);
lean::dec(x_488);
x_496 = lean::cnstr_get(x_493, 0);
lean::inc(x_496);
x_498 = lean::cnstr_get(x_493, 1);
lean::inc(x_498);
if (lean::is_scalar(x_347)) {
 x_500 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_500 = x_347;
}
lean::cnstr_set(x_500, 0, x_433);
lean::cnstr_set(x_500, 1, x_491);
x_501 = lean::cnstr_get(x_493, 2);
lean::inc(x_501);
x_503 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_503, 0, x_500);
lean::cnstr_set(x_503, 1, x_501);
x_504 = lean::cnstr_get(x_493, 3);
lean::inc(x_504);
lean::dec(x_493);
x_507 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_507, 0, x_496);
lean::cnstr_set(x_507, 1, x_498);
lean::cnstr_set(x_507, 2, x_503);
lean::cnstr_set(x_507, 3, x_504);
x_1 = x_11;
x_2 = x_507;
goto _start;
}
}
case 2:
{
obj* x_509; obj* x_513; 
x_509 = lean::cnstr_get(x_473, 0);
lean::inc(x_509);
lean::dec(x_473);
lean::inc(x_3);
x_513 = l___private_init_lean_expander_1__pop__stx__arg(x_345, x_3);
if (lean::obj_tag(x_513) == 0)
{
obj* x_520; obj* x_522; obj* x_523; 
lean::dec(x_433);
lean::dec(x_509);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_347);
x_520 = lean::cnstr_get(x_513, 0);
lean::inc(x_520);
if (lean::is_shared(x_513)) {
 lean::dec(x_513);
 x_522 = lean::box(0);
} else {
 lean::cnstr_release(x_513, 0);
 x_522 = x_513;
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
obj* x_524; obj* x_526; obj* x_527; obj* x_529; obj* x_532; obj* x_534; obj* x_536; obj* x_538; 
x_524 = lean::cnstr_get(x_513, 0);
lean::inc(x_524);
if (lean::is_shared(x_513)) {
 lean::dec(x_513);
 x_526 = lean::box(0);
} else {
 lean::cnstr_release(x_513, 0);
 x_526 = x_513;
}
x_527 = lean::cnstr_get(x_524, 0);
lean::inc(x_527);
x_529 = lean::cnstr_get(x_524, 1);
lean::inc(x_529);
lean::dec(x_524);
x_532 = lean::cnstr_get(x_529, 0);
lean::inc(x_532);
x_534 = lean::cnstr_get(x_529, 1);
lean::inc(x_534);
x_536 = lean::cnstr_get(x_529, 2);
lean::inc(x_536);
x_538 = lean::cnstr_get(x_529, 3);
lean::inc(x_538);
if (lean::obj_tag(x_538) == 0)
{
obj* x_547; obj* x_551; 
lean::dec(x_433);
lean::dec(x_509);
lean::dec(x_536);
lean::dec(x_532);
lean::dec(x_527);
lean::dec(x_347);
lean::dec(x_534);
x_547 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_547);
lean::inc(x_0);
x_551 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_547, x_529, x_3);
if (lean::obj_tag(x_551) == 0)
{
obj* x_555; obj* x_558; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_555 = lean::cnstr_get(x_551, 0);
lean::inc(x_555);
lean::dec(x_551);
if (lean::is_scalar(x_526)) {
 x_558 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_558 = x_526;
 lean::cnstr_set_tag(x_526, 0);
}
lean::cnstr_set(x_558, 0, x_555);
return x_558;
}
else
{
obj* x_560; obj* x_563; 
lean::dec(x_526);
x_560 = lean::cnstr_get(x_551, 0);
lean::inc(x_560);
lean::dec(x_551);
x_563 = lean::cnstr_get(x_560, 1);
lean::inc(x_563);
lean::dec(x_560);
x_1 = x_11;
x_2 = x_563;
goto _start;
}
}
else
{
obj* x_569; obj* x_571; obj* x_572; obj* x_574; obj* x_575; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_585; obj* x_586; obj* x_589; obj* x_591; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; 
lean::dec(x_529);
lean::dec(x_526);
x_569 = lean::cnstr_get(x_538, 0);
lean::inc(x_569);
x_571 = l_lean_parser_term_lambda_has__view;
x_572 = lean::cnstr_get(x_571, 1);
lean::inc(x_572);
x_574 = lean::box(0);
x_575 = lean::cnstr_get(x_509, 3);
lean::inc(x_575);
lean::inc(x_574);
x_578 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_578, 0, x_575);
lean::cnstr_set(x_578, 1, x_574);
x_579 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_578);
x_580 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_580, 0, x_579);
lean::cnstr_set(x_580, 1, x_574);
x_581 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_581, 0, x_580);
x_582 = lean::cnstr_get(x_509, 5);
lean::inc(x_582);
lean::dec(x_509);
x_585 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_586 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_586);
lean::inc(x_585);
x_589 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_589, 0, x_585);
lean::cnstr_set(x_589, 1, x_581);
lean::cnstr_set(x_589, 2, x_586);
lean::cnstr_set(x_589, 3, x_582);
lean::inc(x_572);
x_591 = lean::apply_1(x_572, x_589);
lean::inc(x_586);
lean::inc(x_585);
x_594 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_594, 0, x_585);
lean::cnstr_set(x_594, 1, x_569);
lean::cnstr_set(x_594, 2, x_586);
lean::cnstr_set(x_594, 3, x_527);
x_595 = lean::apply_1(x_572, x_594);
x_596 = l_lean_parser_term_app_has__view;
x_597 = lean::cnstr_get(x_596, 1);
lean::inc(x_597);
x_599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_599, 0, x_591);
lean::cnstr_set(x_599, 1, x_595);
x_600 = lean::apply_1(x_597, x_599);
if (lean::is_scalar(x_347)) {
 x_601 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_601 = x_347;
}
lean::cnstr_set(x_601, 0, x_433);
lean::cnstr_set(x_601, 1, x_600);
x_602 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_602, 0, x_601);
lean::cnstr_set(x_602, 1, x_536);
x_603 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_603, 0, x_532);
lean::cnstr_set(x_603, 1, x_534);
lean::cnstr_set(x_603, 2, x_602);
lean::cnstr_set(x_603, 3, x_538);
x_1 = x_11;
x_2 = x_603;
goto _start;
}
}
}
default:
{
obj* x_608; obj* x_612; 
lean::dec(x_473);
lean::dec(x_433);
lean::dec(x_347);
x_608 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_608);
lean::inc(x_0);
x_612 = l_lean_expander_error___at___private_init_lean_expander_1__pop__stx__arg___spec__1___rarg(x_0, x_608, x_345, x_3);
if (lean::obj_tag(x_612) == 0)
{
obj* x_616; obj* x_618; obj* x_619; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_616 = lean::cnstr_get(x_612, 0);
lean::inc(x_616);
if (lean::is_shared(x_612)) {
 lean::dec(x_612);
 x_618 = lean::box(0);
} else {
 lean::cnstr_release(x_612, 0);
 x_618 = x_612;
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
x_1 = x_11;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
}
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
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
obj* x_1; uint8 x_4; 
x_1 = l_lean_parser_ident__univs;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_4 == 0)
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = l_lean_parser_ident__univs_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::apply_1(x_8, x_0);
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
obj* x_6; obj* x_8; 
lean::dec(x_0);
x_6 = l___private_init_lean_expander_1__pop__stx__arg___closed__1;
lean::inc(x_6);
x_8 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_1, x_6, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_19; obj* x_20; obj* x_23; obj* x_25; obj* x_27; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
lean::inc(x_15);
lean::inc(x_15);
lean::inc(x_1);
x_19 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_15);
lean::cnstr_set(x_19, 3, x_15);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; 
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_19);
x_27 = x_29;
goto lbl_28;
}
else
{
obj* x_30; obj* x_34; 
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
lean::dec(x_25);
lean::inc(x_2);
x_34 = l___private_init_lean_expander_1__pop__stx__arg(x_19, x_2);
if (lean::obj_tag(x_34) == 0)
{
obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_20);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_23);
x_42 = lean::cnstr_get(x_34, 0);
lean::inc(x_42);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 x_44 = x_34;
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_65; obj* x_66; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
lean::dec(x_34);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_53 = x_46;
}
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
if (lean::is_scalar(x_53)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_53;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_49);
x_59 = lean::cnstr_get(x_51, 2);
lean::inc(x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::cnstr_get(x_51, 3);
lean::inc(x_62);
lean::dec(x_51);
x_65 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_65, 0, x_54);
lean::cnstr_set(x_65, 1, x_56);
lean::cnstr_set(x_65, 2, x_61);
lean::cnstr_set(x_65, 3, x_62);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_15);
lean::cnstr_set(x_66, 1, x_65);
x_27 = x_66;
goto lbl_28;
}
}
lbl_28:
{
obj* x_67; obj* x_70; obj* x_73; 
x_67 = lean::cnstr_get(x_27, 1);
lean::inc(x_67);
lean::dec(x_27);
x_70 = lean::cnstr_get(x_23, 1);
lean::inc(x_70);
lean::dec(x_23);
x_73 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_70, x_67, x_2);
if (lean::obj_tag(x_73) == 0)
{
obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_20);
lean::dec(x_11);
x_76 = lean::cnstr_get(x_73, 0);
lean::inc(x_76);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_78 = x_73;
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
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_82 = x_73;
}
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_86);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1), 2, 1);
lean::closure_set(x_90, 0, x_89);
x_91 = lean::cnstr_get(x_20, 4);
lean::inc(x_91);
lean::dec(x_20);
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
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
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
obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = l_lean_expander_mixfix__to__notation__spec___closed__3;
lean::inc(x_12);
x_14 = l_option_map___rarg(x_12, x_5);
x_15 = l_lean_expander_mixfix__to__notation__spec___closed__4;
lean::inc(x_15);
x_17 = l_option_map___rarg(x_15, x_14);
x_18 = l_lean_expander_mixfix__to__notation__spec___closed__5;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_17);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_22);
lean::inc(x_11);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_11);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
case 3:
{
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_30; 
lean::dec(x_2);
x_30 = lean::box(0);
x_3 = x_30;
goto lbl_4;
}
else
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_37; uint8 x_38; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_33 = x_5;
}
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
x_36 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_34);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean::nat_dec_eq(x_36, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_2);
lean::dec(x_31);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_sub(x_36, x_42);
lean::dec(x_42);
lean::dec(x_36);
x_46 = l_lean_parser_number_view_of__nat(x_43);
x_47 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_49);
if (lean::is_scalar(x_33)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_33;
}
lean::cnstr_set(x_53, 0, x_52);
x_3 = x_53;
goto lbl_4;
}
else
{
obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_36);
lean::dec(x_33);
x_56 = l_lean_parser_command_notation__spec_precedence_has__view;
x_57 = lean::cnstr_get(x_56, 1);
lean::inc(x_57);
x_59 = lean::apply_1(x_57, x_31);
x_60 = l_lean_expander_mixfix__to__notation__spec___closed__6;
lean::inc(x_60);
x_62 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_59, x_60, x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_1);
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_66 = x_62;
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
obj* x_68; 
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
lean::dec(x_62);
x_3 = x_68;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
x_74 = lean::box(0);
lean::inc(x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_1);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_74);
x_78 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_78);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_77);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
default:
{
obj* x_84; 
lean::dec(x_0);
lean::dec(x_2);
x_84 = lean::box(0);
x_7 = x_84;
goto lbl_8;
}
}
lbl_4:
{
obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; 
x_85 = lean::box(0);
x_86 = l_lean_expander_mixfix__to__notation__spec___closed__1;
lean::inc(x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
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
lean::cnstr_set(x_92, 1, x_85);
x_93 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_93);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_92);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
lbl_8:
{
obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_7);
x_98 = lean::box(0);
x_99 = l_lean_expander_mixfix__to__notation__spec___closed__3;
lean::inc(x_99);
x_101 = l_option_map___rarg(x_99, x_5);
x_102 = l_lean_expander_mixfix__to__notation__spec___closed__4;
lean::inc(x_102);
x_104 = l_option_map___rarg(x_102, x_101);
x_105 = l_lean_expander_mixfix__to__notation__spec___closed__1;
lean::inc(x_105);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_104);
x_108 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_1);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_98);
x_112 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_112);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_112);
lean::cnstr_set(x_114, 1, x_111);
x_115 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_115, 0, x_114);
return x_115;
}
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("a");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("b");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
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
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("b");
lean::inc(x_0);
x_6 = lean_name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
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
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_2 = l_lean_parser_command_mixfix_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_10 = x_12;
goto lbl_11;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; 
x_15 = lean::cnstr_get(x_6, 0);
lean::inc(x_15);
lean::dec(x_6);
x_18 = lean::box(0);
x_19 = l_lean_expander_mixfix_transform___closed__6;
lean::inc(x_19);
lean::inc(x_19);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_19);
lean::cnstr_set(x_22, 3, x_18);
x_10 = x_22;
goto lbl_11;
}
lbl_11:
{
obj* x_24; 
lean::inc(x_8);
x_24 = l_lean_expander_mixfix__to__notation__spec(x_8, x_10, x_1);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_5);
lean::dec(x_8);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_29 = x_24;
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
obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_33 = x_24;
}
x_34 = l_lean_parser_command_notation_has__view;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_43; obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_8);
lean::dec(x_33);
x_43 = l_lean_parser_term_app_has__view;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_5, 4);
lean::inc(x_46);
lean::dec(x_5);
x_49 = l_lean_expander_mixfix_transform___closed__5;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_49);
x_52 = lean::apply_1(x_44, x_51);
x_53 = l_lean_expander_mixfix_transform___closed__3;
x_54 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_54);
lean::inc(x_53);
x_57 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_53);
lean::cnstr_set(x_57, 2, x_31);
lean::cnstr_set(x_57, 3, x_54);
lean::cnstr_set(x_57, 4, x_52);
x_58 = lean::apply_1(x_35, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
case 4:
{
obj* x_63; obj* x_64; obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_8);
lean::dec(x_33);
x_63 = l_lean_parser_term_app_has__view;
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_5, 4);
lean::inc(x_66);
lean::dec(x_5);
x_69 = l_lean_expander_mixfix_transform___closed__1;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_66);
lean::cnstr_set(x_71, 1, x_69);
x_72 = lean::apply_1(x_64, x_71);
x_73 = l_lean_expander_mixfix_transform___closed__3;
x_74 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_74);
lean::inc(x_73);
x_77 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_77, 0, x_37);
lean::cnstr_set(x_77, 1, x_73);
lean::cnstr_set(x_77, 2, x_31);
lean::cnstr_set(x_77, 3, x_74);
lean::cnstr_set(x_77, 4, x_72);
x_78 = lean::apply_1(x_35, x_77);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
default:
{
obj* x_82; 
lean::dec(x_8);
x_82 = lean::box(0);
x_39 = x_82;
goto lbl_40;
}
}
lbl_40:
{
obj* x_84; obj* x_85; obj* x_87; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_39);
x_84 = l_lean_parser_term_app_has__view;
x_85 = lean::cnstr_get(x_84, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_5, 4);
lean::inc(x_87);
lean::dec(x_5);
x_90 = l_lean_expander_mixfix_transform___closed__1;
lean::inc(x_90);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_87);
lean::cnstr_set(x_92, 1, x_90);
lean::inc(x_85);
x_94 = lean::apply_1(x_85, x_92);
x_95 = l_lean_expander_mixfix_transform___closed__2;
lean::inc(x_95);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_94);
lean::cnstr_set(x_97, 1, x_95);
x_98 = lean::apply_1(x_85, x_97);
x_99 = l_lean_expander_mixfix_transform___closed__3;
x_100 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_100);
lean::inc(x_99);
x_103 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_103, 0, x_37);
lean::cnstr_set(x_103, 1, x_99);
lean::cnstr_set(x_103, 2, x_31);
lean::cnstr_set(x_103, 3, x_100);
lean::cnstr_set(x_103, 4, x_98);
x_104 = lean::apply_1(x_35, x_103);
x_105 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
if (lean::is_scalar(x_33)) {
 x_106 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_106 = x_33;
}
lean::cnstr_set(x_106, 0, x_105);
return x_106;
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
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
x_2 = l_lean_parser_command_reserve__mixfix_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_expander_mixfix__to__notation__spec(x_6, x_8, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_14 = x_11;
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
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
x_19 = l_lean_parser_command_reserve__notation_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = l_lean_expander_reserve__mixfix_transform___closed__1;
x_23 = l_lean_expander_mixfix_transform___closed__3;
lean::inc(x_23);
lean::inc(x_22);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_16);
x_27 = lean::apply_1(x_20, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_18;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_3 = l_lean_expander_mk__simple__binder___closed__2;
x_4 = l_lean_expander_mk__simple__binder___closed__1;
x_5 = l_lean_expander_mk__simple__binder___closed__3;
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_2);
lean::cnstr_set(x_9, 4, x_5);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
case 2:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_17; obj* x_18; 
x_11 = l_lean_expander_mk__simple__binder___closed__4;
x_12 = l_lean_expander_mk__simple__binder___closed__1;
x_13 = l_lean_expander_mk__simple__binder___closed__5;
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_0);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_2);
lean::cnstr_set(x_17, 4, x_13);
x_18 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
case 3:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; 
x_19 = l_lean_expander_mk__simple__binder___closed__6;
x_20 = l_lean_expander_mk__simple__binder___closed__1;
x_21 = l_lean_expander_mk__simple__binder___closed__7;
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
x_25 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_0);
lean::cnstr_set(x_25, 2, x_20);
lean::cnstr_set(x_25, 3, x_2);
lean::cnstr_set(x_25, 4, x_21);
x_26 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
default:
{
obj* x_27; obj* x_28; obj* x_29; obj* x_33; obj* x_34; 
x_27 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_28 = l_lean_expander_mk__simple__binder___closed__1;
x_29 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
x_33 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_33, 0, x_27);
lean::cnstr_set(x_33, 1, x_0);
lean::cnstr_set(x_33, 2, x_28);
lean::cnstr_set(x_33, 3, x_2);
lean::cnstr_set(x_33, 4, x_29);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
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
lean::dec(x_0);
return x_1;
}
else
{
obj* x_5; 
lean::dec(x_0);
x_5 = l_lean_expander_binder__ident__to__ident___main___closed__1;
lean::inc(x_5);
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = l_lean_parser_term_hole_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::apply_1(x_1, x_7);
return x_8;
}
}
obj* l_lean_expander_get__opt__type___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
return x_6;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
}
x_7 = l_lean_expander_binder__ident__to__ident___main(x_2);
x_8 = 0;
x_9 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
lean::inc(x_9);
x_11 = l_lean_expander_mk__simple__binder(x_7, x_8, x_9);
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
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_11 = x_3;
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
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_24 = l_lean_expander_mk__simple__binder(x_23, x_0, x_22);
x_25 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_0, x_1, x_2, x_9);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = l_lean_expander_mk__simple__binder(x_17, x_0, x_16);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
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
lean::inc(x_19);
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_22 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_23 = 0;
x_24 = l_lean_expander_mk__simple__binder(x_22, x_23, x_21);
x_25 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_8);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_13);
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_15);
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
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
lean::inc(x_19);
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_22 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_23 = 1;
x_24 = l_lean_expander_mk__simple__binder(x_22, x_23, x_21);
x_25 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_8);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_13);
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_17 = 1;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_15);
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
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
lean::inc(x_19);
x_21 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_19, x_18);
x_22 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_23 = 2;
x_24 = l_lean_expander_mk__simple__binder(x_22, x_23, x_21);
x_25 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_8);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_13);
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_17 = 2;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_15);
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
}
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = l_lean_expander_get__opt__type___main(x_14);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_17 = 3;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_15);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_6);
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
}
x_9 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_0);
lean::inc(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_lean_expander_get__opt__type___main(x_13);
x_15 = l_lean_expander_binder__ident__to__ident___main(x_4);
x_16 = 3;
x_17 = l_lean_expander_mk__simple__binder(x_15, x_16, x_14);
x_18 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_6);
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
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_11 = x_3;
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
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_24 = l_lean_expander_mk__simple__binder(x_23, x_0, x_22);
x_25 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_0, x_1, x_2, x_9);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = l_lean_expander_mk__simple__binder(x_17, x_0, x_16);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
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
obj* x_0; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_0);
x_4 = 0;
x_5 = lean::box(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
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
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_0);
return x_13;
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
lean::inc(x_12);
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
obj* x_18; 
lean::dec(x_6);
lean::dec(x_1);
x_18 = l_lean_expander_expand__bracketed__binder___main___closed__5;
lean::inc(x_18);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_6, 0);
lean::inc(x_20);
lean::dec(x_6);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_20, 0);
lean::inc(x_26);
x_28 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_20, x_26);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_1);
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
lean::dec(x_30);
x_37 = lean::cnstr_get(x_20, 0);
lean::inc(x_37);
x_39 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_20, x_34, x_37);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_30, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_20, 1);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_30);
x_47 = lean::cnstr_get(x_20, 0);
lean::inc(x_47);
lean::dec(x_20);
x_50 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_41, x_47);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_41);
lean::dec(x_43);
x_54 = l_lean_parser_term_binder__default_has__view;
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_30);
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_58);
x_60 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_57, x_58, x_1);
if (lean::obj_tag(x_60) == 0)
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_20);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_64 = x_60;
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
x_66 = lean::cnstr_get(x_60, 0);
lean::inc(x_66);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_68 = x_60;
}
x_69 = lean::cnstr_get(x_20, 0);
lean::inc(x_69);
lean::dec(x_20);
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
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_1);
x_79 = lean::cnstr_get(x_6, 0);
lean::inc(x_79);
x_81 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_79);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
else
{
obj* x_83; 
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_1);
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
lean::dec(x_83);
x_90 = lean::cnstr_get(x_6, 0);
lean::inc(x_90);
x_92 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_87, x_90);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
else
{
obj* x_94; obj* x_96; 
x_94 = lean::cnstr_get(x_83, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_6, 1);
lean::inc(x_96);
if (lean::obj_tag(x_96) == 0)
{
obj* x_100; obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_83);
x_100 = lean::cnstr_get(x_6, 0);
lean::inc(x_100);
lean::dec(x_6);
x_103 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_94, x_100);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
return x_104;
}
else
{
obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_94);
lean::dec(x_96);
x_107 = l_lean_parser_term_binder__default_has__view;
x_108 = lean::cnstr_get(x_107, 1);
lean::inc(x_108);
x_110 = lean::apply_1(x_108, x_83);
x_111 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_111);
x_113 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_110, x_111, x_1);
if (lean::obj_tag(x_113) == 0)
{
obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_6);
x_115 = lean::cnstr_get(x_113, 0);
lean::inc(x_115);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 x_117 = x_113;
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
obj* x_119; obj* x_121; obj* x_122; obj* x_125; obj* x_126; 
x_119 = lean::cnstr_get(x_113, 0);
lean::inc(x_119);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 x_121 = x_113;
}
x_122 = lean::cnstr_get(x_6, 0);
lean::inc(x_122);
lean::dec(x_6);
x_125 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_119, x_122);
if (lean::is_scalar(x_121)) {
 x_126 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_126 = x_121;
}
lean::cnstr_set(x_126, 0, x_125);
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
obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_1);
x_132 = lean::cnstr_get(x_6, 0);
lean::inc(x_132);
x_134 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_132);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_134);
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
obj* x_140; obj* x_143; obj* x_145; obj* x_146; 
lean::dec(x_1);
x_140 = lean::cnstr_get(x_136, 0);
lean::inc(x_140);
lean::dec(x_136);
x_143 = lean::cnstr_get(x_6, 0);
lean::inc(x_143);
x_145 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_140, x_143);
x_146 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_146, 0, x_145);
return x_146;
}
else
{
obj* x_147; obj* x_149; 
x_147 = lean::cnstr_get(x_136, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_6, 1);
lean::inc(x_149);
if (lean::obj_tag(x_149) == 0)
{
obj* x_153; obj* x_156; obj* x_157; 
lean::dec(x_136);
lean::dec(x_1);
x_153 = lean::cnstr_get(x_6, 0);
lean::inc(x_153);
lean::dec(x_6);
x_156 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_147, x_153);
x_157 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_157, 0, x_156);
return x_157;
}
else
{
obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_166; 
lean::dec(x_149);
lean::dec(x_147);
x_160 = l_lean_parser_term_binder__default_has__view;
x_161 = lean::cnstr_get(x_160, 1);
lean::inc(x_161);
x_163 = lean::apply_1(x_161, x_136);
x_164 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_164);
x_166 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_163, x_164, x_1);
if (lean::obj_tag(x_166) == 0)
{
obj* x_168; obj* x_170; obj* x_171; 
lean::dec(x_6);
x_168 = lean::cnstr_get(x_166, 0);
lean::inc(x_168);
if (lean::is_shared(x_166)) {
 lean::dec(x_166);
 x_170 = lean::box(0);
} else {
 lean::cnstr_release(x_166, 0);
 x_170 = x_166;
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
return x_171;
}
else
{
obj* x_172; obj* x_174; obj* x_175; obj* x_178; obj* x_179; 
x_172 = lean::cnstr_get(x_166, 0);
lean::inc(x_172);
if (lean::is_shared(x_166)) {
 lean::dec(x_166);
 x_174 = lean::box(0);
} else {
 lean::cnstr_release(x_166, 0);
 x_174 = x_166;
}
x_175 = lean::cnstr_get(x_6, 0);
lean::inc(x_175);
lean::dec(x_6);
x_178 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_172, x_175);
if (lean::is_scalar(x_174)) {
 x_179 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_179 = x_174;
}
lean::cnstr_set(x_179, 0, x_178);
return x_179;
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
obj* x_183; obj* x_186; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_183 = lean::cnstr_get(x_6, 0);
lean::inc(x_183);
lean::dec(x_6);
x_186 = lean::cnstr_get(x_183, 0);
lean::inc(x_186);
x_188 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_188, 0, x_186);
x_189 = lean::box(0);
x_190 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_190, 0, x_188);
lean::cnstr_set(x_190, 1, x_189);
x_191 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_183, x_190);
x_192 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_192, 0, x_191);
return x_192;
}
else
{
obj* x_193; obj* x_196; obj* x_198; obj* x_199; 
x_193 = lean::cnstr_get(x_6, 0);
lean::inc(x_193);
lean::dec(x_6);
x_196 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_196);
x_198 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_193, x_196);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_198);
return x_199;
}
}
default:
{
obj* x_202; obj* x_203; obj* x_205; obj* x_206; obj* x_209; 
lean::dec(x_6);
lean::dec(x_0);
x_202 = l_lean_parser_term_anonymous__constructor_has__view;
x_203 = lean::cnstr_get(x_202, 1);
lean::inc(x_203);
x_205 = lean::apply_1(x_203, x_4);
x_206 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_206);
x_209 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_205, x_206, x_1);
if (lean::obj_tag(x_209) == 0)
{
obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_1);
x_211 = lean::cnstr_get(x_209, 0);
lean::inc(x_211);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_213 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 x_213 = x_209;
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
obj* x_215; obj* x_217; obj* x_218; obj* x_220; obj* x_223; 
x_215 = lean::cnstr_get(x_209, 0);
lean::inc(x_215);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_217 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 x_217 = x_209;
}
x_218 = lean::cnstr_get(x_215, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_215, 1);
lean::inc(x_220);
lean::dec(x_215);
x_223 = lean::cnstr_get(x_220, 2);
lean::inc(x_223);
if (lean::obj_tag(x_223) == 0)
{
obj* x_226; uint8 x_228; obj* x_230; obj* x_231; 
lean::dec(x_1);
x_226 = lean::cnstr_get(x_220, 0);
lean::inc(x_226);
x_228 = lean::unbox(x_218);
lean::dec(x_218);
x_230 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_228, x_220, x_226);
if (lean::is_scalar(x_217)) {
 x_231 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_231 = x_217;
}
lean::cnstr_set(x_231, 0, x_230);
return x_231;
}
else
{
obj* x_232; 
x_232 = lean::cnstr_get(x_223, 0);
lean::inc(x_232);
lean::dec(x_223);
if (lean::obj_tag(x_232) == 0)
{
obj* x_236; obj* x_239; uint8 x_241; obj* x_243; obj* x_244; 
lean::dec(x_1);
x_236 = lean::cnstr_get(x_232, 0);
lean::inc(x_236);
lean::dec(x_232);
x_239 = lean::cnstr_get(x_220, 0);
lean::inc(x_239);
x_241 = lean::unbox(x_218);
lean::dec(x_218);
x_243 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_241, x_220, x_236, x_239);
if (lean::is_scalar(x_217)) {
 x_244 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_244 = x_217;
}
lean::cnstr_set(x_244, 0, x_243);
return x_244;
}
else
{
obj* x_245; obj* x_247; 
x_245 = lean::cnstr_get(x_232, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_220, 1);
lean::inc(x_247);
if (lean::obj_tag(x_247) == 0)
{
obj* x_251; uint8 x_254; obj* x_256; obj* x_257; 
lean::dec(x_232);
lean::dec(x_1);
x_251 = lean::cnstr_get(x_220, 0);
lean::inc(x_251);
lean::dec(x_220);
x_254 = lean::unbox(x_218);
lean::dec(x_218);
x_256 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_254, x_245, x_251);
if (lean::is_scalar(x_217)) {
 x_257 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_257 = x_217;
}
lean::cnstr_set(x_257, 0, x_256);
return x_257;
}
else
{
obj* x_260; obj* x_261; obj* x_263; obj* x_264; obj* x_266; 
lean::dec(x_247);
lean::dec(x_245);
x_260 = l_lean_parser_term_binder__default_has__view;
x_261 = lean::cnstr_get(x_260, 1);
lean::inc(x_261);
x_263 = lean::apply_1(x_261, x_232);
x_264 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_264);
x_266 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_263, x_264, x_1);
if (lean::obj_tag(x_266) == 0)
{
obj* x_269; obj* x_272; 
lean::dec(x_218);
lean::dec(x_220);
x_269 = lean::cnstr_get(x_266, 0);
lean::inc(x_269);
lean::dec(x_266);
if (lean::is_scalar(x_217)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_217;
 lean::cnstr_set_tag(x_217, 0);
}
lean::cnstr_set(x_272, 0, x_269);
return x_272;
}
else
{
obj* x_273; obj* x_276; uint8 x_279; obj* x_281; obj* x_282; 
x_273 = lean::cnstr_get(x_266, 0);
lean::inc(x_273);
lean::dec(x_266);
x_276 = lean::cnstr_get(x_220, 0);
lean::inc(x_276);
lean::dec(x_220);
x_279 = lean::unbox(x_218);
lean::dec(x_218);
x_281 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_279, x_273, x_276);
if (lean::is_scalar(x_217)) {
 x_282 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_282 = x_217;
}
lean::cnstr_set(x_282, 0, x_281);
return x_282;
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
obj* x_283; obj* x_286; 
x_283 = lean::cnstr_get(x_0, 0);
lean::inc(x_283);
lean::dec(x_0);
x_286 = lean::cnstr_get(x_283, 1);
lean::inc(x_286);
lean::dec(x_283);
if (lean::obj_tag(x_286) == 0)
{
obj* x_290; 
lean::dec(x_286);
x_290 = l_lean_expander_expand__bracketed__binder___main___closed__3;
lean::inc(x_290);
x_2 = x_290;
goto lbl_3;
}
else
{
obj* x_292; uint8 x_295; obj* x_296; obj* x_297; 
x_292 = lean::cnstr_get(x_286, 0);
lean::inc(x_292);
lean::dec(x_286);
x_295 = 0;
x_296 = lean::box(x_295);
x_297 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_292);
x_2 = x_297;
goto lbl_3;
}
}
case 1:
{
obj* x_298; obj* x_301; uint8 x_304; obj* x_305; obj* x_306; 
x_298 = lean::cnstr_get(x_0, 0);
lean::inc(x_298);
lean::dec(x_0);
x_301 = lean::cnstr_get(x_298, 1);
lean::inc(x_301);
lean::dec(x_298);
x_304 = 1;
x_305 = lean::box(x_304);
x_306 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_306, 0, x_305);
lean::cnstr_set(x_306, 1, x_301);
x_2 = x_306;
goto lbl_3;
}
case 2:
{
obj* x_307; obj* x_310; uint8 x_313; obj* x_314; obj* x_315; 
x_307 = lean::cnstr_get(x_0, 0);
lean::inc(x_307);
lean::dec(x_0);
x_310 = lean::cnstr_get(x_307, 1);
lean::inc(x_310);
lean::dec(x_307);
x_313 = 2;
x_314 = lean::box(x_313);
x_315 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_310);
x_2 = x_315;
goto lbl_3;
}
case 3:
{
obj* x_316; obj* x_319; 
x_316 = lean::cnstr_get(x_0, 0);
lean::inc(x_316);
lean::dec(x_0);
x_319 = lean::cnstr_get(x_316, 1);
lean::inc(x_319);
lean::dec(x_316);
if (lean::obj_tag(x_319) == 0)
{
obj* x_322; obj* x_325; obj* x_327; obj* x_328; obj* x_330; obj* x_331; obj* x_334; obj* x_336; obj* x_337; obj* x_338; uint8 x_339; obj* x_340; obj* x_341; 
x_322 = lean::cnstr_get(x_319, 0);
lean::inc(x_322);
lean::dec(x_319);
x_325 = lean::cnstr_get(x_322, 0);
lean::inc(x_325);
x_327 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_327, 0, x_325);
x_328 = lean::box(0);
lean::inc(x_328);
x_330 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_330, 0, x_327);
lean::cnstr_set(x_330, 1, x_328);
x_331 = lean::cnstr_get(x_322, 2);
lean::inc(x_331);
lean::dec(x_322);
x_334 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_334);
x_336 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_336, 0, x_334);
lean::cnstr_set(x_336, 1, x_331);
x_337 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_337, 0, x_336);
x_338 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_338, 0, x_330);
lean::cnstr_set(x_338, 1, x_337);
lean::cnstr_set(x_338, 2, x_328);
x_339 = 3;
x_340 = lean::box(x_339);
x_341 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_341, 0, x_340);
lean::cnstr_set(x_341, 1, x_338);
x_2 = x_341;
goto lbl_3;
}
else
{
obj* x_342; obj* x_345; obj* x_346; obj* x_348; obj* x_349; obj* x_350; obj* x_352; uint8 x_353; obj* x_354; obj* x_355; 
x_342 = lean::cnstr_get(x_319, 0);
lean::inc(x_342);
lean::dec(x_319);
x_345 = lean::box(0);
x_346 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_346);
x_348 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_348, 0, x_346);
lean::cnstr_set(x_348, 1, x_342);
x_349 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_349, 0, x_348);
x_350 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_350);
x_352 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_352, 0, x_350);
lean::cnstr_set(x_352, 1, x_349);
lean::cnstr_set(x_352, 2, x_345);
x_353 = 3;
x_354 = lean::box(x_353);
x_355 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_355, 0, x_354);
lean::cnstr_set(x_355, 1, x_352);
x_2 = x_355;
goto lbl_3;
}
}
default:
{
obj* x_356; obj* x_359; obj* x_360; obj* x_362; obj* x_363; obj* x_366; 
x_356 = lean::cnstr_get(x_0, 0);
lean::inc(x_356);
lean::dec(x_0);
x_359 = l_lean_parser_term_anonymous__constructor_has__view;
x_360 = lean::cnstr_get(x_359, 1);
lean::inc(x_360);
x_362 = lean::apply_1(x_360, x_356);
x_363 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_363);
x_366 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_362, x_363, x_1);
if (lean::obj_tag(x_366) == 0)
{
obj* x_368; obj* x_370; obj* x_371; 
lean::dec(x_1);
x_368 = lean::cnstr_get(x_366, 0);
lean::inc(x_368);
if (lean::is_shared(x_366)) {
 lean::dec(x_366);
 x_370 = lean::box(0);
} else {
 lean::cnstr_release(x_366, 0);
 x_370 = x_366;
}
if (lean::is_scalar(x_370)) {
 x_371 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_371 = x_370;
}
lean::cnstr_set(x_371, 0, x_368);
return x_371;
}
else
{
obj* x_372; 
x_372 = lean::cnstr_get(x_366, 0);
lean::inc(x_372);
lean::dec(x_366);
x_2 = x_372;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_375; obj* x_377; obj* x_380; 
x_375 = lean::cnstr_get(x_2, 0);
lean::inc(x_375);
x_377 = lean::cnstr_get(x_2, 1);
lean::inc(x_377);
lean::dec(x_2);
x_380 = lean::cnstr_get(x_377, 2);
lean::inc(x_380);
if (lean::obj_tag(x_380) == 0)
{
obj* x_383; uint8 x_385; obj* x_387; obj* x_388; 
lean::dec(x_1);
x_383 = lean::cnstr_get(x_377, 0);
lean::inc(x_383);
x_385 = lean::unbox(x_375);
lean::dec(x_375);
x_387 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_385, x_377, x_383);
x_388 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_388, 0, x_387);
return x_388;
}
else
{
obj* x_389; 
x_389 = lean::cnstr_get(x_380, 0);
lean::inc(x_389);
lean::dec(x_380);
if (lean::obj_tag(x_389) == 0)
{
obj* x_393; obj* x_396; uint8 x_398; obj* x_400; obj* x_401; 
lean::dec(x_1);
x_393 = lean::cnstr_get(x_389, 0);
lean::inc(x_393);
lean::dec(x_389);
x_396 = lean::cnstr_get(x_377, 0);
lean::inc(x_396);
x_398 = lean::unbox(x_375);
lean::dec(x_375);
x_400 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_398, x_377, x_393, x_396);
x_401 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_401, 0, x_400);
return x_401;
}
else
{
obj* x_402; obj* x_404; 
x_402 = lean::cnstr_get(x_389, 0);
lean::inc(x_402);
x_404 = lean::cnstr_get(x_377, 1);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_408; uint8 x_411; obj* x_413; obj* x_414; 
lean::dec(x_1);
lean::dec(x_389);
x_408 = lean::cnstr_get(x_377, 0);
lean::inc(x_408);
lean::dec(x_377);
x_411 = lean::unbox(x_375);
lean::dec(x_375);
x_413 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_411, x_402, x_408);
x_414 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_414, 0, x_413);
return x_414;
}
else
{
obj* x_417; obj* x_418; obj* x_420; obj* x_421; obj* x_423; 
lean::dec(x_404);
lean::dec(x_402);
x_417 = l_lean_parser_term_binder__default_has__view;
x_418 = lean::cnstr_get(x_417, 1);
lean::inc(x_418);
x_420 = lean::apply_1(x_418, x_389);
x_421 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_421);
x_423 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_420, x_421, x_1);
if (lean::obj_tag(x_423) == 0)
{
obj* x_426; obj* x_428; obj* x_429; 
lean::dec(x_375);
lean::dec(x_377);
x_426 = lean::cnstr_get(x_423, 0);
lean::inc(x_426);
if (lean::is_shared(x_423)) {
 lean::dec(x_423);
 x_428 = lean::box(0);
} else {
 lean::cnstr_release(x_423, 0);
 x_428 = x_423;
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
obj* x_430; obj* x_432; obj* x_433; uint8 x_436; obj* x_438; obj* x_439; 
x_430 = lean::cnstr_get(x_423, 0);
lean::inc(x_430);
if (lean::is_shared(x_423)) {
 lean::dec(x_423);
 x_432 = lean::box(0);
} else {
 lean::cnstr_release(x_423, 0);
 x_432 = x_423;
}
x_433 = lean::cnstr_get(x_377, 0);
lean::inc(x_433);
lean::dec(x_377);
x_436 = lean::unbox(x_375);
lean::dec(x_375);
x_438 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_436, x_430, x_433);
if (lean::is_scalar(x_432)) {
 x_439 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_439 = x_432;
}
lean::cnstr_set(x_439, 0, x_438);
return x_439;
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
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_13);
x_15 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_10);
return x_17;
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
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_13);
x_15 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_10);
return x_17;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = l_lean_parser_ident__univs_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::inc(x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_0);
x_17 = lean::apply_1(x_13, x_16);
lean::inc(x_0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_0);
return x_20;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = l_lean_parser_term_hole_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::mk_string("_");
x_16 = l_string_trim(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_1(x_13, x_18);
x_20 = 0;
x_21 = l_lean_expander_mk__simple__binder(x_11, x_20, x_19);
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
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
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
lean::inc(x_19);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_21 = x_14;
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
lean::inc(x_23);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_25 = x_14;
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
obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_3);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_26, 0);
lean::inc(x_33);
lean::dec(x_26);
x_36 = lean::box(0);
x_37 = l_lean_parser_term_match_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_40 = l_lean_parser_term_anonymous__constructor_has__view;
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_33);
lean::inc(x_36);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_36);
lean::inc(x_36);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_36);
x_48 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
lean::cnstr_set(x_50, 2, x_23);
lean::inc(x_36);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_36);
lean::inc(x_36);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_36);
x_55 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_56 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
x_57 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
lean::inc(x_57);
lean::inc(x_36);
lean::inc(x_56);
lean::inc(x_55);
x_62 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_62, 0, x_55);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_36);
lean::cnstr_set(x_62, 3, x_57);
lean::cnstr_set(x_62, 4, x_36);
lean::cnstr_set(x_62, 5, x_54);
x_63 = lean::apply_1(x_38, x_62);
x_64 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
lean::inc(x_64);
x_66 = lean::apply_2(x_0, x_64, x_63);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
default:
{
obj* x_69; 
lean::dec(x_11);
x_69 = lean::box(0);
x_29 = x_69;
goto lbl_30;
}
}
lbl_30:
{
obj* x_71; 
lean::dec(x_29);
x_71 = l_lean_expander_expand__bracketed__binder___main(x_26, x_3);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_77; 
lean::dec(x_0);
lean::dec(x_23);
x_74 = lean::cnstr_get(x_71, 0);
lean::inc(x_74);
lean::dec(x_71);
if (lean::is_scalar(x_25)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_25;
 lean::cnstr_set_tag(x_25, 0);
}
lean::cnstr_set(x_77, 0, x_74);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
x_81 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_23, x_78);
if (lean::is_scalar(x_25)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_25;
}
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
obj* x_85; obj* x_88; uint8 x_89; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_11);
lean::dec(x_3);
x_85 = lean::cnstr_get(x_7, 0);
lean::inc(x_85);
lean::dec(x_7);
x_88 = l_lean_expander_binder__ident__to__ident___main(x_85);
x_89 = 0;
x_90 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_90);
x_92 = l_lean_expander_mk__simple__binder(x_88, x_89, x_90);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = lean::apply_2(x_0, x_93, x_23);
if (lean::is_scalar(x_25)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_25;
}
lean::cnstr_set(x_95, 0, x_94);
return x_95;
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
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
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
lean::inc(x_13);
x_15 = l_lean_expander_mk__simple__binder(x_11, x_12, x_13);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, x_16, x_10);
return x_17;
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
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_18 = x_7;
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
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_42 = x_7;
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
lean::inc(x_66);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_68 = x_60;
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
lean::inc(x_70);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_72 = x_60;
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
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_81 = x_7;
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
lean::inc(x_99);
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
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
lean::inc(x_1);
x_11 = l_lean_expander_expand__bracketed__binder___main(x_5, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_17 = x_11;
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
}
x_22 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_7, x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_28; 
lean::dec(x_9);
lean::dec(x_19);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
lean::dec(x_22);
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_9)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_9;
}
lean::cnstr_set(x_32, 0, x_19);
lean::cnstr_set(x_32, 1, x_29);
if (lean::is_scalar(x_21)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_21;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
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
lean::inc(x_6);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
}
x_9 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_13 = x_9;
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
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_17 = x_9;
}
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
x_20 = l_list_join___main___rarg(x_15);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::apply_1(x_18, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
else
{
obj* x_27; 
lean::dec(x_5);
lean::dec(x_1);
x_27 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_27);
return x_27;
}
}
}
obj* l_lean_expander_lambda_transform___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_6 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_6);
lean::inc(x_5);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_1);
x_10 = lean::apply_1(x_3, x_9);
return x_10;
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
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_13; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 3);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_expander_lambda_transform___closed__1;
lean::inc(x_11);
x_13 = l_lean_expander_expand__binders(x_11, x_6, x_8, x_1);
return x_13;
}
}
obj* l_lean_expander_pi_transform___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_3 = l_lean_parser_term_pi_has__view;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_11, 3, x_2);
x_12 = lean::apply_1(x_4, x_11);
return x_12;
}
}
obj* l_lean_expander_pi_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_2 = l_lean_parser_term_pi_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform___lambda__1), 3, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 3);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_lean_expander_expand__binders(x_7, x_8, x_10, x_1);
return x_13;
}
}
obj* _init_l_lean_expander_arrow_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_3 = l_lean_parser_term_arrow_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_term_pi_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_13 = l_lean_expander_arrow_transform___closed__1;
x_14 = l_lean_expander_mk__simple__binder___closed__1;
x_15 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
x_20 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_14);
lean::cnstr_set(x_20, 3, x_10);
lean::cnstr_set(x_20, 4, x_15);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::cnstr_get(x_6, 2);
lean::inc(x_23);
lean::dec(x_6);
x_26 = l_lean_expander_arrow_transform___closed__2;
x_27 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_27);
lean::inc(x_26);
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_27);
lean::cnstr_set(x_30, 3, x_23);
x_31 = lean::apply_1(x_8, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_7);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
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
lean::inc(x_13);
x_15 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_13, x_12);
return x_15;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_paren_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
x_10 = l_lean_expander_paren_transform___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
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
obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
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
lean::inc(x_40);
x_42 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_40, x_39);
if (lean::is_scalar(x_14)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_14;
}
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
obj* _init_l_lean_expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* l_lean_expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_1);
x_3 = l_lean_parser_term_assume_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = l_lean_parser_term_lambda_has__view;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 3);
lean::inc(x_12);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_22 = l_lean_expander_assume_transform___closed__1;
x_23 = l_lean_expander_mk__simple__binder___closed__1;
x_24 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
x_29 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_22);
lean::cnstr_set(x_29, 2, x_23);
lean::cnstr_set(x_29, 3, x_18);
lean::cnstr_set(x_29, 4, x_24);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_33 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_33);
lean::inc(x_32);
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_31);
lean::cnstr_set(x_36, 2, x_33);
lean::cnstr_set(x_36, 3, x_12);
x_37 = lean::apply_1(x_10, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_7, 0);
lean::inc(x_40);
lean::dec(x_7);
x_43 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_44 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_44);
lean::inc(x_43);
x_47 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_44);
lean::cnstr_set(x_47, 3, x_12);
x_48 = lean::apply_1(x_10, x_47);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_if_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
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
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_62; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_27 = x_7;
}
x_28 = lean::cnstr_get(x_6, 2);
lean::inc(x_28);
x_30 = l_lean_parser_term_lambda_has__view;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_37 = l_lean_expander_mk__simple__binder___closed__1;
x_38 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_38);
lean::inc(x_28);
lean::inc(x_37);
lean::inc(x_33);
lean::inc(x_36);
x_44 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_44, 0, x_36);
lean::cnstr_set(x_44, 1, x_33);
lean::cnstr_set(x_44, 2, x_37);
lean::cnstr_set(x_44, 3, x_28);
lean::cnstr_set(x_44, 4, x_38);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::cnstr_get(x_6, 4);
lean::inc(x_47);
x_49 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_50 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_50);
lean::inc(x_49);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_46);
lean::cnstr_set(x_53, 2, x_50);
lean::cnstr_set(x_53, 3, x_47);
lean::inc(x_31);
x_55 = lean::apply_1(x_31, x_53);
x_56 = lean::box(0);
lean::inc(x_56);
lean::inc(x_28);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_28);
lean::cnstr_set(x_59, 1, x_56);
x_60 = l_lean_expander_if_transform___closed__2;
lean::inc(x_60);
x_62 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_60, x_59);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
x_66 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_66, 0, x_36);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_37);
lean::cnstr_set(x_66, 3, x_62);
lean::cnstr_set(x_66, 4, x_38);
x_67 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::cnstr_get(x_6, 6);
lean::inc(x_69);
lean::dec(x_6);
lean::inc(x_50);
lean::inc(x_49);
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_49);
lean::cnstr_set(x_74, 1, x_68);
lean::cnstr_set(x_74, 2, x_50);
lean::cnstr_set(x_74, 3, x_69);
x_75 = lean::apply_1(x_31, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_56);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_55);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_28);
lean::cnstr_set(x_78, 1, x_77);
x_79 = l_lean_expander_if_transform___closed__3;
lean::inc(x_79);
x_81 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_79, x_78);
if (lean::is_scalar(x_27)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_27;
}
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_lean_parser_term_hole_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::mk_string("_");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_7, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
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
lean::inc(x_9);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_11 = x_7;
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
}
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
x_23 = l_lean_expander_let_transform___closed__1;
lean::inc(x_23);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_14);
lean::cnstr_set(x_25, 2, x_23);
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
lean::cnstr_set(x_36, 0, x_21);
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
lean::inc(x_45);
return x_45;
}
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_85; obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_47 = lean::box(0);
x_48 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_14);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::inc(x_47);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_47);
lean::cnstr_set(x_52, 1, x_50);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::cnstr_get(x_3, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_6, 0);
lean::inc(x_56);
x_58 = l_lean_parser_term_pi_has__view;
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
x_61 = l_lean_expander_get__opt__type___main(x_16);
x_62 = l_lean_expander_arrow_transform___closed__2;
x_63 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_63);
lean::inc(x_53);
lean::inc(x_62);
x_67 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set(x_67, 1, x_53);
lean::cnstr_set(x_67, 2, x_63);
lean::cnstr_set(x_67, 3, x_61);
x_68 = lean::apply_1(x_59, x_67);
x_69 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_68);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
if (lean::is_scalar(x_18)) {
 x_73 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_73 = x_18;
}
lean::cnstr_set(x_73, 0, x_12);
lean::cnstr_set(x_73, 1, x_47);
lean::cnstr_set(x_73, 2, x_72);
if (lean::is_scalar(x_11)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_11;
}
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::cnstr_get(x_6, 2);
lean::inc(x_75);
x_77 = l_lean_parser_term_lambda_has__view;
x_78 = lean::cnstr_get(x_77, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_6, 3);
lean::inc(x_80);
x_82 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
lean::inc(x_63);
lean::inc(x_82);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_82);
lean::cnstr_set(x_85, 1, x_53);
lean::cnstr_set(x_85, 2, x_63);
lean::cnstr_set(x_85, 3, x_80);
x_86 = lean::apply_1(x_78, x_85);
x_87 = lean::cnstr_get(x_6, 4);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_6, 5);
lean::inc(x_89);
lean::dec(x_6);
x_92 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_92, 0, x_56);
lean::cnstr_set(x_92, 1, x_74);
lean::cnstr_set(x_92, 2, x_75);
lean::cnstr_set(x_92, 3, x_86);
lean::cnstr_set(x_92, 4, x_87);
lean::cnstr_set(x_92, 5, x_89);
x_93 = lean::apply_1(x_54, x_92);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
else
{
obj* x_96; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_113; obj* x_116; obj* x_118; obj* x_120; obj* x_122; obj* x_123; obj* x_124; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_96 = lean::cnstr_get(x_7, 0);
lean::inc(x_96);
lean::dec(x_7);
x_99 = l_lean_parser_term_match_has__view;
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
x_102 = lean::box(0);
x_103 = lean::cnstr_get(x_6, 3);
lean::inc(x_103);
lean::inc(x_102);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_102);
lean::inc(x_102);
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_102);
lean::inc(x_102);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_96);
lean::cnstr_set(x_110, 1, x_102);
lean::inc(x_102);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_102);
x_113 = lean::cnstr_get(x_6, 5);
lean::inc(x_113);
lean::dec(x_6);
x_116 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_116);
x_118 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_118, 0, x_112);
lean::cnstr_set(x_118, 1, x_116);
lean::cnstr_set(x_118, 2, x_113);
lean::inc(x_102);
x_120 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_102);
lean::inc(x_102);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_102);
x_123 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_124 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
lean::inc(x_124);
lean::inc(x_102);
lean::inc(x_123);
x_128 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_128, 0, x_123);
lean::cnstr_set(x_128, 1, x_108);
lean::cnstr_set(x_128, 2, x_102);
lean::cnstr_set(x_128, 3, x_124);
lean::cnstr_set(x_128, 4, x_102);
lean::cnstr_set(x_128, 5, x_122);
x_129 = lean::apply_1(x_100, x_128);
x_130 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_130, 0, x_129);
x_131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
return x_131;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_13 = x_7;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
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
x_25 = lean::cnstr_get(x_6, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_6, 1);
lean::inc(x_27);
lean::dec(x_6);
x_30 = l_lean_parser_term_pi_has__view;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_11, 1);
lean::inc(x_33);
lean::dec(x_11);
x_36 = l_lean_expander_arrow_transform___closed__2;
x_37 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_37);
lean::inc(x_36);
x_40 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_22);
lean::cnstr_set(x_40, 2, x_37);
lean::cnstr_set(x_40, 3, x_33);
x_41 = lean::apply_1(x_31, x_40);
x_42 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_41);
x_45 = l_lean_expander_constant_transform___closed__1;
lean::inc(x_45);
if (lean::is_scalar(x_13)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_13;
}
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_44);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_25);
lean::cnstr_set(x_48, 1, x_27);
lean::cnstr_set(x_48, 2, x_47);
x_49 = lean::apply_1(x_23, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_56; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_56 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_56);
return x_56;
}
}
}
obj* _init_l_lean_expander_declaration_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@[");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::mk_string("]");
x_7 = l_string_trim(x_6);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("class");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
lean::inc(x_0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
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
lean::inc(x_9);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_11 = x_7;
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 3);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_9, 4);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_9, 5);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_9, 6);
lean::inc(x_24);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 lean::cnstr_release(x_9, 3);
 lean::cnstr_release(x_9, 4);
 lean::cnstr_release(x_9, 5);
 lean::cnstr_release(x_9, 6);
 x_26 = x_9;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_36; 
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_26);
x_36 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_36);
return x_36;
}
else
{
obj* x_38; obj* x_39; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_38 = x_12;
}
x_39 = lean::cnstr_get(x_6, 0);
lean::inc(x_39);
lean::dec(x_6);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = lean::box(0);
x_45 = l_lean_expander_declaration_transform___closed__1;
lean::inc(x_45);
x_47 = l_option_get__or__else___main___rarg(x_42, x_45);
x_48 = lean::cnstr_get(x_3, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_39, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = l_lean_expander_declaration_transform___closed__2;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_54);
x_59 = lean::cnstr_get(x_47, 2);
lean::inc(x_59);
lean::dec(x_47);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_52);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_59);
if (lean::is_scalar(x_38)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_38;
}
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::cnstr_get(x_39, 2);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_39, 3);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_39, 4);
lean::inc(x_68);
lean::dec(x_39);
x_71 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_71, 0, x_50);
lean::cnstr_set(x_71, 1, x_63);
lean::cnstr_set(x_71, 2, x_64);
lean::cnstr_set(x_71, 3, x_66);
lean::cnstr_set(x_71, 4, x_68);
if (lean::is_scalar(x_26)) {
 x_72 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_72 = x_26;
}
lean::cnstr_set(x_72, 0, x_44);
lean::cnstr_set(x_72, 1, x_14);
lean::cnstr_set(x_72, 2, x_16);
lean::cnstr_set(x_72, 3, x_18);
lean::cnstr_set(x_72, 4, x_20);
lean::cnstr_set(x_72, 5, x_22);
lean::cnstr_set(x_72, 6, x_24);
if (lean::is_scalar(x_11)) {
 x_73 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_73 = x_11;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::apply_1(x_48, x_74);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
}
case 5:
{
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_97; 
x_78 = lean::cnstr_get(x_7, 0);
lean::inc(x_78);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_80 = x_7;
}
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_78, 2);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_78, 3);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_78, 4);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_78, 5);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_78, 6);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_78, 7);
lean::inc(x_95);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 lean::cnstr_release(x_78, 2);
 lean::cnstr_release(x_78, 3);
 lean::cnstr_release(x_78, 4);
 lean::cnstr_release(x_78, 5);
 lean::cnstr_release(x_78, 6);
 lean::cnstr_release(x_78, 7);
 x_97 = x_78;
}
if (lean::obj_tag(x_81) == 0)
{
obj* x_109; 
lean::dec(x_6);
lean::dec(x_83);
lean::dec(x_81);
lean::dec(x_80);
lean::dec(x_87);
lean::dec(x_89);
lean::dec(x_95);
lean::dec(x_97);
lean::dec(x_85);
lean::dec(x_91);
lean::dec(x_93);
x_109 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_109);
return x_109;
}
else
{
obj* x_112; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_130; obj* x_131; obj* x_134; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_81);
x_112 = lean::cnstr_get(x_6, 0);
lean::inc(x_112);
lean::dec(x_6);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
x_117 = l_lean_expander_declaration_transform___closed__1;
lean::inc(x_117);
x_119 = l_option_get__or__else___main___rarg(x_115, x_117);
x_120 = lean::cnstr_get(x_3, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_112, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_119, 1);
lean::inc(x_126);
x_128 = l_lean_expander_declaration_transform___closed__2;
lean::inc(x_128);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_126);
x_131 = lean::cnstr_get(x_119, 2);
lean::inc(x_131);
lean::dec(x_119);
x_134 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_134, 0, x_124);
lean::cnstr_set(x_134, 1, x_130);
lean::cnstr_set(x_134, 2, x_131);
x_135 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_135, 0, x_134);
x_136 = lean::cnstr_get(x_112, 2);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_112, 3);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_112, 4);
lean::inc(x_140);
lean::dec(x_112);
x_143 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_143, 0, x_122);
lean::cnstr_set(x_143, 1, x_135);
lean::cnstr_set(x_143, 2, x_136);
lean::cnstr_set(x_143, 3, x_138);
lean::cnstr_set(x_143, 4, x_140);
x_144 = l_lean_expander_declaration_transform___closed__3;
lean::inc(x_144);
if (lean::is_scalar(x_97)) {
 x_146 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_146 = x_97;
}
lean::cnstr_set(x_146, 0, x_144);
lean::cnstr_set(x_146, 1, x_83);
lean::cnstr_set(x_146, 2, x_85);
lean::cnstr_set(x_146, 3, x_87);
lean::cnstr_set(x_146, 4, x_89);
lean::cnstr_set(x_146, 5, x_91);
lean::cnstr_set(x_146, 6, x_93);
lean::cnstr_set(x_146, 7, x_95);
if (lean::is_scalar(x_80)) {
 x_147 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_147 = x_80;
}
lean::cnstr_set(x_147, 0, x_146);
x_148 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_148, 0, x_143);
lean::cnstr_set(x_148, 1, x_147);
x_149 = lean::apply_1(x_120, x_148);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
}
default:
{
obj* x_154; 
lean::dec(x_7);
lean::dec(x_6);
x_154 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_154);
return x_154;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_13 = x_7;
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
lean::inc(x_20);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_24 = x_11;
}
x_25 = lean::box(0);
x_26 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_14);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::cnstr_get(x_3, 1);
lean::inc(x_31);
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
x_43 = lean::cnstr_get(x_22, 1);
lean::inc(x_43);
lean::dec(x_22);
x_46 = l_lean_expander_arrow_transform___closed__2;
x_47 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_47);
lean::inc(x_46);
x_50 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_30);
lean::cnstr_set(x_50, 2, x_47);
lean::cnstr_set(x_50, 3, x_43);
x_51 = lean::apply_1(x_41, x_50);
x_52 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_51);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = l_lean_expander_constant_transform___closed__1;
lean::inc(x_56);
if (lean::is_scalar(x_13)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_13;
}
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_55);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_33);
lean::cnstr_set(x_59, 1, x_35);
lean::cnstr_set(x_59, 2, x_37);
lean::cnstr_set(x_59, 3, x_58);
x_60 = lean::apply_1(x_31, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
return x_62;
}
}
else
{
obj* x_67; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_67 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_67);
return x_67;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_variable_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_command_variables_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_13 = lean::box(0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_13);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_18);
x_22 = lean::apply_1(x_8, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_25 = lean::cnstr_get(x_10, 0);
lean::inc(x_25);
lean::dec(x_10);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_30 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_30);
lean::inc(x_29);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set(x_33, 1, x_28);
lean::cnstr_set(x_33, 2, x_30);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_13);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_36);
x_40 = lean::apply_1(x_8, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
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
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_1);
x_3 = l_option_map___rarg(x_1, x_0);
x_4 = lean::box(3);
x_5 = l_option_get__or__else___main___rarg(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_expander_binding__annotation__update;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_10;
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
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_20; 
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
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
x_20 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
return x_20;
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
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_expander_binding__annotation__update;
x_6 = l_lean_expander_binding__annotation__update_parser___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_9;
}
}
obj* _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_lean_expander_binding__annotation__update_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::mk_string("dummy");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_7, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
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
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_12, 2);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_20 = x_12;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_26; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_20);
lean::inc(x_1);
x_26 = l_lean_expander_expand__bracketed__binder___main(x_5, x_1);
x_10 = x_26;
goto lbl_11;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; 
x_27 = lean::cnstr_get(x_16, 0);
lean::inc(x_27);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_29 = x_16;
}
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_27, 2);
lean::inc(x_34);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 lean::cnstr_release(x_27, 2);
 x_36 = x_27;
}
if (lean::obj_tag(x_32) == 0)
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_5);
x_38 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
lean::inc(x_38);
if (lean::is_scalar(x_36)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_36;
}
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_38);
lean::cnstr_set(x_40, 2, x_34);
if (lean::is_scalar(x_29)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_29;
}
lean::cnstr_set(x_41, 0, x_40);
if (lean::is_scalar(x_20)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_20;
}
lean::cnstr_set(x_42, 0, x_14);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set(x_42, 2, x_18);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::inc(x_1);
x_45 = l_lean_expander_expand__bracketed__binder___main(x_43, x_1);
x_10 = x_45;
goto lbl_11;
}
else
{
obj* x_54; 
lean::dec(x_14);
lean::dec(x_30);
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_29);
lean::dec(x_18);
lean::dec(x_20);
lean::inc(x_1);
x_54 = l_lean_expander_expand__bracketed__binder___main(x_5, x_1);
x_10 = x_54;
goto lbl_11;
}
}
else
{
obj* x_64; 
lean::dec(x_14);
lean::dec(x_30);
lean::dec(x_32);
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_29);
lean::dec(x_18);
lean::dec(x_20);
lean::inc(x_1);
x_64 = l_lean_expander_expand__bracketed__binder___main(x_5, x_1);
x_10 = x_64;
goto lbl_11;
}
}
}
default:
{
obj* x_66; 
lean::inc(x_1);
x_66 = l_lean_expander_expand__bracketed__binder___main(x_5, x_1);
x_10 = x_66;
goto lbl_11;
}
}
lbl_11:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_1);
x_70 = lean::cnstr_get(x_10, 0);
lean::inc(x_70);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_72 = x_10;
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
obj* x_74; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_10, 0);
lean::inc(x_74);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_76 = x_10;
}
x_77 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_7, x_1);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_83; 
lean::dec(x_9);
lean::dec(x_74);
x_80 = lean::cnstr_get(x_77, 0);
lean::inc(x_80);
lean::dec(x_77);
if (lean::is_scalar(x_76)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_76;
 lean::cnstr_set_tag(x_76, 0);
}
lean::cnstr_set(x_83, 0, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_88; 
x_84 = lean::cnstr_get(x_77, 0);
lean::inc(x_84);
lean::dec(x_77);
if (lean::is_scalar(x_9)) {
 x_87 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_87 = x_9;
}
lean::cnstr_set(x_87, 0, x_74);
lean::cnstr_set(x_87, 1, x_84);
if (lean::is_scalar(x_76)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_76;
}
lean::cnstr_set(x_88, 0, x_87);
return x_88;
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
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
}
x_12 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_9, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_11);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_16 = x_12;
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
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = l_list_join___main___rarg(x_18);
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_24);
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
lean::inc(x_33);
return x_33;
}
}
}
obj* l_lean_expander_level_leading_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; 
lean::dec(x_1);
x_3 = l_lean_parser_level_leading_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
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
lean::inc(x_16);
return x_16;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_3 = l_lean_parser_term_subtype_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_term_lambda_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 2);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = 0;
x_16 = l_lean_expander_mk__simple__binder(x_10, x_15, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::cnstr_get(x_6, 4);
lean::inc(x_18);
lean::dec(x_6);
x_21 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_22 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_22);
lean::inc(x_21);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_17);
lean::cnstr_set(x_25, 2, x_22);
lean::cnstr_set(x_25, 3, x_18);
x_26 = lean::apply_1(x_8, x_25);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_lean_expander_subtype_transform___closed__1;
lean::inc(x_29);
x_31 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
}
x_7 = l_lean_parser_command_universe_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_3 = l_lean_parser_command_universes_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_7);
x_11 = l_lean_parser_no__kind;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = lean::box(0);
x_1 = lean::mk_string("sorry_ax");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = l_lean_expander_glob__id(x_3);
x_5 = l_lean_parser_term_hole_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::mk_string("_");
x_9 = l_string_trim(x_8);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_6, x_12);
x_14 = lean::mk_string("bool");
lean::inc(x_0);
x_16 = lean_name_mk_string(x_0, x_14);
x_17 = lean::mk_string("ff");
x_18 = lean_name_mk_string(x_16, x_17);
x_19 = l_lean_expander_glob__id(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_4, x_21);
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
lean::inc(x_4);
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_0 = l_lean_parser_command_mixfix;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix_transform), 2, 0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_lean_parser_command_reserve__mixfix;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_reserve__mixfix_transform), 2, 0);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_lean_parser_term_bracketed__binders;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_bracketed__binders_transform), 2, 0);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_term_lambda;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform), 2, 0);
lean::inc(x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_lean_parser_term_pi;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform), 2, 0);
lean::inc(x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_lean_parser_term_arrow;
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_arrow_transform), 2, 0);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
x_24 = l_lean_parser_term_paren;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_paren_transform), 2, 0);
lean::inc(x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_lean_parser_term_assume;
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_assume_transform), 2, 0);
lean::inc(x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
x_32 = l_lean_parser_term_if;
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_if_transform), 2, 0);
lean::inc(x_32);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_lean_parser_term_let;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_let_transform), 2, 0);
lean::inc(x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
x_40 = l_lean_parser_command_constant;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_constant_transform), 2, 0);
lean::inc(x_40);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_lean_parser_command_declaration;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_declaration_transform), 2, 0);
lean::inc(x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
x_48 = l_lean_parser_command_intro__rule;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_intro__rule_transform), 2, 0);
lean::inc(x_48);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
x_52 = l_lean_parser_command_variable;
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variable_transform), 2, 0);
lean::inc(x_52);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
x_56 = l_lean_parser_command_variables;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variables_transform), 2, 0);
lean::inc(x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
x_60 = l_lean_parser_level_leading;
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_level_leading_transform), 2, 0);
lean::inc(x_60);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_lean_parser_term_subtype;
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_subtype_transform), 2, 0);
lean::inc(x_64);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_65);
x_68 = l_lean_parser_command_universes;
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_universes_transform), 2, 0);
lean::inc(x_68);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_69);
x_72 = l_lean_parser_term_sorry;
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_sorry_transform), 2, 0);
lean::inc(x_72);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
x_76 = lean::box(0);
lean::inc(x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_67);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_63);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_59);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_55);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_51);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_47);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_43);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_39);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_35);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_31);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_27);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_23);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_19);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_15);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_11);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_7);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_3);
lean::cnstr_set(x_96, 1, x_95);
x_97 = l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(x_76, x_96);
return x_97;
}
}
obj* _init_l_lean_expander_builtin__transformers() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
lean::inc(x_0);
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
lean::inc(x_0);
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_0, x_3);
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
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
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_19);
lean::cnstr_set(x_21, 4, x_1);
lean::cnstr_set_scalar(x_21, sizeof(void*)*5, x_18);
x_22 = x_21;
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
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
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
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
lean::inc(x_21);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_23 = x_16;
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
lean::inc(x_25);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_27 = x_16;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_13 = x_1;
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
lean::inc(x_21);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_23 = x_16;
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
lean::inc(x_25);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_27 = x_16;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_32 = x_25;
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
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::inc(x_1);
x_8 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_3);
lean::dec(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_2);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_21; obj* x_23; obj* x_26; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_0, x_17);
lean::dec(x_17);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
lean::inc(x_23);
x_26 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_21, x_23);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_14, 1);
lean::inc(x_27);
lean::dec(x_14);
x_30 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__3(x_18, x_27, x_2, x_3);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_23);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 x_34 = x_30;
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
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_36 = lean::cnstr_get(x_30, 0);
lean::inc(x_36);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 x_38 = x_30;
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 1);
lean::inc(x_41);
if (lean::is_shared(x_36)) {
 lean::dec(x_36);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_43 = x_36;
}
x_44 = l_lean_parser_syntax_mk__node(x_23, x_39);
if (lean::is_scalar(x_43)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_43;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_41);
if (lean::is_scalar(x_38)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_38;
}
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
else
{
obj* x_47; obj* x_51; 
x_47 = lean::cnstr_get(x_26, 0);
lean::inc(x_47);
lean::dec(x_26);
lean::inc(x_3);
x_51 = l_lean_expander_mk__scope(x_2, x_3);
if (lean::obj_tag(x_51) == 0)
{
obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_47);
lean::dec(x_18);
lean::dec(x_23);
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_59 = x_51;
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
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_74; obj* x_76; obj* x_77; obj* x_79; 
x_61 = lean::cnstr_get(x_51, 0);
lean::inc(x_61);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_63 = x_51;
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_68 = x_61;
}
x_69 = lean::cnstr_get(x_14, 1);
lean::inc(x_69);
lean::dec(x_14);
lean::inc(x_69);
lean::inc(x_64);
x_74 = l_list_map___main___at___private_init_lean_expander_2__expand__core___main___spec__4(x_64, x_69);
lean::inc(x_23);
x_76 = l_lean_parser_syntax_mk__node(x_23, x_74);
x_77 = lean::cnstr_get(x_3, 0);
lean::inc(x_77);
x_79 = lean::apply_2(x_47, x_76, x_77);
if (lean::obj_tag(x_79) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_3);
lean::dec(x_66);
lean::dec(x_64);
lean::dec(x_68);
lean::dec(x_69);
lean::dec(x_18);
lean::dec(x_23);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
if (lean::is_scalar(x_63)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_90, 0, x_87);
return x_90;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_79, 0);
lean::inc(x_91);
lean::dec(x_79);
if (lean::obj_tag(x_91) == 0)
{
obj* x_95; 
lean::dec(x_64);
x_95 = l_list_mmap___main___at___private_init_lean_expander_2__expand__core___main___spec__5(x_18, x_69, x_66, x_3);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_101; 
lean::dec(x_68);
lean::dec(x_23);
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
lean::dec(x_95);
if (lean::is_scalar(x_63)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_102; obj* x_105; obj* x_107; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_95, 0);
lean::inc(x_102);
lean::dec(x_95);
x_105 = lean::cnstr_get(x_102, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_102, 1);
lean::inc(x_107);
lean::dec(x_102);
x_110 = l_lean_parser_syntax_mk__node(x_23, x_105);
if (lean::is_scalar(x_68)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_68;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_107);
if (lean::is_scalar(x_63)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_63;
}
lean::cnstr_set(x_112, 0, x_111);
return x_112;
}
}
else
{
obj* x_117; obj* x_120; obj* x_121; obj* x_122; 
lean::dec(x_63);
lean::dec(x_68);
lean::dec(x_69);
lean::dec(x_23);
x_117 = lean::cnstr_get(x_91, 0);
lean::inc(x_117);
lean::dec(x_91);
x_120 = lean::box(0);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_64);
lean::cnstr_set(x_121, 1, x_120);
x_122 = l_lean_parser_syntax_flip__scopes___main(x_121, x_117);
x_0 = x_18;
x_1 = x_122;
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
obj* x_125; obj* x_127; 
lean::dec(x_0);
x_125 = l___private_init_lean_expander_2__expand__core___main___closed__1;
lean::inc(x_125);
x_127 = l_lean_expander_error___at___private_init_lean_expander_2__expand__core___main___spec__1___rarg(x_1, x_125, x_2, x_3);
return x_127;
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
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::mk_nat_obj(1000u);
x_3 = l_lean_expander_expander__state_new;
lean::inc(x_3);
x_5 = l___private_init_lean_expander_2__expand__core___main(x_2, x_0, x_3, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
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
obj* x_10; obj* x_12; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
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
 l_lean_expander_transform__m_monad__reader = _init_l_lean_expander_transform__m_monad__reader();
 l_lean_expander_transform__m_monad__except = _init_l_lean_expander_transform__m_monad__except();
 l_lean_expander_transform__m = _init_l_lean_expander_transform__m();
 l_lean_expander_transformer = _init_l_lean_expander_transformer();
 l_lean_expander_no__expansion___closed__1 = _init_l_lean_expander_no__expansion___closed__1();
 l_lean_expander_coe__binder__bracketed__binder___closed__1 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__1();
 l_lean_expander_coe__binder__bracketed__binder___closed__2 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__2();
 l___private_init_lean_expander_1__pop__stx__arg___closed__1 = _init_l___private_init_lean_expander_1__pop__stx__arg___closed__1();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3();
 l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1 = _init_l_lean_expander_mixfix__to__notation__spec___lambda__1___closed__1();
 l_lean_expander_mixfix__to__notation__spec___closed__1 = _init_l_lean_expander_mixfix__to__notation__spec___closed__1();
 l_lean_expander_mixfix__to__notation__spec___closed__2 = _init_l_lean_expander_mixfix__to__notation__spec___closed__2();
 l_lean_expander_mixfix__to__notation__spec___closed__3 = _init_l_lean_expander_mixfix__to__notation__spec___closed__3();
 l_lean_expander_mixfix__to__notation__spec___closed__4 = _init_l_lean_expander_mixfix__to__notation__spec___closed__4();
 l_lean_expander_mixfix__to__notation__spec___closed__5 = _init_l_lean_expander_mixfix__to__notation__spec___closed__5();
 l_lean_expander_mixfix__to__notation__spec___closed__6 = _init_l_lean_expander_mixfix__to__notation__spec___closed__6();
 l_lean_expander_mixfix_transform___closed__1 = _init_l_lean_expander_mixfix_transform___closed__1();
 l_lean_expander_mixfix_transform___closed__2 = _init_l_lean_expander_mixfix_transform___closed__2();
 l_lean_expander_mixfix_transform___closed__3 = _init_l_lean_expander_mixfix_transform___closed__3();
 l_lean_expander_mixfix_transform___closed__4 = _init_l_lean_expander_mixfix_transform___closed__4();
 l_lean_expander_mixfix_transform___closed__5 = _init_l_lean_expander_mixfix_transform___closed__5();
 l_lean_expander_mixfix_transform___closed__6 = _init_l_lean_expander_mixfix_transform___closed__6();
 l_lean_expander_reserve__mixfix_transform___closed__1 = _init_l_lean_expander_reserve__mixfix_transform___closed__1();
 l_lean_expander_mk__simple__binder___closed__1 = _init_l_lean_expander_mk__simple__binder___closed__1();
 l_lean_expander_mk__simple__binder___closed__2 = _init_l_lean_expander_mk__simple__binder___closed__2();
 l_lean_expander_mk__simple__binder___closed__3 = _init_l_lean_expander_mk__simple__binder___closed__3();
 l_lean_expander_mk__simple__binder___closed__4 = _init_l_lean_expander_mk__simple__binder___closed__4();
 l_lean_expander_mk__simple__binder___closed__5 = _init_l_lean_expander_mk__simple__binder___closed__5();
 l_lean_expander_mk__simple__binder___closed__6 = _init_l_lean_expander_mk__simple__binder___closed__6();
 l_lean_expander_mk__simple__binder___closed__7 = _init_l_lean_expander_mk__simple__binder___closed__7();
 l_lean_expander_binder__ident__to__ident___main___closed__1 = _init_l_lean_expander_binder__ident__to__ident___main___closed__1();
 l_lean_expander_get__opt__type___main___closed__1 = _init_l_lean_expander_get__opt__type___main___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1();
 l_lean_expander_expand__bracketed__binder___main___closed__1 = _init_l_lean_expander_expand__bracketed__binder___main___closed__1();
 l_lean_expander_expand__bracketed__binder___main___closed__2 = _init_l_lean_expander_expand__bracketed__binder___main___closed__2();
 l_lean_expander_expand__bracketed__binder___main___closed__3 = _init_l_lean_expander_expand__bracketed__binder___main___closed__3();
 l_lean_expander_expand__bracketed__binder___main___closed__4 = _init_l_lean_expander_expand__bracketed__binder___main___closed__4();
 l_lean_expander_expand__bracketed__binder___main___closed__5 = _init_l_lean_expander_expand__bracketed__binder___main___closed__5();
 l_lean_expander_expand__bracketed__binder___main___closed__6 = _init_l_lean_expander_expand__bracketed__binder___main___closed__6();
 l_lean_expander_expand__bracketed__binder___main___closed__7 = _init_l_lean_expander_expand__bracketed__binder___main___closed__7();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4();
 l_lean_expander_lambda_transform___closed__1 = _init_l_lean_expander_lambda_transform___closed__1();
 l_lean_expander_arrow_transform___closed__1 = _init_l_lean_expander_arrow_transform___closed__1();
 l_lean_expander_arrow_transform___closed__2 = _init_l_lean_expander_arrow_transform___closed__2();
 l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1 = _init_l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1();
 l_lean_expander_paren_transform___closed__1 = _init_l_lean_expander_paren_transform___closed__1();
 l_lean_expander_paren_transform___closed__2 = _init_l_lean_expander_paren_transform___closed__2();
 l_lean_expander_assume_transform___closed__1 = _init_l_lean_expander_assume_transform___closed__1();
 l_lean_expander_if_transform___closed__1 = _init_l_lean_expander_if_transform___closed__1();
 l_lean_expander_if_transform___closed__2 = _init_l_lean_expander_if_transform___closed__2();
 l_lean_expander_if_transform___closed__3 = _init_l_lean_expander_if_transform___closed__3();
 l_lean_expander_let_transform___closed__1 = _init_l_lean_expander_let_transform___closed__1();
 l_lean_expander_constant_transform___closed__1 = _init_l_lean_expander_constant_transform___closed__1();
 l_lean_expander_declaration_transform___closed__1 = _init_l_lean_expander_declaration_transform___closed__1();
 l_lean_expander_declaration_transform___closed__2 = _init_l_lean_expander_declaration_transform___closed__2();
 l_lean_expander_declaration_transform___closed__3 = _init_l_lean_expander_declaration_transform___closed__3();
 l_lean_expander_variable_transform___closed__1 = _init_l_lean_expander_variable_transform___closed__1();
 l_lean_expander_binding__annotation__update = _init_l_lean_expander_binding__annotation__update();
 l_lean_expander_binding__annotation__update_has__view_x_27 = _init_l_lean_expander_binding__annotation__update_has__view_x_27();
 l_lean_expander_binding__annotation__update_has__view = _init_l_lean_expander_binding__annotation__update_has__view();
 l_lean_expander_binding__annotation__update_parser_lean_parser_has__view = _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view();
 l_lean_expander_binding__annotation__update_parser___closed__1 = _init_l_lean_expander_binding__annotation__update_parser___closed__1();
 l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1();
 l_lean_expander_subtype_transform___closed__1 = _init_l_lean_expander_subtype_transform___closed__1();
 l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1();
 l_lean_expander_sorry_transform___closed__1 = _init_l_lean_expander_sorry_transform___closed__1();
 l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1 = _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1();
 l_lean_expander_builtin__transformers = _init_l_lean_expander_builtin__transformers();
 l_lean_expander_expander__m = _init_l_lean_expander_expander__m();
 l_lean_expander_expander__state_new = _init_l_lean_expander_expander__state_new();
 l___private_init_lean_expander_2__expand__core___main___closed__1 = _init_l___private_init_lean_expander_2__expand__core___main___closed__1();
}
